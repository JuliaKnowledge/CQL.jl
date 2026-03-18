# ─── Julia-native DSL macros for CQL ─────────────────────────────────────────
#
# These macros transform Julia-like block syntax into CQL source strings,
# then evaluate them through the existing parser + evaluator pipeline.
# This ensures 100% semantic compatibility with cql"..." while providing
# a more Julian look and feel.

# ─── Helpers ─────────────────────────────────────────────────────────────────

"""
Convert a Julia expression to a CQL term string.

Dot notation `e.f.g` is converted to nested function calls `g(f(e))`,
matching CQL's algebraic term syntax.
"""
function _expr_to_cql_term(ex)
    if ex isa Symbol
        return string(ex)
    elseif ex isa String
        return "\"$ex\""
    elseif ex isa QuoteNode
        return string(ex.value)
    elseif ex isa Integer || ex isa Int
        return "\"$(ex)\""
    elseif ex isa Expr
        if ex.head == :call
            fname = ex.args[1]
            if fname == :(.) && length(ex.args) == 3
                # a.b  →  b(a)  (CQL function application)
                inner = _expr_to_cql_term(ex.args[2])
                outer = ex.args[3] isa QuoteNode ? string(ex.args[3].value) : _expr_to_cql_term(ex.args[3])
                return "$outer($inner)"
            else
                args = join([_expr_to_cql_term(a) for a in ex.args[2:end]], ", ")
                return "$fname($args)"
            end
        elseif ex.head == :(.)
            # a.b  →  b(a)  (CQL function application)
            inner = _expr_to_cql_term(ex.args[1])
            outer = ex.args[2] isa QuoteNode ? string(ex.args[2].value) : _expr_to_cql_term(ex.args[2])
            return "$outer($inner)"
        end
    end
    return string(ex)
end

"""Extract options from keyword arguments in a block."""
function _extract_options(stmts)
    opts = Tuple{String,String}[]
    rest = []
    for s in stmts
        if s isa Expr && s.head == :(=) && s.args[1] == :options
            # options block
            optblock = s.args[2]
            if optblock isa Expr && optblock.head == :block
                for o in optblock.args
                    o isa LineNumberNode && continue
                    if o isa Expr && o.head == :(=)
                        push!(opts, (string(o.args[1]), string(o.args[2])))
                    end
                end
            end
        elseif s isa Expr && s.head == :macrocall && s.args[1] == Symbol("@options")
            for i in 3:length(s.args)
                o = s.args[i]
                if o isa Expr && o.head == :(=)
                    push!(opts, (string(o.args[1]), string(o.args[2])))
                end
            end
        else
            push!(rest, s)
        end
    end
    opts, rest
end

"""Get statements from a block expression, filtering LineNumberNodes."""
function _block_stmts(block)
    if block isa Expr && block.head == :block
        return [s for s in block.args if !(s isa LineNumberNode)]
    end
    return [block]
end

"""Convert a Julia expression to a CQL dot-path string (for path equations)."""
function _expr_to_cql_path(ex)
    if ex isa Symbol
        return string(ex)
    elseif ex isa Expr
        if ex.head == :(.)
            lhs = _expr_to_cql_path(ex.args[1])
            rhs = ex.args[2] isa QuoteNode ? string(ex.args[2].value) : _expr_to_cql_path(ex.args[2])
            return "$lhs.$rhs"
        elseif ex.head == :call && ex.args[1] == :(.)
            lhs = _expr_to_cql_path(ex.args[2])
            rhs = ex.args[3] isa QuoteNode ? string(ex.args[3].value) : _expr_to_cql_path(ex.args[3])
            return "$lhs.$rhs"
        end
    end
    return string(ex)
end

"""Collect `name => expr` pairs from macro args, handling tuples."""
function _collect_pairs!(result::Vector{String}, args)
    for a in args
        a isa LineNumberNode && continue
        if a isa Expr && a.head == :call && a.args[1] == :(=>)
            push!(result, "$(a.args[2]) -> $(_expr_to_cql_term(a.args[3]))")
        elseif a isa Expr && a.head == :tuple
            _collect_pairs!(result, a.args)
        end
    end
end

# ─── @typeside ───────────────────────────────────────────────────────────────

"""
    @typeside begin ... end

Define a CQL typeside using Julia-like syntax.

# Syntax
- `MyType::Ty` — declare a type
- `"constant"::MyType` — declare a constant
- `f(::A, ::B)::C` — declare a function
- `@eq (x::A,) lhs == rhs` — declare an equation
- `@options prover = "completion"` — set options

# Example
```julia
Ty = @typeside begin
    String::Ty
    Int::Ty
    "hello"::String
    succ(::Int)::Int
    @eq (x::Int,) succ(succ(x)) == succ(x)
end
```
"""
macro typeside(block)
    stmts = _block_stmts(block)
    opts, stmts = _extract_options(stmts)

    types = String[]
    constants = Tuple{String,String}[]  # (name, type)
    functions = Tuple{String,Vector{String},String}[]  # (name, argtypes, rettype)
    equations = Tuple{Vector{Tuple{String,String}}, String, String}[]  # (ctx, lhs, rhs)

    for s in stmts
        s isa LineNumberNode && continue

        if s isa Expr && s.head == :(::)
            # X::Ty  or  "const"::Type  or  f(::A)::B
            lhs, rhs = s.args
            if rhs == :Ty || rhs == :Type
                # type declaration
                push!(types, string(lhs))
            elseif lhs isa String || (lhs isa Expr && lhs.head == :string)
                # constant: "value"::Type — preserve quotes for CQL output
                push!(constants, ("\"$(string(lhs))\"", string(rhs)))
            elseif lhs isa Symbol
                # constant: name::Type
                push!(constants, (string(lhs), string(rhs)))
            elseif lhs isa Expr && lhs.head == :call
                # function: f(::A, ::B)::C
                fname = string(lhs.args[1])
                argtypes = String[]
                for arg in lhs.args[2:end]
                    if arg isa Expr && arg.head == :(::)
                        push!(argtypes, string(arg.args[end]))
                    end
                end
                push!(functions, (fname, argtypes, string(rhs)))
            end
        elseif s isa Expr && s.head == :macrocall && s.args[1] == Symbol("@eq")
            # @eq (x::A, y::B) lhs == rhs
            ctx_expr = nothing
            eq_expr = nothing
            for a in s.args[2:end]
                a isa LineNumberNode && continue
                if a isa Expr && a.head == :tuple
                    ctx_expr = a
                elseif a isa Expr && a.head == :call && a.args[1] == :(==)
                    eq_expr = a
                elseif eq_expr === nothing
                    eq_expr = a
                end
            end
            ctx = Tuple{String,String}[]
            if ctx_expr !== nothing
                for c in ctx_expr.args
                    c isa LineNumberNode && continue
                    if c isa Expr && c.head == :(::)
                        push!(ctx, (string(c.args[1]), string(c.args[2])))
                    end
                end
            end
            if eq_expr !== nothing && eq_expr isa Expr && eq_expr.head == :call && eq_expr.args[1] == :(==)
                lhs_str = _expr_to_cql_term(eq_expr.args[2])
                rhs_str = _expr_to_cql_term(eq_expr.args[3])
                push!(equations, (ctx, lhs_str, rhs_str))
            end
        end
    end

    # Generate CQL source
    lines = String["typeside _T = literal {"]
    if !isempty(types)
        push!(lines, "    types")
        push!(lines, "        " * join(types, " "))
    end
    if !isempty(constants)
        push!(lines, "    constants")
        # Group by type
        by_type = Dict{String,Vector{String}}()
        for (name, ty) in constants
            push!(get!(by_type, ty, String[]), name)
        end
        for (ty, names) in by_type
            push!(lines, "        " * join(names, " ") * " : $ty")
        end
    end
    if !isempty(functions)
        push!(lines, "    functions")
        for (fname, argtypes, rettype) in functions
            arg_str = join(argtypes, " ")
            push!(lines, "        $fname : $arg_str -> $rettype")
        end
    end
    if !isempty(equations)
        push!(lines, "    equations")
        for (ctx, lhs, rhs) in equations
            ctx_str = join(["$v:$t" for (v,t) in ctx], " ")
            push!(lines, "        forall $ctx_str . $lhs = $rhs")
        end
    end
    if !isempty(opts)
        push!(lines, "    options")
        for (k, v) in opts
            push!(lines, "        $k = $v")
        end
    end
    push!(lines, "}")
    src = join(lines, "\n")

    return esc(:(run_program($src).typesides["_T"]))
end

# ─── @schema ─────────────────────────────────────────────────────────────────

"""
    @schema typeside_var begin ... end

Define a CQL schema using Julia-like syntax.

# Syntax
- `@entities A, B, C` — declare entities
- `f : A → B` or `f : A --> B` — foreign key
- `a : A ⇒ String` or `a : A ==> String` — attribute
- `@path_eq Entity  lhs == rhs` — path equation
- `@obs_eq (v::Entity,) lhs == rhs` — observation equation

# Example
```julia
S = @schema Ty begin
    @entities Employee, Department
    worksIn : Employee → Department
    name : Employee ⇒ String
    @path_eq Employee  mgr.mgr == mgr
end
```
"""
macro schema(ts_ref, block)
    stmts = _block_stmts(block)
    opts, stmts = _extract_options(stmts)

    entities = String[]
    fks = Tuple{String,String,String}[]  # (name, src, tgt)
    atts = Tuple{String,String,String}[] # (name, src, tgt_type)
    path_eqs = Tuple{String,String,String}[]  # (entity, lhs, rhs)
    obs_eqs = Tuple{Vector{Tuple{String,String}},String,String}[]



    for s in stmts
        s isa LineNumberNode && continue

        if s isa Expr && s.head == :macrocall && s.args[1] == Symbol("@entities")
            for a in s.args[2:end]
                a isa LineNumberNode && continue
                if a isa Symbol
                    push!(entities, string(a))
                elseif a isa Expr && a.head == :tuple
                    for e in a.args
                        e isa Symbol && push!(entities, string(e))
                    end
                end
            end
        elseif s isa Expr && s.head == :call
            # f : A → B  or  f : A ⇒ String
            # In Julia AST: call(→, call(:, f, A), B) or call(-->, ...)
            op = s.args[1]
            if op in (:→, :-->, :⟶)
                # Foreign key
                lhs = s.args[2]  # call(:, name, src) or just name:src
                tgt = string(s.args[3])
                if lhs isa Expr && lhs.head == :call && lhs.args[1] == :(:)
                    name = string(lhs.args[2])
                    src = string(lhs.args[3])
                    push!(fks, (name, src, tgt))
                end
            elseif op == :⇒
                # Attribute
                lhs = s.args[2]
                tgt = string(s.args[3])
                if lhs isa Expr && lhs.head == :call && lhs.args[1] == :(:)
                    name = string(lhs.args[2])
                    src = string(lhs.args[3])
                    push!(atts, (name, src, tgt))
                end
            end
        elseif s isa Expr && s.head == :macrocall && s.args[1] == Symbol("@path_eq")
            # @path_eq Entity  lhs == rhs
            entity = nothing
            eq_expr = nothing
            for a in s.args[2:end]
                a isa LineNumberNode && continue
                if a isa Symbol && entity === nothing
                    entity = string(a)
                elseif a isa Expr && a.head == :call && a.args[1] == :(==)
                    eq_expr = a
                end
            end
            if entity !== nothing && eq_expr !== nothing
                lhs = _expr_to_cql_path(eq_expr.args[2])
                rhs = _expr_to_cql_path(eq_expr.args[3])
                push!(path_eqs, (entity, lhs, rhs))
            end
        elseif s isa Expr && s.head == :macrocall && s.args[1] == Symbol("@obs_eq")
            ctx_expr = nothing
            eq_expr = nothing
            for a in s.args[2:end]
                a isa LineNumberNode && continue
                if a isa Expr && a.head == :tuple
                    ctx_expr = a
                elseif a isa Expr && a.head == :call && a.args[1] == :(==)
                    eq_expr = a
                end
            end
            ctx = Tuple{String,String}[]
            if ctx_expr !== nothing
                for c in ctx_expr.args
                    c isa LineNumberNode && continue
                    if c isa Expr && c.head == :(::)
                        push!(ctx, (string(c.args[1]), string(c.args[2])))
                    end
                end
            end
            if eq_expr !== nothing
                lhs = _expr_to_cql_term(eq_expr.args[2])
                rhs = _expr_to_cql_term(eq_expr.args[3])
                push!(obs_eqs, (ctx, lhs, rhs))
            end
        end
    end

    lines = String[]
    push!(lines, "schema _S = literal : _TS {")
    if !isempty(entities)
        push!(lines, "    entities")
        push!(lines, "        " * join(entities, " "))
    end
    if !isempty(fks)
        push!(lines, "    foreign_keys")
        for (name, src, tgt) in fks
            push!(lines, "        $name : $src -> $tgt")
        end
    end
    if !isempty(atts)
        push!(lines, "    attributes")
        for (name, src, tgt) in atts
            push!(lines, "        $name : $src -> $tgt")
        end
    end
    if !isempty(path_eqs)
        push!(lines, "    path_equations")
        for (en, lhs, rhs) in path_eqs
            push!(lines, "        $en.$lhs = $en.$rhs")
        end
    end
    if !isempty(obs_eqs)
        push!(lines, "    observation_equations")
        for (ctx, lhs, rhs) in obs_eqs
            ctx_str = join(["forall $v:$t" for (v,t) in ctx], " ")
            push!(lines, "        $ctx_str . $lhs = $rhs")
        end
    end
    if !isempty(opts)
        push!(lines, "    options")
        for (k, v) in opts
            push!(lines, "        $k = $v")
        end
    end
    push!(lines, "}")

    schema_src = join(lines, "\n")

    # We need the typeside variable to be in scope. Generate code that
    # builds a mini-program with the typeside injected.
    return esc(quote
        let _ts = $(ts_ref)
            _env = CQL._make_env_with_typeside("_TS", _ts)
            CQL._eval_fragment(_env, $schema_src).schemas["_S"]
        end
    end)
end

# ─── @instance ───────────────────────────────────────────────────────────────

"""
    @instance schema_var begin ... end

Define a CQL instance using Julia-like syntax.

# Syntax
- `g1::Entity` — declare a generator
- `fk(g1) == g2` — foreign key equation
- `att(g1) == "value"` — attribute equation

# Example
```julia
I = @instance S begin
    e1::Employee; e2::Employee; d1::Department
    worksIn(e1) == d1
    worksIn(e2) == d1
    name(e1) == "Alice"
    name(e2) == "Bob"
end
```
"""
macro instance(sch_ref, block)
    stmts = _block_stmts(block)
    opts, stmts = _extract_options(stmts)

    generators = Tuple{String,String}[]  # (name, entity)
    equations = Tuple{String,String}[]   # (lhs, rhs)

    for s in stmts
        s isa LineNumberNode && continue

        if s isa Expr && s.head == :(::)
            # g::Entity
            name = string(s.args[1])
            entity = string(s.args[2])
            push!(generators, (name, entity))
        elseif s isa Expr && s.head == :call && s.args[1] == :(==)
            lhs = _expr_to_cql_term(s.args[2])
            rhs = _expr_to_cql_term(s.args[3])
            push!(equations, (lhs, rhs))
        end
    end

    lines = String["instance _I = literal : _S {"]
    if !isempty(generators)
        push!(lines, "    generators")
        by_entity = Dict{String,Vector{String}}()
        for (name, entity) in generators
            push!(get!(by_entity, entity, String[]), name)
        end
        for (entity, names) in by_entity
            push!(lines, "        " * join(names, " ") * " : $entity")
        end
    end
    if !isempty(equations)
        push!(lines, "    equations")
        for (lhs, rhs) in equations
            push!(lines, "        $lhs = $rhs")
        end
    end
    if !isempty(opts)
        push!(lines, "    options")
        for (k, v) in opts
            push!(lines, "        $k = $v")
        end
    end
    push!(lines, "}")
    inst_src = join(lines, "\n")

    return esc(quote
        let _sch = $(sch_ref)
            _env = CQL._make_env_with_schema("_S", _sch)
            CQL._eval_fragment(_env, $inst_src).instances["_I"]
        end
    end)
end

# ─── @mapping ────────────────────────────────────────────────────────────────

"""
    @mapping src_schema → dst_schema begin ... end

Define a CQL mapping using Julia-like syntax.

# Syntax
- `SrcEntity → DstEntity` — entity mapping
- `src_fk → dst_fk` or `src_fk → dst_path` — FK mapping
- `src_att → dst_att` — attribute mapping

# Example
```julia
F = @mapping S → T begin
    Person → Employee
    name → ename
end
```
"""
macro mapping(arrow_expr, block)
    # Parse src → dst or src --> dst
    src_ref = nothing
    dst_ref = nothing
    if arrow_expr isa Expr && arrow_expr.head == :call
        op = arrow_expr.args[1]
        if op in (:→, :-->, :⟶)
            src_ref = arrow_expr.args[2]
            dst_ref = arrow_expr.args[3]
        end
    end
    src_ref === nothing && error("@mapping expects: @mapping Src → Dst begin ... end")

    stmts = _block_stmts(block)
    opts, stmts = _extract_options(stmts)

    entity_maps = Tuple{String,String}[]
    fk_maps = Tuple{String,String}[]
    att_maps = Tuple{String,String}[]

    for s in stmts
        s isa LineNumberNode && continue
        if s isa Expr && s.head == :call && s.args[1] in (:→, :-->, :⟶)
            lhs = string(s.args[2])
            rhs = _expr_to_cql_term(s.args[3])
            # We can't easily distinguish entity/fk/att here at macro time,
            # so we'll emit them in a combined section and let CQL sort it out
            push!(entity_maps, (lhs, rhs))
        end
    end

    # All mappings are stored as pairs. At runtime, we classify them
    # as entity/fk/att by checking against the source schema.
    pair_strs = [(lhs, rhs) for (lhs, rhs) in entity_maps]
    opt_strs = opts

    return esc(quote
        let _src = $(src_ref), _dst = $(dst_ref)
            _pairs = $pair_strs
            _opts = $opt_strs
            CQL._build_mapping_from_pairs(_src, _dst, _pairs, _opts)
        end
    end)
end

# ─── @query ──────────────────────────────────────────────────────────────────

"""
    @query src_schema → dst_schema begin ... end

Define a CQL query (uber-flower) using Julia-like syntax.

# Syntax
```julia
Q = @query S → T begin
    @entity TargetEntity begin
        @from x::SrcEntity, y::SrcEntity2
        @where f(x) == y
        @return att1 => expr1, att2 => expr2
        @fkeys fk1 => {v1 => expr1, v2 => expr2}
    end
end
```
"""
macro query(arrow_expr, block)
    src_ref = nothing
    dst_ref = nothing
    if arrow_expr isa Expr && arrow_expr.head == :call
        op = arrow_expr.args[1]
        if op in (:→, :-->, :⟶)
            src_ref = arrow_expr.args[2]
            dst_ref = arrow_expr.args[3]
        end
    end
    src_ref === nothing && error("@query expects: @query Src → Dst begin ... end")

    stmts = _block_stmts(block)
    opts, stmts = _extract_options(stmts)

    entity_blocks = String[]

    for s in stmts
        s isa LineNumberNode && continue
        if s isa Expr && s.head == :macrocall && s.args[1] == Symbol("@entity")
            entity_name = nothing
            entity_block = nothing
            for a in s.args[2:end]
                a isa LineNumberNode && continue
                if a isa Symbol && entity_name === nothing
                    entity_name = string(a)
                elseif a isa Expr && a.head == :block
                    entity_block = a
                end
            end
            entity_name === nothing && continue

            from_parts = String[]
            where_parts = String[]
            att_parts = String[]
            fk_parts = String[]

            if entity_block !== nothing
                for es in _block_stmts(entity_block)
                    es isa LineNumberNode && continue
                    if es isa Expr && es.head == :macrocall
                        sub = es.args[1]
                        if sub == Symbol("@from")
                            for a in es.args[2:end]
                                a isa LineNumberNode && continue
                                if a isa Expr && a.head == :(::)
                                    push!(from_parts, "$(a.args[1]):$(a.args[2])")
                                elseif a isa Expr && a.head == :tuple
                                    for t in a.args
                                        if t isa Expr && t.head == :(::)
                                            push!(from_parts, "$(t.args[1]):$(t.args[2])")
                                        end
                                    end
                                end
                            end
                        elseif sub == Symbol("@where")
                            for a in es.args[2:end]
                                a isa LineNumberNode && continue
                                if a isa Expr && a.head == :call && a.args[1] == :(==)
                                    lhs = _expr_to_cql_term(a.args[2])
                                    rhs = _expr_to_cql_term(a.args[3])
                                    push!(where_parts, "$lhs = $rhs")
                                end
                            end
                        elseif sub == Symbol("@return")
                            _collect_pairs!(att_parts, es.args[2:end])
                        elseif sub == Symbol("@fkeys")
                            for a in es.args[2:end]
                                a isa LineNumberNode && continue
                                if a isa Expr && a.head == :call && a.args[1] == :(=>)
                                    fk_name = string(a.args[2])
                                    fk_body = a.args[3]
                                    if fk_body isa Expr && fk_body.head == :braces
                                        binds = String[]
                                        for b in fk_body.args
                                            if b isa Expr && b.head == :call && b.args[1] == :(=>)
                                                push!(binds, "$(b.args[2]) -> $(_expr_to_cql_term(b.args[3]))")
                                            end
                                        end
                                        push!(fk_parts, "$fk_name -> {$(join(binds, " "))}")
                                    end
                                end
                            end
                        end
                    end
                end
            end

            elines = String["    entity $entity_name -> {"]
            if !isempty(from_parts)
                push!(elines, "        from " * join(from_parts, " "))
            end
            if !isempty(where_parts)
                push!(elines, "        where " * join(where_parts, " "))
            end
            if !isempty(att_parts)
                push!(elines, "        attributes " * join(att_parts, " "))
            end
            if !isempty(fk_parts)
                push!(elines, "        foreign_keys " * join(fk_parts, " "))
            end
            push!(elines, "    }")
            push!(entity_blocks, join(elines, "\n"))
        end
    end

    lines = String["query _Q = literal : _SRC -> _DST {"]
    append!(lines, entity_blocks)
    if !isempty(opts)
        push!(lines, "    options")
        for (k, v) in opts
            push!(lines, "        $k = $v")
        end
    end
    push!(lines, "}")
    query_src = join(lines, "\n")

    return esc(quote
        let _src = $(src_ref), _dst = $(dst_ref)
            _env = CQL._make_env_with_schemas("_SRC", _src, "_DST", _dst)
            CQL._eval_fragment(_env, $query_src).queries["_Q"]
        end
    end)
end

# ─── @transform ──────────────────────────────────────────────────────────────

"""
    @transform src_instance → dst_instance begin ... end

Define a CQL transform (instance morphism) using Julia-like syntax.

# Syntax
- `src_gen → dst_term` — generator mapping

# Example
```julia
h = @transform I → J begin
    e1 → e2
    d1 → d1
end
```

Special forms:
- `identity(I)` — identity transform
- `Σ(F, t)` — sigma transform
- `Δ(F, t)` — delta transform
"""
macro transform(arrow_expr, block)
    src_ref = nothing
    dst_ref = nothing
    if arrow_expr isa Expr && arrow_expr.head == :call
        op = arrow_expr.args[1]
        if op in (:→, :-->, :⟶)
            src_ref = arrow_expr.args[2]
            dst_ref = arrow_expr.args[3]
        end
    end
    src_ref === nothing && error("@transform expects: @transform I → J begin ... end")

    stmts = _block_stmts(block)
    opts, stmts = _extract_options(stmts)

    gen_maps = Tuple{String,String}[]

    for s in stmts
        s isa LineNumberNode && continue
        if s isa Expr && s.head == :call && s.args[1] in (:→, :-->, :⟶)
            lhs = string(s.args[2])
            rhs = _expr_to_cql_term(s.args[3])
            push!(gen_maps, (lhs, rhs))
        end
    end

    lines = String["transform _T = literal : _SRC -> _DST {"]
    if !isempty(gen_maps)
        push!(lines, "    generators")
        for (lhs, rhs) in gen_maps
            push!(lines, "        $lhs -> $rhs")
        end
    end
    if !isempty(opts)
        push!(lines, "    options")
        for (k, v) in opts
            push!(lines, "        $k = $v")
        end
    end
    push!(lines, "}")
    src = join(lines, "\n")

    return esc(quote
        let _src_inst = $(src_ref), _dst_inst = $(dst_ref)
            _env = CQL._make_env_with_instances("_SRC", _src_inst, "_DST", _dst_inst)
            CQL._eval_fragment(_env, $src).transforms["_T"]
        end
    end)
end

# ─── @schema_colimit ─────────────────────────────────────────────────────────

"""
    @schema_colimit typeside_var begin ... end

Define a CQL schema colimit using Julia-like syntax.

# Syntax
- `@schemas S1, S2, ...` — schemas to merge
- `S1.Entity1 == S2.Entity2` — entity equations (or use `@entity_equations` section)
- `@observation_equations forall x:S1.E . S1.att(x) = S2.att(x)` — observation equations

# Example
```julia
SC = @schema_colimit Ty begin
    @schemas S1, S2
    S1.Person == S2.Employee
    @options simplify_names = true
end
```

Returns a `SchemaColimitResult` with `.schema` and accessor for inclusion mappings.
"""
macro schema_colimit(ts_ref, block)
    stmts = _block_stmts(block)
    opts, stmts = _extract_options(stmts)

    schema_names = String[]
    schema_refs = []
    entity_eqs = Tuple{String,String}[]
    attr_eqs = Tuple{String,String}[]

    current_section = :entity  # default: bare == goes to entity_equations

    for s in stmts
        s isa LineNumberNode && continue
        if s isa Expr && s.head == :macrocall && s.args[1] == Symbol("@schemas")
            for a in s.args[2:end]
                a isa LineNumberNode && continue
                if a isa Symbol
                    push!(schema_names, string(a))
                    push!(schema_refs, a)
                elseif a isa Expr && a.head == :tuple
                    for e in a.args
                        if e isa Symbol
                            push!(schema_names, string(e))
                            push!(schema_refs, e)
                        end
                    end
                end
            end
        elseif s isa Expr && s.head == :macrocall && s.args[1] == Symbol("@entity_equations")
            current_section = :entity
            for a in s.args[2:end]
                a isa LineNumberNode && continue
                if a isa Expr && a.head == :call && a.args[1] == :(==)
                    push!(entity_eqs, (_expr_to_cql_path(a.args[2]), _expr_to_cql_path(a.args[3])))
                end
            end
        elseif s isa Expr && s.head == :macrocall && s.args[1] == Symbol("@observation_equations")
            current_section = :observation
            for a in s.args[2:end]
                a isa LineNumberNode && continue
                if a isa Symbol || (a isa Expr)
                    # Pass through as raw CQL observation equation text
                    push!(attr_eqs, (_expr_to_cql_path(a), ""))
                end
            end
        elseif s isa Expr && s.head == :call && s.args[1] == :(==)
            lhs = _expr_to_cql_path(s.args[2])
            rhs = _expr_to_cql_path(s.args[3])
            if current_section == :attribute
                push!(attr_eqs, (lhs, rhs))
            else
                push!(entity_eqs, (lhs, rhs))
            end
        end
    end

    schema_sum = join(schema_names, " + ")
    lines = String["schema_colimit _SC = quotient $schema_sum : _TS {"]
    if !isempty(entity_eqs)
        push!(lines, "    entity_equations")
        for (lhs, rhs) in entity_eqs
            push!(lines, "        $lhs = $rhs")
        end
    end
    # observation_equations would go here if needed
    if !isempty(opts)
        push!(lines, "    options")
        for (k, v) in opts
            push!(lines, "        $k = $v")
        end
    end
    push!(lines, "}")
    src = join(lines, "\n")

    # Build environment with all referenced schemas
    return esc(quote
        let _ts = $(ts_ref)
            _env = CQL._make_env_with_typeside("_TS", _ts)
            $([:(CQL._add_schema!(_env, $(string(n)), $(n))) for n in schema_refs]...)
            CQL._eval_fragment(_env, $src).colimits["_SC"]
        end
    end)
end

# ─── @constraints ────────────────────────────────────────────────────────────

"""
    @constraints schema_var cql_string

Define CQL constraints using CQL constraint syntax.

Since constraint syntax (∀/∃ with where-clauses) doesn't map cleanly to Julia
expressions, this macro takes the constraint body as a string.

# Example
```julia
C = @constraints S "forall a:A -> exists b:B where f(a) = b"
```
"""
macro constraints(sch_ref, body_str)
    return esc(quote
        let _sch = $(sch_ref)
            _env = CQL._make_env_with_schema("_S", _sch)
            _src = "constraints _C = literal : _S { " * $(body_str) * " }"
            CQL._eval_fragment(_env, _src).constraints["_C"]
        end
    end)
end
