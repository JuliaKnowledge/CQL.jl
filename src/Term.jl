"""
Core term AST for CQL.

Terms represent expressions in the CQL language. The 6 constructors correspond
to the Haskell type: Var | Sym sym [Term] | Fk fk Term | Att att Term | Gen gen | Sk sk

In Julia, we use Symbol for all identifiers in the evaluated/concrete types.
"""

# ============================================================================
# Term types
# ============================================================================

"""Abstract supertype for all CQL terms."""
abstract type CQLTerm end

"""A variable."""
struct CQLVar <: CQLTerm
    name::Symbol
end

"""A typeside function/constant symbol applied to arguments."""
struct CQLSym <: CQLTerm
    sym::Symbol
    args::Vector{CQLTerm}
end

"""A foreign key applied to a term."""
struct CQLFk <: CQLTerm
    fk::Symbol
    arg::CQLTerm
end

"""An attribute applied to a term."""
struct CQLAtt <: CQLTerm
    att::Symbol
    arg::CQLTerm
end

"""A generator (entity-sort witness)."""
struct CQLGen <: CQLTerm
    gen::Symbol
end

"""A Skolem term / labelled null (type-sort witness)."""
struct CQLSk <: CQLTerm
    sk::Symbol
end

# ============================================================================
# Head type (for tracking symbol occurrences)
# ============================================================================

"""A non-variable head symbol."""
@enum HeadKind H_SYM H_FK H_ATT H_GEN H_SK

struct Head
    kind::HeadKind
    name::Symbol
end

Base.:(==)(a::Head, b::Head) = a.kind == b.kind && a.name == b.name
Base.hash(h::Head, x::UInt) = hash((h.kind, h.name), x)

function head_of(t::CQLTerm)::Union{Head,Nothing}
    if t isa CQLSym
        Head(H_SYM, t.sym)
    elseif t isa CQLFk
        Head(H_FK, t.fk)
    elseif t isa CQLAtt
        Head(H_ATT, t.att)
    elseif t isa CQLGen
        Head(H_GEN, t.gen)
    elseif t isa CQLSk
        Head(H_SK, t.sk)
    else
        nothing
    end
end

# ============================================================================
# Show
# ============================================================================

function Base.show(io::IO, t::CQLVar)
    print(io, t.name)
end

function Base.show(io::IO, t::CQLGen)
    print(io, t.gen)
end

function Base.show(io::IO, t::CQLSk)
    print(io, t.sk)
end

function Base.show(io::IO, t::CQLFk)
    print(io, t.arg, ".", t.fk)
end

function Base.show(io::IO, t::CQLAtt)
    print(io, t.arg, ".", t.att)
end

function Base.show(io::IO, t::CQLSym)
    if isempty(t.args)
        print(io, t.sym)
    else
        print(io, t.sym, "(", join(t.args, ","), ")")
    end
end

# ============================================================================
# Equality and hashing
# ============================================================================

Base.:(==)(a::CQLVar, b::CQLVar) = a.name == b.name
Base.:(==)(a::CQLSym, b::CQLSym) = a === b || (a.sym == b.sym && a.args == b.args)
Base.:(==)(a::CQLFk, b::CQLFk) = a === b || (a.fk == b.fk && a.arg == b.arg)
Base.:(==)(a::CQLAtt, b::CQLAtt) = a === b || (a.att == b.att && a.arg == b.arg)
Base.:(==)(a::CQLGen, b::CQLGen) = a.gen == b.gen
Base.:(==)(a::CQLSk, b::CQLSk) = a.sk == b.sk
Base.:(==)(::CQLTerm, ::CQLTerm) = false

Base.hash(t::CQLVar, h::UInt) = hash(t.name, hash(0x56617200, h))
Base.hash(t::CQLSym, h::UInt) = hash(t.args, hash(t.sym, hash(0x53796d00, h)))
Base.hash(t::CQLFk, h::UInt) = hash(t.arg, hash(t.fk, hash(0x466b0000, h)))
Base.hash(t::CQLAtt, h::UInt) = hash(t.arg, hash(t.att, hash(0x41747400, h)))
Base.hash(t::CQLGen, h::UInt) = hash(t.gen, hash(0x47656e00, h))
Base.hash(t::CQLSk, h::UInt) = hash(t.sk, hash(0x536b0000, h))

# ============================================================================
# Equation type
# ============================================================================

"""An equation between two terms."""
struct Equation
    lhs::CQLTerm
    rhs::CQLTerm
end

Base.:(==)(a::Equation, b::Equation) = a.lhs == b.lhs && a.rhs == b.rhs
Base.hash(eq::Equation, h::UInt) = hash(eq.rhs, hash(eq.lhs, h))

function Base.show(io::IO, eq::Equation)
    print(io, eq.lhs, " = ", eq.rhs)
end

"""An aggregation term: sub-query with folding over matching tuples."""
struct CQLAgg <: CQLTerm
    from_ctx::Dict{Symbol, Symbol}     # sub-query from-clause (var -> entity)
    where_eqs::Vector{Equation}        # sub-query where-clause
    ret_term::CQLTerm                  # return expression
    zero::CQLTerm                      # aggregate zero element
    lambda_args::Tuple{Symbol, Symbol} # (accumulator, element)
    lambda_body::CQLTerm               # aggregate body
end

Base.:(==)(a::CQLAgg, b::CQLAgg) = a.from_ctx == b.from_ctx && a.where_eqs == b.where_eqs &&
    a.ret_term == b.ret_term && a.zero == b.zero && a.lambda_args == b.lambda_args && a.lambda_body == b.lambda_body
Base.hash(t::CQLAgg, h::UInt) = hash((:Agg, t.from_ctx, t.ret_term, t.zero), h)

function Base.show(io::IO, t::CQLAgg)
    print(io, "agg(from ", t.from_ctx, " return ", t.ret_term,
          " aggregate ", t.zero, " lambda ", t.lambda_args[1], " ", t.lambda_args[2],
          ". ", t.lambda_body, ")")
end

"""Context: mapping from variables to their sorts (type or entity)."""
const Ctx = Dict{Symbol, Either{Symbol,Symbol}}

# ============================================================================
# Term operations
# ============================================================================

"""Map functions over all components of a term."""
function map_term(t::CQLTerm;
    on_var::Function = identity,
    on_sym::Function = identity,
    on_fk::Function = identity,
    on_att::Function = identity,
    on_gen::Function = identity,
    on_sk::Function = identity)
    mt(x) = map_term(x; on_var, on_sym, on_fk, on_att, on_gen, on_sk)
    if t isa CQLVar
        CQLVar(on_var(t.name))
    elseif t isa CQLSym
        changed = false
        new_args = t.args
        for (i, a) in enumerate(t.args)
            na = mt(a)
            if na !== a
                if !changed
                    new_args = copy(t.args)
                    changed = true
                end
                new_args[i] = na
            end
        end
        new_sym = on_sym(t.sym)
        (changed || new_sym !== t.sym) ? CQLSym(new_sym, changed ? new_args : copy(t.args)) : t
    elseif t isa CQLFk
        na = mt(t.arg)
        new_fk = on_fk(t.fk)
        (na !== t.arg || new_fk !== t.fk) ? CQLFk(new_fk, na) : t
    elseif t isa CQLAtt
        na = mt(t.arg)
        new_att = on_att(t.att)
        (na !== t.arg || new_att !== t.att) ? CQLAtt(new_att, na) : t
    elseif t isa CQLGen
        new_gen = on_gen(t.gen)
        new_gen === t.gen ? t : CQLGen(new_gen)
    elseif t isa CQLSk
        new_sk = on_sk(t.sk)
        new_sk === t.sk ? t : CQLSk(new_sk)
    elseif t isa CQLAgg
        t  # CQLAgg is opaque to map_term
    else
        error("Unknown term type")
    end
end

"""Size of a term (number of nodes)."""
function term_size(t::CQLTerm)::Int
    if t isa CQLVar || t isa CQLGen || t isa CQLSk
        1
    elseif t isa CQLFk
        1 + term_size(t.arg)
    elseif t isa CQLAtt
        1 + term_size(t.arg)
    elseif t isa CQLSym
        1 + sum(term_size(a) for a in t.args; init=0)
    elseif t isa CQLAgg
        1 + term_size(t.ret_term) + term_size(t.zero) + term_size(t.lambda_body)
    else
        error("Unknown term type")
    end
end

"""Collect all variables in a term."""
function term_vars(t::CQLTerm)::Vector{Symbol}
    if t isa CQLVar
        [t.name]
    elseif t isa CQLGen || t isa CQLSk
        Symbol[]
    elseif t isa CQLFk
        term_vars(t.arg)
    elseif t isa CQLAtt
        term_vars(t.arg)
    elseif t isa CQLSym
        vcat([term_vars(a) for a in t.args]...)
    elseif t isa CQLAgg
        vcat(term_vars(t.ret_term), term_vars(t.zero), term_vars(t.lambda_body))
    else
        error("Unknown term type")
    end
end

"""True if the term has type-sort (as opposed to entity-sort).
Sym, Att, and Sk produce type-sort; Gen, Fk produce entity-sort.
Var is assumed entity-sort."""
function has_type_type(t::CQLTerm)::Bool
    t isa CQLSym || t isa CQLAtt || t isa CQLSk || t isa CQLAgg
end

"""Count occurrences of each head symbol in a term."""
function occs_term(t::CQLTerm)::Dict{Head,Int}
    result = Dict{Head,Int}()
    function count!(t)
        h = head_of(t)
        if h !== nothing
            result[h] = get(result, h, 0) + 1
        end
        if t isa CQLSym
            for a in t.args
                count!(a)
            end
        elseif t isa CQLFk || t isa CQLAtt
            count!(t.arg)
        end
    end
    count!(t)
    result
end

"""Check if a head symbol occurs in a term."""
function head_occurs(h::Head, t::CQLTerm)::Bool
    h2 = head_of(t)
    if h2 !== nothing && h == h2
        return true
    end
    if t isa CQLSym
        return any(a -> head_occurs(h, a), t.args)
    elseif t isa CQLFk || t isa CQLAtt
        return head_occurs(h, t.arg)
    end
    false
end

"""Fast check if a generator name occurs anywhere in a term (avoids Head allocation)."""
function gen_name_occurs(name::Symbol, t::CQLTerm)::Bool
    if t isa CQLGen;  return t.gen == name
    elseif t isa CQLFk;  return gen_name_occurs(name, t.arg)
    elseif t isa CQLAtt; return gen_name_occurs(name, t.arg)
    elseif t isa CQLSym; return any(a -> gen_name_occurs(name, a), t.args)
    end
    false
end

"""Fast check if a Skolem name occurs anywhere in a term (avoids Head allocation)."""
function sk_name_occurs(name::Symbol, t::CQLTerm)::Bool
    if t isa CQLSk;   return t.sk == name
    elseif t isa CQLFk;  return sk_name_occurs(name, t.arg)
    elseif t isa CQLAtt; return sk_name_occurs(name, t.arg)
    elseif t isa CQLSym; return any(a -> sk_name_occurs(name, a), t.args)
    end
    false
end

# ============================================================================
# Substitution
# ============================================================================

"""Substitute a variable (named :_unit, i.e. the single () variable) with a term.
This is the CQL pattern: terms with one variable () get substituted."""
function subst_term(template::CQLTerm, replacement::CQLTerm)::CQLTerm
    if template isa CQLVar
        replacement
    elseif template isa CQLSym
        changed = false
        new_args = template.args
        for (i, a) in enumerate(template.args)
            na = subst_term(a, replacement)
            if na !== a
                if !changed
                    new_args = copy(template.args)
                    changed = true
                end
                new_args[i] = na
            end
        end
        changed ? CQLSym(template.sym, new_args) : template
    elseif template isa CQLFk
        na = subst_term(template.arg, replacement)
        na === template.arg ? template : CQLFk(template.fk, na)
    elseif template isa CQLAtt
        na = subst_term(template.arg, replacement)
        na === template.arg ? template : CQLAtt(template.att, na)
    elseif template isa CQLGen
        template
    elseif template isa CQLSk
        template
    else
        error("Unknown term type in subst_term")
    end
end

"""Replace a head symbol with a term throughout a term."""
function replace_head(to_replace::Head, replacer::CQLTerm, t::CQLTerm)::CQLTerm
    h = head_of(t)
    if h !== nothing && h == to_replace
        # For Gen/Sk/nullary Sym, replace the whole term
        if t isa CQLGen || t isa CQLSk || (t isa CQLSym && isempty(t.args))
            return replacer
        end
    end
    if t isa CQLSym
        changed = false
        new_args = t.args
        for (i, a) in enumerate(t.args)
            na = replace_head(to_replace, replacer, a)
            if na !== a
                if !changed
                    new_args = copy(t.args)
                    changed = true
                end
                new_args[i] = na
            end
        end
        changed ? CQLSym(t.sym, new_args) : t
    elseif t isa CQLFk
        na = replace_head(to_replace, replacer, t.arg)
        na === t.arg ? t : CQLFk(t.fk, na)
    elseif t isa CQLAtt
        na = replace_head(to_replace, replacer, t.arg)
        na === t.arg ? t : CQLAtt(t.att, na)
    else
        t
    end
end

"""Apply a sequence of head replacements to a term."""
function replace_repeatedly(replacements::Vector{Tuple{Head,CQLTerm}}, t::CQLTerm)::CQLTerm
    for (h, r) in replacements
        t = replace_head(h, r, t)
    end
    t
end

# ============================================================================
# Theory = Set of (context, equation) pairs
# ============================================================================

"""A theory: a set of (context, equation) pairs."""
const Theory = Set{Tuple{Ctx, Equation}}

"""Find an equation of the form gen/sk = term where gen/sk doesn't occur in term.
Used for theory simplification."""
function find_simplifiable_eq(theory::Theory)::Union{Nothing, Tuple{Head, CQLTerm}}
    # Two passes: first prefer replacing generated Skolems (those with dots),
    # which preserves literal values as canonical representatives.
    for (ctx, eq) in theory
        !isempty(ctx) && continue
        result = _try_simplify_prefer_generated(eq.lhs, eq.rhs)
        if result !== nothing
            return result
        end
        result = _try_simplify_prefer_generated(eq.rhs, eq.lhs)
        if result !== nothing
            return result
        end
    end
    # Fallback: any simplification
    for (ctx, eq) in theory
        !isempty(ctx) && continue
        result = _try_simplify(eq.lhs, eq.rhs)
        if result !== nothing
            return result
        end
        result = _try_simplify(eq.rhs, eq.lhs)
        if result !== nothing
            return result
        end
    end
    nothing
end

"""Check if a Skolem looks like a generated/attribute Skolem (contains dot but is not a number)."""
function _is_generated_skolem(s::Symbol)
    str = string(s)
    occursin('.', str) && tryparse(Float64, str) === nothing
end

"""Try to simplify by preferring to replace generated Skolems over literals."""
function _try_simplify_prefer_generated(lhs::CQLTerm, rhs::CQLTerm)
    if lhs isa CQLSk && _is_generated_skolem(lhs.sk)
        !sk_name_occurs(lhs.sk, rhs) && return (Head(H_SK, lhs.sk), rhs)
    elseif lhs isa CQLGen
        !gen_name_occurs(lhs.gen, rhs) && return (Head(H_GEN, lhs.gen), rhs)
    end
    nothing
end

function _try_simplify(lhs::CQLTerm, rhs::CQLTerm)
    if lhs isa CQLSk
        !sk_name_occurs(lhs.sk, rhs) && return (Head(H_SK, lhs.sk), rhs)
    elseif lhs isa CQLGen
        !gen_name_occurs(lhs.gen, rhs) && return (Head(H_GEN, lhs.gen), rhs)
    end
    nothing
end

"""Simplify a theory by repeatedly finding and eliminating gen/sk = term equations.
Returns (simplified_theory, list of replacements made)."""
function simplify_theory(theory::Theory, substs::Vector{Tuple{Head,CQLTerm}} = Tuple{Head,CQLTerm}[])
    # Convert to Vector for faster iteration (avoid Set hashing overhead)
    eqs = collect(theory)
    while true
        # Batch: collect ALL independent simplifiable equations in one pass
        batch = _find_all_simplifiable(eqs)
        isempty(batch) && return (Set{Tuple{Ctx,Equation}}(eqs), substs)

        # Apply all replacements in batch
        for (to_remove, replacer) in batch
            j = 0
            for i in eachindex(eqs)
                (ctx, eq) = eqs[i]
                new_lhs = replace_head(to_remove, replacer, eq.lhs)
                new_rhs = replace_head(to_remove, replacer, eq.rhs)
                if new_lhs != new_rhs
                    j += 1
                    eqs[j] = (ctx, Equation(new_lhs, new_rhs))
                end
            end
            resize!(eqs, j)
            push!(substs, (to_remove, replacer))
        end
    end
end

"""Find all independent simplifiable equations in one pass.
Returns a vector of (Head, CQLTerm) pairs. Heads in the batch are independent:
no removed head appears in any replacer term."""
function _find_all_simplifiable(eqs::Vector{Tuple{Ctx,Equation}})::Vector{Tuple{Head, CQLTerm}}
    batch = Tuple{Head, CQLTerm}[]
    removed = Set{Symbol}()  # names already scheduled for removal

    # First pass: prefer generated skolems and gens
    for (ctx, eq) in eqs
        !isempty(ctx) && continue
        result = _try_simplify_prefer_generated(eq.lhs, eq.rhs)
        if result === nothing
            result = _try_simplify_prefer_generated(eq.rhs, eq.lhs)
        end
        if result !== nothing
            (h, replacer) = result
            # Check independence: h.name not already removed, and no removed name in replacer
            if !(h.name in removed) && !_any_name_occurs(removed, replacer)
                push!(batch, result)
                push!(removed, h.name)
            end
        end
    end

    # Second pass: general simplification for remaining equations
    for (ctx, eq) in eqs
        !isempty(ctx) && continue
        result = _try_simplify(eq.lhs, eq.rhs)
        if result === nothing
            result = _try_simplify(eq.rhs, eq.lhs)
        end
        if result !== nothing
            (h, replacer) = result
            if !(h.name in removed) && !_any_name_occurs(removed, replacer)
                push!(batch, result)
                push!(removed, h.name)
            end
        end
    end

    batch
end

"""Check if any name from the set occurs in a term."""
function _any_name_occurs(names::Set{Symbol}, t::CQLTerm)::Bool
    if t isa CQLGen; return t.gen in names
    elseif t isa CQLSk; return t.sk in names
    elseif t isa CQLFk; return _any_name_occurs(names, t.arg)
    elseif t isa CQLAtt; return _any_name_occurs(names, t.arg)
    elseif t isa CQLSym; return any(a -> _any_name_occurs(names, a), t.args)
    end
    false
end

# ============================================================================
# RawTerm for parsing
# ============================================================================

"""Unparsed/raw term from the parser."""
struct RawTerm
    head::String
    args::Vector{RawTerm}
end

function Base.show(io::IO, t::RawTerm)
    if isempty(t.args)
        print(io, t.head)
    else
        print(io, t.head, "(", join(t.args, ","), ")")
    end
end

Base.:(==)(a::RawTerm, b::RawTerm) = a.head == b.head && a.args == b.args
Base.hash(t::RawTerm, h::UInt) = hash((t.head, t.args), h)
