"""
Queries: the uber-flower pattern (from-where-return).

A query Q: S -> T consists of:
- For each target entity: a context (from-clause), where-clause, attribute terms, FK variable mappings
"""

# ============================================================================
# Expression types (must come first for forward references)
# ============================================================================

abstract type QueryExp end

struct QueryVar <: QueryExp
    name::String
end

struct QueryId <: QueryExp
    schema::SchemaExp
end

"""Raw query data from parsing. Each entity block contains from, where, attributes, and foreign_keys."""
struct QueryExpRaw
    src_ref::Any  # SchemaExp
    dst_ref::Any  # SchemaExp
    # entity_name -> (from_bindings, where_eqs, att_mappings, fk_mappings)
    ens::Vector{Tuple{String, Tuple{
        Vector{Tuple{String,String}},                        # from: var -> entity
        Vector{Tuple{RawTerm,RawTerm}},                      # where: eq pairs
        Vector{Tuple{String,RawTerm}},                       # attributes: att -> term
        Vector{Tuple{String,Vector{Tuple{String,RawTerm}}}}  # foreign_keys: fk -> [var -> term]
    }}}
    options::Vector{Tuple{String,String}}
    imports::Vector{Any}
end

struct QueryRawExp <: QueryExp
    raw::QueryExpRaw
end

struct QueryComp <: QueryExp
    first::QueryExp
    second::QueryExp
end

struct QueryToQuery <: QueryExp
    mapping::Any  # MappingExp (defined earlier)
end

struct QueryToCoQuery <: QueryExp
    mapping::Any  # MappingExp (defined earlier)
end

"""Front query of constraint: front constraints index"""
struct QueryFront <: QueryExp
    constraints_name::String
    index::Int
end

"""Back query of constraint: back constraints index"""
struct QueryBack <: QueryExp
    constraints_name::String
    index::Int
end

"""Right extension: rext q1 q2"""
struct QueryRext <: QueryExp
    q1::QueryExp
    q2::QueryExp
end

"""Spanify query: spanify schema"""
struct QuerySpanify <: QueryExp
    schema::Any  # SchemaExp
end

"""Spanify mapping query: spanify_mapping mapping"""
struct QuerySpanifyMapping <: QueryExp
    mapping::Any  # MappingExp
end

"""Query include: include src_schema tgt_schema"""
struct QueryInclude <: QueryExp
    src_schema::Any  # SchemaExp
    tgt_schema::Any  # SchemaExp
end

"""Query from co-span: fromCoSpan mapping1 mapping2"""
struct QueryFromCoSpan <: QueryExp
    m1::Any  # MappingExp
    m2::Any  # MappingExp
end

"""Query from constraints: fromConstraints index constraints"""
struct QueryFromConstraints <: QueryExp
    index::Int
    constraints_name::String
end

"""Chase a query with constraints: chase C Q"""
struct QueryChase <: QueryExp
    constraints::Any  # String (name ref) or constraints expression
    query::QueryExp
end

"""Reformulate query: reformulate C Q T N"""
struct QueryReformulate <: QueryExp
    constraints::Any  # String (name ref) or constraints expression
    query::QueryExp
    schema::Any       # SchemaExp
    index::Int
end

function deps(e::QueryExp)::Vector{Tuple{String,Kind}}
    if e isa QueryVar
        [(e.name, QUERY)]
    elseif e isa QueryId
        deps(e.schema)
    elseif e isa QueryRawExp
        src_deps = e.raw.src_ref isa SchemaExp ? deps(e.raw.src_ref) : Tuple{String,Kind}[]
        dst_deps = e.raw.dst_ref isa SchemaExp ? deps(e.raw.dst_ref) : Tuple{String,Kind}[]
        vcat(src_deps, dst_deps, vcat([deps(i) for i in e.raw.imports]...))
    elseif e isa QueryComp
        vcat(deps(e.first), deps(e.second))
    elseif e isa QueryToQuery
        e.mapping isa MappingExp ? deps(e.mapping) : Tuple{String,Kind}[]
    elseif e isa QueryToCoQuery
        e.mapping isa MappingExp ? deps(e.mapping) : Tuple{String,Kind}[]
    elseif e isa QueryFront
        [(e.constraints_name, CONSTRAINTS)]
    elseif e isa QueryBack
        [(e.constraints_name, CONSTRAINTS)]
    elseif e isa QueryRext
        vcat(deps(e.q1), deps(e.q2))
    elseif e isa QuerySpanify
        e.schema isa SchemaExp ? deps(e.schema) : Tuple{String,Kind}[]
    elseif e isa QuerySpanifyMapping
        e.mapping isa MappingExp ? deps(e.mapping) : Tuple{String,Kind}[]
    elseif e isa QueryInclude
        result = Tuple{String,Kind}[]
        e.src_schema isa SchemaExp && append!(result, deps(e.src_schema))
        e.tgt_schema isa SchemaExp && append!(result, deps(e.tgt_schema))
        result
    elseif e isa QueryFromCoSpan
        result = Tuple{String,Kind}[]
        e.m1 isa MappingExp && append!(result, deps(e.m1))
        e.m2 isa MappingExp && append!(result, deps(e.m2))
        result
    elseif e isa QueryFromConstraints
        [(e.constraints_name, CONSTRAINTS)]
    elseif e isa QueryChase
        d = deps(e.query)
        if e.constraints isa String
            push!(d, (e.constraints, CONSTRAINTS))
        end
        d
    elseif e isa QueryReformulate
        d = deps(e.query)
        if e.constraints isa String
            push!(d, (e.constraints, CONSTRAINTS))
        end
        if e.schema isa SchemaExp
            append!(d, deps(e.schema))
        end
        d
    else
        Tuple{String,Kind}[]
    end
end

# ============================================================================
# Core query type
# ============================================================================

"""A CQL query from source schema to target schema."""
struct CQLQuery
    src::CQLSchema
    dst::CQLSchema
    ens::Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}
        # target entity -> (var->src_entity context, where-clause equations)
    fks::Dict{Symbol, Dict{Symbol, CQLTerm}}
        # target fk -> (tgt_entity_var -> term in src_entity_vars)
    atts::Dict{Symbol, CQLTerm}
        # target att -> term in source vars
end

function Base.:(==)(a::CQLQuery, b::CQLQuery)
    a.src == b.src && a.dst == b.dst && a.ens == b.ens && a.fks == b.fks && a.atts == b.atts
end

function Base.show(io::IO, q::CQLQuery)
    println(io, "query {")
    for (en, (ctx, wh)) in q.ens
        println(io, "  entity ", en, " -> {")
        println(io, "    from")
        for (v, e) in ctx
            println(io, "      ", v, " : ", e)
        end
        if !isempty(wh)
            println(io, "    where")
            for eq in wh
                println(io, "      ", eq)
            end
        end
        println(io, "  }")
    end
    for (fk, mapping) in q.fks
        println(io, "  foreign_key ", fk, " -> {")
        for (v, t) in mapping
            println(io, "    ", v, " -> ", t)
        end
        println(io, "  }")
    end
    println(io, "  attributes")
    for (att, t) in q.atts
        println(io, "    ", att, " -> ", t)
    end
    println(io, "}")
end

"""Create an identity query on a schema."""
function identity_query(sch::CQLSchema)
    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}()
    for en in sch.ens
        ens[en] = (Dict(:x => en), Set{Equation}())
    end

    fks = Dict{Symbol, Dict{Symbol, CQLTerm}}()
    for (fk, (src, tgt)) in sch.fks
        fks[fk] = Dict(:x => CQLFk(fk, CQLVar(:x)))
    end

    atts = Dict{Symbol, CQLTerm}()
    for (att, (src, ty)) in sch.atts
        atts[att] = CQLAtt(att, CQLVar(:x))
    end

    CQLQuery(sch, sch, ens, fks, atts)
end

"""Convert a mapping F : S → T to the delta query Q : T → S.

For each source entity E_S with F(E_S) = E_T, the query block has:
- from: x : E_T
- attributes: F.atts[att_S] with _unit replaced by x
- foreign_keys: F.fks[fk_S] with _unit replaced by x
"""
function mapping_to_query(m::CQLMapping)::CQLQuery
    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}()
    fks = Dict{Symbol, Dict{Symbol, CQLTerm}}()
    atts = Dict{Symbol, CQLTerm}()

    for (src_en, tgt_en) in m.ens
        ens[src_en] = (Dict(:x => tgt_en), Set{Equation}())
    end

    for (att_s, att_term) in m.atts
        atts[att_s] = _replace_unit_var(att_term, :x)
    end

    for (fk_s, fk_term) in m.fks
        (_, tgt_en) = m.src.fks[fk_s]
        fks[fk_s] = Dict(:x => _replace_unit_var(fk_term, :x))
    end

    CQLQuery(m.dst, m.src, ens, fks, atts)
end

"""Replace CQLVar(:_unit) with CQLVar(new_name) in a term."""
function _replace_unit_var(t::CQLTerm, new_name::Symbol)::CQLTerm
    if t isa CQLVar
        t.name == :_unit ? CQLVar(new_name) : t
    elseif t isa CQLFk
        CQLFk(t.fk, _replace_unit_var(t.arg, new_name))
    elseif t isa CQLAtt
        CQLAtt(t.att, _replace_unit_var(t.arg, new_name))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_replace_unit_var(a, new_name) for a in t.args])
    else
        t
    end
end

"""Compose two queries: f : A -> B, g : B -> C => [f;g] : A -> C"""
function compose_query(f::CQLQuery, g::CQLQuery)::CQLQuery
    # f: A → B, g: B → C, result g∘f: A → C
    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}()
    fks = Dict{Symbol, Dict{Symbol, CQLTerm}}()
    atts = Dict{Symbol, CQLTerm}()

    # Fresh variable counter (matching Java's vv0, vv1, ... naming)
    vv_counter = Ref(0)
    function fresh_var()
        n = vv_counter[]
        vv_counter[] += 1
        Symbol("vv", n)
    end

    # Build var_expansion for each g entity block
    en_var_expansion = Dict{Symbol, Dict{Symbol, Dict{Symbol, CQLTerm}}}()
    en_prefix_rename = Dict{Symbol, Dict{Symbol, Dict{Symbol, Symbol}}}()
    en_type_var_rename = Dict{Symbol, Dict{Symbol, Symbol}}()

    for (g_en, (g_ctx, g_where)) in g.ens
        combined_ctx = Dict{Symbol,Symbol}()
        combined_where = Set{Equation}()
        var_expansion = Dict{Symbol, Dict{Symbol, CQLTerm}}()
        # Map from (g_var, f_var) to fresh vv name for prefix substitution
        prefix_rename = Dict{Symbol, Dict{Symbol, Symbol}}()

        # Map from original type-sorted var to fresh vv name
        type_var_rename = Dict{Symbol, Symbol}()

        for (g_var, g_entity) in g_ctx
            if haskey(f.ens, g_entity)
                f_ctx, f_where = f.ens[g_entity]
                prefix_rename[g_var] = Dict{Symbol, Symbol}()
                local_expansion = Dict{Symbol, CQLTerm}()
                for (f_var, f_entity) in f_ctx
                    new_var = fresh_var()
                    combined_ctx[new_var] = f_entity
                    prefix_rename[g_var][f_var] = new_var
                    local_expansion[f_var] = CQLVar(new_var)
                end
                var_expansion[g_var] = local_expansion
                for eq in f_where
                    new_lhs = _prefix_query_term_renamed(eq.lhs, prefix_rename[g_var])
                    new_rhs = _prefix_query_term_renamed(eq.rhs, prefix_rename[g_var])
                    push!(combined_where, Equation(new_lhs, new_rhs))
                end
            else
                # Type-sorted variable: assign fresh vv name (matching Java behavior)
                new_var = fresh_var()
                combined_ctx[new_var] = g_entity
                type_var_rename[g_var] = new_var
            end
        end

        en_var_expansion[g_en] = var_expansion
        en_prefix_rename[g_en] = prefix_rename
        en_type_var_rename[g_en] = type_var_rename

        # Translate g-where clauses through f, applying type var renames
        for eq in g_where
            new_lhs = _compose_query_type_term(eq.lhs, var_expansion, f, g_ctx; type_var_rename=type_var_rename)
            new_rhs = _compose_query_type_term(eq.rhs, var_expansion, f, g_ctx; type_var_rename=type_var_rename)
            push!(combined_where, Equation(new_lhs, new_rhs))
        end

        ens[g_en] = (combined_ctx, combined_where)
    end

    # Compose FK mappings
    for (g_fk, g_fk_map) in g.fks
        (g_fk_src_en, g_fk_tgt_en) = g.dst.fks[g_fk]
        (g_src_ctx, _) = g.ens[g_fk_src_en]
        (g_tgt_ctx, _) = g.ens[g_fk_tgt_en]
        src_expansion = en_var_expansion[g_fk_src_en]
        src_type_rename = get(en_type_var_rename, g_fk_src_en, Dict{Symbol, Symbol}())
        tgt_rename = get(en_prefix_rename, g_fk_tgt_en, Dict{Symbol, Dict{Symbol, Symbol}}())
        tgt_type_rename = get(en_type_var_rename, g_fk_tgt_en, Dict{Symbol, Symbol}())

        new_fk_map = Dict{Symbol, CQLTerm}()
        for (g_tgt_var, g_src_term) in g_fk_map
            tgt_sort = g_tgt_ctx[g_tgt_var]
            if haskey(f.ens, tgt_sort)
                # Entity-sorted target variable: expand through f
                composed_env = _compose_query_entity_env(g_src_term, src_expansion, f, g_src_ctx)
                vv_names = get(tgt_rename, g_tgt_var, Dict{Symbol, Symbol}())
                for (f_var, composed_term) in composed_env
                    vv_name = get(vv_names, f_var, Symbol(g_tgt_var, "_", f_var))
                    new_fk_map[vv_name] = _apply_type_var_rename(composed_term, src_type_rename)
                end
            else
                # Type-sorted target variable: use renamed target var name
                renamed_tgt = get(tgt_type_rename, g_tgt_var, g_tgt_var)
                new_fk_map[renamed_tgt] = _apply_type_var_rename(
                    _compose_query_type_term(g_src_term, src_expansion, f, g_src_ctx; type_var_rename=src_type_rename),
                    src_type_rename)
            end
        end
        fks[g_fk] = new_fk_map
    end

    # Compose attribute mappings
    for (g_att, g_term) in g.atts
        (att_src_en, _) = g.dst.atts[g_att]
        (g_att_ctx, _) = g.ens[att_src_en]
        att_expansion = en_var_expansion[att_src_en]
        att_type_rename = get(en_type_var_rename, att_src_en, Dict{Symbol, Symbol}())
        atts[g_att] = _apply_type_var_rename(
            _compose_query_type_term(g_term, att_expansion, f, g_att_ctx; type_var_rename=att_type_rename),
            att_type_rename)
    end

    result = CQLQuery(f.src, g.dst, ens, fks, atts)
    # Remove redundant variables (matching Java's query_remove_redundancy)
    _remove_redundant_vars!(result)
    return result
end

"""Remove redundant variables from a composed query.
A variable is redundant if it appears alone on one side of a where equation
and not on the other side — meaning it's fully determined."""
function _remove_redundant_vars!(q::CQLQuery)
    changed = true
    while changed
        changed = false
        for (en, (ctx, where_eqs)) in q.ens
            redundant = _find_redundant_var(ctx, where_eqs, q)
            if redundant !== nothing
                (var, replacement_term) = redundant
                _eliminate_var!(q, en, var, replacement_term)
                changed = true
                break  # restart after modification
            end
        end
    end
end

"""Find a redundant variable in a query entity block.
Returns (var_name, replacement_term) or nothing."""
function _find_redundant_var(ctx::Dict{Symbol,Symbol}, where_eqs::Set{Equation}, q::CQLQuery)
    for eq in where_eqs
        # Check if LHS is a bare variable
        result = _check_side_redundant(eq.lhs, eq.rhs, ctx, q)
        if result !== nothing
            return result
        end
        # Check if RHS is a bare variable
        result = _check_side_redundant(eq.rhs, eq.lhs, ctx, q)
        if result !== nothing
            return result
        end
    end
    return nothing
end

function _check_side_redundant(candidate::CQLTerm, other::CQLTerm, ctx::Dict{Symbol,Symbol}, q::CQLQuery)
    if candidate isa CQLVar && haskey(ctx, candidate.name)
        # Check that this variable doesn't appear in the other side
        if !(candidate.name in _collect_vars(other))
            return (candidate.name, other)
        end
    end
    return nothing
end

"""Collect all variable names used in a term."""
function _collect_vars(t::CQLTerm)::Set{Symbol}
    result = Set{Symbol}()
    _collect_vars!(t, result)
    return result
end

function _collect_vars!(t::CQLTerm, result::Set{Symbol})
    if t isa CQLVar
        push!(result, t.name)
    elseif t isa CQLFk
        _collect_vars!(t.arg, result)
    elseif t isa CQLAtt
        _collect_vars!(t.arg, result)
    elseif t isa CQLSym
        for a in t.args
            _collect_vars!(a, result)
        end
    end
end

"""Eliminate a variable from a query entity block by substituting its replacement."""
function _eliminate_var!(q::CQLQuery, en::Symbol, var::Symbol, replacement::CQLTerm)
    ctx, where_eqs = q.ens[en]
    # Remove from context
    delete!(ctx, var)
    # Substitute in all where equations
    new_where = Set{Equation}()
    for eq in where_eqs
        new_lhs = _subst_var(eq.lhs, var, replacement)
        new_rhs = _subst_var(eq.rhs, var, replacement)
        # Skip trivial equations (lhs == rhs after substitution)
        if new_lhs != new_rhs
            push!(new_where, Equation(new_lhs, new_rhs))
        end
    end
    q.ens[en] = (ctx, new_where)
    # Substitute in FK mappings
    for (fk, fk_map) in q.fks
        (src_en, tgt_en) = q.dst.fks[fk]
        if src_en == en
            # Substitute var in source terms
            for (tgt_var, term) in fk_map
                q.fks[fk][tgt_var] = _subst_var(term, var, replacement)
            end
        end
        if tgt_en == en
            # Remove the eliminated var from FK target mapping
            delete!(fk_map, var)
        end
    end
    # Substitute in attribute mappings for atts sourced from this entity
    for (att, term) in q.atts
        (src_en, _) = q.dst.atts[att]
        if src_en == en
            q.atts[att] = _subst_var(term, var, replacement)
        end
    end
end

"""Substitute a variable with a replacement term."""
function _subst_var(t::CQLTerm, var::Symbol, replacement::CQLTerm)::CQLTerm
    if t isa CQLVar
        t.name == var ? replacement : t
    elseif t isa CQLFk
        CQLFk(t.fk, _subst_var(t.arg, var, replacement))
    elseif t isa CQLAtt
        CQLAtt(t.att, _subst_var(t.arg, var, replacement))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_subst_var(a, var, replacement) for a in t.args])
    else
        t
    end
end

"""Prefix variable names in a term."""
function _prefix_query_term(t::CQLTerm, prefix::Symbol)::CQLTerm
    if t isa CQLVar
        CQLVar(Symbol(prefix, "_", t.name))
    elseif t isa CQLFk
        CQLFk(t.fk, _prefix_query_term(t.arg, prefix))
    elseif t isa CQLAtt
        CQLAtt(t.att, _prefix_query_term(t.arg, prefix))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_prefix_query_term(a, prefix) for a in t.args])
    else
        t
    end
end

"""Rename variable names in a term using a rename map (var → new_name)."""
function _prefix_query_term_renamed(t::CQLTerm, rename::Dict{Symbol, Symbol})::CQLTerm
    if t isa CQLVar
        CQLVar(get(rename, t.name, t.name))
    elseif t isa CQLFk
        CQLFk(t.fk, _prefix_query_term_renamed(t.arg, rename))
    elseif t isa CQLAtt
        CQLAtt(t.att, _prefix_query_term_renamed(t.arg, rename))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_prefix_query_term_renamed(a, rename) for a in t.args])
    else
        t
    end
end

"""Compose an entity-level term through query f, returning an environment
mapping f's target entity variables to composed terms over A's FKs."""
function _compose_query_entity_env(t::CQLTerm, var_expansion, f_query, g_ctx)::Dict{Symbol, CQLTerm}
    if t isa CQLVar
        # t.name is a g-variable of type g_ctx[t.name] in B
        return var_expansion[t.name]
    elseif t isa CQLFk
        # fk: E_src → E_tgt in B (= f.dst)
        # inner gives us E_src env; f.fks[fk] maps E_tgt vars → E_src terms
        inner_env = _compose_query_entity_env(t.arg, var_expansion, f_query, g_ctx)
        if haskey(f_query.fks, t.fk)
            fk_map = f_query.fks[t.fk]
            composed = Dict{Symbol, CQLTerm}()
            for (tgt_var, src_term) in fk_map
                composed[tgt_var] = _apply_env_to_term(src_term, inner_env)
            end
            return composed
        else
            # FK not in f's mapping — it's an identity-like FK
            return inner_env
        end
    else
        error("Cannot compose entity term: $t")
    end
end

"""Compose a type-level term (attributes, symbols) through query f."""
function _compose_query_type_term(t::CQLTerm, var_expansion, f_query, g_ctx; type_var_rename::Dict{Symbol,Symbol}=Dict{Symbol,Symbol}())::CQLTerm
    if t isa CQLAtt
        inner_env = _compose_query_entity_env(t.arg, var_expansion, f_query, g_ctx)
        if haskey(f_query.atts, t.att)
            att_term = f_query.atts[t.att]
            return _apply_env_to_term(att_term, inner_env)
        else
            # Att not in f's mapping — pass through with composed inner
            return CQLAtt(t.att, first(values(inner_env)))
        end
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_compose_query_type_term(a, var_expansion, f_query, g_ctx; type_var_rename=type_var_rename) for a in t.args])
    elseif t isa CQLFk
        # Entity-level term appearing in a type context (shouldn't normally happen)
        env = _compose_query_entity_env(t, var_expansion, f_query, g_ctx)
        first(values(env))
    elseif t isa CQLVar && haskey(var_expansion, t.name)
        first(values(var_expansion[t.name]))
    elseif t isa CQLVar && haskey(type_var_rename, t.name)
        CQLVar(type_var_rename[t.name])
    else
        t  # constants, skolems pass through
    end
end

"""Apply type variable renaming to a term (rename old type var names to fresh vv names)."""
function _apply_type_var_rename(t::CQLTerm, rename::Dict{Symbol, Symbol})::CQLTerm
    isempty(rename) && return t
    if t isa CQLVar
        new_name = get(rename, t.name, nothing)
        new_name !== nothing ? CQLVar(new_name) : t
    elseif t isa CQLFk
        CQLFk(t.fk, _apply_type_var_rename(t.arg, rename))
    elseif t isa CQLAtt
        CQLAtt(t.att, _apply_type_var_rename(t.arg, rename))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_apply_type_var_rename(a, rename) for a in t.args])
    else
        t
    end
end

"""Apply a variable-to-term environment to a term."""
function _apply_env_to_term(t::CQLTerm, env::Dict{Symbol, CQLTerm})::CQLTerm
    if t isa CQLVar
        get(env, t.name, t)
    elseif t isa CQLFk
        CQLFk(t.fk, _apply_env_to_term(t.arg, env))
    elseif t isa CQLAtt
        CQLAtt(t.att, _apply_env_to_term(t.arg, env))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_apply_env_to_term(a, env) for a in t.args])
    else
        t
    end
end

# ============================================================================
# Query evaluation on instances
# ============================================================================

"""
Evaluate a query on an instance: given Q: S -> T and instance I on S,
produce an instance on T.

For each target entity, we enumerate all satisfying variable assignments
from the source instance, then build a presentation and initial algebra.
"""
function eval_query_instance(q::CQLQuery, inst::CQLInstance, opts::CQLOptions)
    (_, _, _, pres) = _eval_query_data(q, inst)
    _instance_from_query_pres(q, pres, opts)
end

"""Build an instance from query presentation (shared by eval_query_instance and callers that
already have query data)."""
function _instance_from_query_pres(q::CQLQuery, pres::Presentation, opts::CQLOptions)
    # Query results have fully-computed FK/attribute equations from the
    # tuple enumeration, so use saturated_instance (direct algebra
    # interpretation) which avoids theorem-proving issues with complex
    # path equations on the target schema.
    #
    # However, when the query has type-sorted from-variables and the source
    # instance has a non-trivial type algebra (e.g. coeval instances), some
    # FK equations may be missing because the FK mapping produces compound
    # type terms that don't match any enumerated tuple.  In this case, fall
    # back to initial_instance which handles missing equations via carrier
    # closure and the theorem prover.
    try
        saturated_instance(q.dst, pres)
    catch e
        if e isa CQLException && contains(e.msg, "Missing equation")
            col = presentation_to_collage(q.dst, pres)
            prover, canonical = create_prover_with_canonical(col, opts)
            dp_fn = eq -> prover(Ctx(), eq)
            initial_instance(pres, dp_fn, q.dst; canonical_fn=canonical)
        else
            rethrow()
        end
    end
end

"""Get query provenance: maps each gen Symbol to (entity, Dict(var => source_elem)).
Returns gen_to_tuple mapping for formatting FK targets as (var=inl idx)."""
function query_provenance(q::CQLQuery, inst::CQLInstance)
    (_, _, gen_to_tuple, _) = _eval_query_data(q, inst)
    gen_to_tuple
end

"""Core query evaluation: enumerate tuples, build generators and equations.

Returns (entity_tuples, tuple_to_gen, gen_to_tuple, presentation)."""
function _eval_query_data(q::CQLQuery, inst::CQLInstance)
    src_alg = inst.algebra

    entity_tuples = Dict{Symbol, Vector{Dict{Symbol, Any}}}()
    ts_rules = _build_typeside_rules(inst.schema.typeside)

    for (tgt_en, (ctx, where_eqs)) in q.ens
        vars = collect(keys(ctx))
        if isempty(vars)
            entity_tuples[tgt_en] = [Dict{Symbol, Any}()]
            continue
        end
        src_entities = [ctx[v] for v in vars]
        src_carriers = Any[]
        for en in src_entities
            if haskey(src_alg.en, en)
                push!(src_carriers, collect(carrier(src_alg, en)))
            elseif haskey(src_alg.ty, en)
                # Type-sorted variable: enumerate type carrier elements
                push!(src_carriers, collect(src_alg.ty[en]))
            else
                push!(src_carriers, Any[])  # empty carrier
            end
        end

        # Track which variables are type-sorted for normalization
        type_sorted_vars = Set{Symbol}()
        for (j, en) in enumerate(src_entities)
            if !haskey(src_alg.en, en)
                push!(type_sorted_vars, vars[j])
            end
        end

        valid = Dict{Symbol, Any}[]
        valid_hashes = Dict{UInt, Vector{Int}}()  # hash → indices in valid (for dedup)
        # Reusable assignment buffer — only copied when tuple passes filter
        assign_buf = Dict{Symbol, Any}()
        sizehint!(assign_buf, length(vars))
        for combo in Iterators.product(src_carriers...)
            empty!(assign_buf)
            for i in eachindex(vars)
                assign_buf[vars[i]] = combo[i]
            end
            # Normalize type-sorted variable values to CQLTerm using nf_y for
            # consistency with eval_att (which also uses nf_y).  Using repr_y
            # here would create a mismatch: eval_att returns nf_y-normalized
            # values but variable references would return repr_y values,
            # causing compound terms like and(nf_y_val, repr_y_val) that
            # can't be matched against any carrier element.
            for v in type_sorted_vars
                val = assign_buf[v]
                if val isa TalgGen
                    assign_buf[v] = _reduce_typeside(ts_rules, src_alg.nf_y(val.val))
                elseif haskey(src_alg.repr_y, val)
                    assign_buf[v] = _reduce_typeside(ts_rules, src_alg.repr_y[val])
                end
            end
            all_ok = true
            for eq in where_eqs
                if _is_type_level(eq.lhs) || _is_type_level(eq.rhs)
                    lval = _reduce_typeside(ts_rules, _eval_query_term_type(src_alg, assign_buf, eq.lhs))
                    rval = _reduce_typeside(ts_rules, _eval_query_term_type(src_alg, assign_buf, eq.rhs))
                    if lval != rval && !inst.dp(Equation(lval, rval))
                        lv = _try_eval_native(lval)
                        rv = _try_eval_native(rval)
                        if lv === nothing || rv === nothing || lv != rv
                            all_ok = false; break
                        end
                    end
                else
                    lval = _eval_query_term_entity(src_alg, assign_buf, eq.lhs)
                    rval = _eval_query_term_entity(src_alg, assign_buf, eq.rhs)
                    if lval != rval
                        all_ok = false; break
                    end
                end
            end
            if all_ok
                # Dedup: skip if an equivalent tuple already exists (can happen
                # when multiple TalgGen elements share the same nf_y value)
                is_dup = false
                if !isempty(type_sorted_vars)
                    # Fast path: hash-based dedup using structural equality.
                    # After nf_y normalization, duplicates should have identical
                    # structure, so hash+== catches them without expensive dp calls.
                    tup_hash = hash(assign_buf)
                    if haskey(valid_hashes, tup_hash)
                        for idx in valid_hashes[tup_hash]
                            existing = valid[idx]
                            if existing == assign_buf
                                is_dup = true; break
                            end
                        end
                    end
                    # Only fall back to dp-based comparison if hash check didn't
                    # find a dup and there are few tuples (avoid O(n²) blowup)
                    if !is_dup && length(valid) <= 64
                        for existing in valid
                            same = true
                            for (k, v) in assign_buf
                                ev = existing[k]
                                if ev != v
                                    if v isa CQLTerm && ev isa CQLTerm && inst.dp(Equation(v, ev))
                                        continue
                                    end
                                    same = false; break
                                end
                            end
                            if same
                                is_dup = true; break
                            end
                        end
                    end
                end
                if !is_dup
                    new_tup = copy(assign_buf)
                    if !isempty(type_sorted_vars)
                        tup_h = hash(new_tup)
                        push!(get!(Vector{Int}, valid_hashes, tup_h), length(valid) + 1)
                    end
                    push!(valid, new_tup)
                end
            end
        end
        entity_tuples[tgt_en] = valid
    end

    gens = Dict{Symbol, Symbol}()
    tuple_to_gen = Dict{Tuple{Symbol, Int}, Symbol}()
    gen_to_tuple = Dict{Symbol, Tuple{Symbol, Dict{Symbol, Any}}}()

    for (tgt_en, tuples) in entity_tuples
        for (i, tup) in enumerate(tuples)
            g = Symbol("q_", tgt_en, "_", i)
            gens[g] = tgt_en
            tuple_to_gen[(tgt_en, i)] = g
            gen_to_tuple[g] = (tgt_en, tup)
        end
    end

    eqs = Set{Equation}()

    # Build hash indices for tuple lookup per target entity (avoids linear scan)
    tuple_hash_indices = Dict{Symbol, Dict{UInt, Vector{Int}}}()
    for (en, tuples) in entity_tuples
        idx = Dict{UInt, Vector{Int}}()
        for (i, tup) in enumerate(tuples)
            h = hash(tup)
            push!(get!(Vector{Int}, idx, h), i)
        end
        tuple_hash_indices[en] = idx
    end

    for (fk_name, var_mapping) in q.fks
        (fk_src_en, fk_tgt_en) = q.dst.fks[fk_name]
        src_tuples = entity_tuples[fk_src_en]
        tgt_tuples = entity_tuples[fk_tgt_en]
        tgt_hash_idx = tuple_hash_indices[fk_tgt_en]

        for (i, src_tup) in enumerate(src_tuples)
            tgt_assignment = Dict{Symbol, Any}()
            for (tgt_var, src_term) in var_mapping
                val = _eval_query_term_mixed(src_alg, src_tup, src_term)
                # Reduce type-side terms through typeside rewriter
                if val isa CQLTerm
                    val = _reduce_typeside(ts_rules, val)
                end
                tgt_assignment[tgt_var] = val
            end

            src_gen = tuple_to_gen[(fk_src_en, i)]
            tgt_idx = _find_tuple_index_hashed(tgt_tuples, tgt_assignment, tgt_hash_idx; dp=inst.dp)
            if tgt_idx !== nothing
                tgt_gen = tuple_to_gen[(fk_tgt_en, tgt_idx)]
                push!(eqs, Equation(CQLFk(fk_name, CQLGen(src_gen)), CQLGen(tgt_gen)))
            end
        end
    end

    for (att_name, att_term) in q.atts
        (att_src_en, _) = q.dst.atts[att_name]
        tuples = entity_tuples[att_src_en]

        for (i, tup) in enumerate(tuples)
            gen = tuple_to_gen[(att_src_en, i)]
            if att_term isa CQLAgg
                val = _eval_agg_term(src_alg, tup, att_term, ts_rules, inst.dp)
            else
                val = _reduce_typeside(ts_rules, _eval_query_term_type(src_alg, tup, att_term))
            end
            push!(eqs, Equation(CQLAtt(att_name, CQLGen(gen)), val))
        end
    end

    pres = Presentation(gens, Dict{Symbol,Symbol}(), eqs)
    (entity_tuples, tuple_to_gen, gen_to_tuple, pres)
end

"""
Evaluate a query on a transform: given Q: S -> T and transform h: I -> J
(both instances on S), produce a transform eval(Q,I) -> eval(Q,J).
"""
function eval_query_transform(q::CQLQuery, tr::CQLTransform, opts::CQLOptions)
    src_inst = eval_query_instance(q, tr.src, opts)
    dst_inst = eval_query_instance(q, tr.dst, opts)

    # Re-enumerate tuples for both to get mappings
    (src_tuples, src_t2g, src_g2t, _) = _eval_query_data(q, tr.src)
    (dst_tuples, dst_t2g, dst_g2t, _) = _eval_query_data(q, tr.dst)

    gens = Dict{Symbol, CQLTerm}()
    for (g, (en, src_assignment)) in src_g2t
        # Map each variable's element through the transform
        dst_assignment = Dict{Symbol, Any}()
        all_mapped = true
        for (v, x) in src_assignment
            # x is an element of tr.src's algebra; get its term representation
            x_term = repr_x(tr.src.algebra, x)
            # Apply transform substitution
            mapped_term = _apply_transform_subst(tr, x_term)
            # Evaluate in destination algebra
            mapped_elem = _eval_gen_term_in_algebra(tr.dst.algebra, mapped_term)
            if mapped_elem === nothing
                all_mapped = false; break
            end
            dst_assignment[v] = mapped_elem
        end

        if all_mapped
            tgt_tuples = dst_tuples[en]
            tgt_idx = _find_tuple_index(tgt_tuples, dst_assignment)
            if tgt_idx !== nothing
                tgt_gen = dst_t2g[(en, tgt_idx)]
                gens[g] = CQLGen(tgt_gen)
            else
                gens[g] = CQLGen(g)  # fallback
            end
        else
            gens[g] = CQLGen(g)  # fallback
        end
    end

    sks = Dict{Symbol, CQLTerm}()
    for (s, _) in src_inst.pres.sks
        sks[s] = CQLSk(s)
    end

    CQLTransform(src_inst, dst_inst, gens, sks)
end

"""Apply a transform's generator/skolem substitution to a term."""
function _apply_transform_subst(tr::CQLTransform, t::CQLTerm)::CQLTerm
    if t isa CQLGen
        haskey(tr.gens, t.gen) ? tr.gens[t.gen] : t
    elseif t isa CQLFk
        CQLFk(t.fk, _apply_transform_subst(tr, t.arg))
    elseif t isa CQLAtt
        CQLAtt(t.att, _apply_transform_subst(tr, t.arg))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_apply_transform_subst(tr, a) for a in t.args])
    elseif t isa CQLSk
        haskey(tr.sks, t.sk) ? tr.sks[t.sk] : t
    else
        t
    end
end

"""Evaluate a generator-level term (CQLGen/CQLFk) in an algebra to get a carrier element."""
function _eval_gen_term_in_algebra(alg::Algebra, t::CQLTerm)
    if t isa CQLGen
        haskey(alg.gen, t.gen) ? alg.gen[t.gen] : nothing
    elseif t isa CQLFk
        inner = _eval_gen_term_in_algebra(alg, t.arg)
        inner === nothing && return nothing
        eval_fk(alg, t.fk, inner)
    else
        nothing
    end
end

"""Try to evaluate a type-level term to a concrete Julia value for comparison.
Returns the evaluated value (String, Number, etc.) or nothing if unevaluable."""
function _try_eval_native(t::CQLTerm)::Union{String, Number, Nothing}
    if t isa CQLSk
        s = string(t.sk)
        # Try parsing as number
        n = tryparse(Float64, s)
        n !== nothing && return n
        # Return as string
        return s
    elseif t isa CQLSym
        if isempty(t.args)
            s = string(t.sym)
            n = tryparse(Float64, s)
            n !== nothing && return n
            return s
        end
        # Evaluate function application
        fname = string(t.sym)
        arg_vals = [_try_eval_native(a) for a in t.args]
        any(isnothing, arg_vals) && return nothing
        # Common string functions
        if fname == "toUpper" && length(arg_vals) == 1 && arg_vals[1] isa String
            return uppercase(arg_vals[1])
        elseif fname == "toLower" && length(arg_vals) == 1 && arg_vals[1] isa String
            return lowercase(arg_vals[1])
        elseif fname == "toString" && length(arg_vals) == 1
            return string(arg_vals[1])
        elseif fname == "length" && length(arg_vals) == 1 && arg_vals[1] isa String
            return Float64(Base.length(arg_vals[1]))
        elseif fname == "concat" && length(arg_vals) == 2 && all(v -> v isa String, arg_vals)
            return string(arg_vals[1], arg_vals[2])
        # Common numeric functions
        elseif fname == "plus" && length(arg_vals) == 2 && all(v -> v isa Number, arg_vals)
            return arg_vals[1] + arg_vals[2]
        elseif fname == "minus" && length(arg_vals) == 2 && all(v -> v isa Number, arg_vals)
            return arg_vals[1] - arg_vals[2]
        elseif fname == "times" && length(arg_vals) == 2 && all(v -> v isa Number, arg_vals)
            return arg_vals[1] * arg_vals[2]
        elseif fname == "neg" && length(arg_vals) == 1 && arg_vals[1] isa Number
            return -arg_vals[1]
        end
        return nothing
    end
    nothing
end

"""Check if a term is type-level (contains attributes or type constants at the top)."""
function _is_type_level(t::CQLTerm)::Bool
    t isa CQLAtt && return true
    t isa CQLSym && return true
    t isa CQLSk && return true
    return false
end

"""Evaluate an entity-side query term given a variable assignment."""
function _eval_query_term_entity(alg::Algebra, assignment::Dict{Symbol, Any}, t::CQLTerm)
    if t isa CQLVar
        assignment[t.name]
    elseif t isa CQLFk
        inner = _eval_query_term_entity(alg, assignment, t.arg)
        eval_fk(alg, t.fk, inner)
    elseif t isa CQLGen
        eval_gen(alg, t.gen)
    else
        error("Cannot evaluate entity-side query term: $t")
    end
end

"""Evaluate a query term that may be entity-sorted or type-sorted.
For entity-sorted variables/terms, returns a carrier element.
For type-sorted variables, returns the type carrier element (a CQLTerm) directly."""
function _eval_query_term_mixed(alg::Algebra, assignment::Dict{Symbol, Any}, t::CQLTerm)
    if t isa CQLVar
        return assignment[t.name]
    elseif t isa CQLFk
        inner = _eval_query_term_mixed(alg, assignment, t.arg)
        return eval_fk(alg, t.fk, inner)
    elseif t isa CQLGen
        return eval_gen(alg, t.gen)
    elseif t isa CQLAtt
        inner = _eval_query_term_entity(alg, assignment, t.arg)
        return eval_att(alg, t.att, inner)
    elseif t isa CQLSym
        if isempty(t.args) && !haskey(alg.schema.typeside.syms, t.sym)
            return alg.nf_y(Left(t.sym))
        end
        return CQLSym(t.sym, CQLTerm[_eval_query_term_type(alg, assignment, a) for a in t.args])
    elseif t isa CQLSk
        return alg.nf_y(Left(t.sk))
    else
        error("Cannot evaluate mixed query term: $t")
    end
end

"""Evaluate a type-side query term given a variable assignment."""
function _eval_query_term_type(alg::Algebra, assignment::Dict{Symbol, Any}, t::CQLTerm)::CQLTerm
    if t isa CQLAtt
        inner = _eval_query_term_entity(alg, assignment, t.arg)
        eval_att(alg, t.att, inner)
    elseif t isa CQLSym
        if isempty(t.args) && !haskey(alg.schema.typeside.syms, t.sym)
            # Bare constant not declared in typeside (e.g. SQL literal "1"):
            # query parser creates CQLSym(:1, []) but instances store as CQLSk(:1).
            # Normalize via nf_y to match instance representation.
            return alg.nf_y(Left(t.sym))
        end
        CQLSym(t.sym, CQLTerm[_eval_query_term_type(alg, assignment, a) for a in t.args])
    elseif t isa CQLVar
        val = assignment[t.name]
        # If value is already a CQLTerm (type-sorted variable), return directly
        val isa CQLTerm && return val
        # If value is a type carrier element (TalgGen), use repr_y
        if haskey(alg.repr_y, val)
            return alg.repr_y[val]
        end
        repr_x(alg, val)
    else
        error("Cannot evaluate type-side query term: $t")
    end
end

"""Find the index of a tuple matching the given assignment.
Uses structural equality, with optional decision procedure for CQLTerm comparisons."""
function _find_tuple_index(tuples::Vector{Dict{Symbol, Any}}, target::Dict{Symbol, Any};
                            dp::Union{Function,Nothing}=nothing)::Union{Int, Nothing}
    for (i, tup) in enumerate(tuples)
        matched = true
        for (k, v) in target
            tup_v = tup[k]
            if tup_v == v
                continue
            elseif dp !== nothing && v isa CQLTerm && tup_v isa CQLTerm
                if dp(Equation(v, tup_v))
                    continue
                end
            end
            matched = false
            break
        end
        if matched
            return i
        end
    end
    nothing
end

"""Hash-accelerated tuple index lookup. Tries exact hash match first, falls back to dp."""
function _find_tuple_index_hashed(tuples::Vector{Dict{Symbol, Any}}, target::Dict{Symbol, Any},
                                   hash_idx::Dict{UInt, Vector{Int}};
                                   dp::Union{Function,Nothing}=nothing)::Union{Int, Nothing}
    h = hash(target)
    candidates = get(hash_idx, h, nothing)
    if candidates !== nothing
        for i in candidates
            if tuples[i] == target
                return i
            end
        end
    end
    # Fall back to dp-based comparison if exact match not found
    dp === nothing && return nothing
    _find_tuple_index(tuples, target; dp=dp)
end

# ============================================================================
# Raw query evaluation
# ============================================================================

"""Evaluate a raw query into a CQLQuery."""
function eval_query_raw(src::CQLSchema, dst::CQLSchema, raw::QueryExpRaw)
    fk_names = collect(keys(src.fks))
    att_names = collect(keys(src.atts))

    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}()
    fks = Dict{Symbol, Dict{Symbol, CQLTerm}}()
    atts = Dict{Symbol, CQLTerm}()

    for (en_name, en_block) in raw.ens
        (from_bindings, where_raw, att_raw, fk_raw) = en_block

        # Build context
        ctx = Dict{Symbol,Symbol}()
        for (v, e) in from_bindings
            ctx[Symbol(v)] = Symbol(e)
        end

        var_names = [Symbol(v) for (v, _) in from_bindings]

        # Build where-clause equations
        where_eqs = Set{Equation}()
        for (lhs_raw, rhs_raw) in where_raw
            lhs = _trans_query_term(var_names, fk_names, att_names, src.typeside.syms, lhs_raw;
                                     src_schema=src, from_ctx=ctx)
            rhs = _trans_query_term(var_names, fk_names, att_names, src.typeside.syms, rhs_raw;
                                     src_schema=src, from_ctx=ctx)
            push!(where_eqs, Equation(lhs, rhs))
        end

        # For simple queries, use the actual target entity name
        actual_en_name = if en_name == "__simple__" && length(dst.ens) == 1
            first(dst.ens)
        else
            Symbol(en_name)
        end

        ens[actual_en_name] = (ctx, where_eqs)

        # Build attribute mappings — resolve against target schema with entity context
        for (att_name, att_raw_term) in att_raw
            resolved_att = _resolve_query_att(dst, Symbol(att_name), actual_en_name)
            if att_raw_term.head == "__agg__"
                atts[resolved_att] = _build_agg_term(var_names, fk_names, att_names,
                    src.typeside.syms, att_raw_term; src_schema=src, from_ctx=ctx)
            else
                atts[resolved_att] = _trans_query_term(var_names, fk_names, att_names,
                    src.typeside.syms, att_raw_term; src_schema=src, from_ctx=ctx)
            end
        end

        # Build FK mappings — resolve against target schema with entity context
        for (fk_name, var_mappings) in fk_raw
            fk_dict = Dict{Symbol, CQLTerm}()
            for (var_name, term_raw) in var_mappings
                fk_dict[Symbol(var_name)] = _trans_query_term(var_names, fk_names, att_names, src.typeside.syms, term_raw;
                                                             src_schema=src, from_ctx=ctx)
            end
            resolved_fk = _resolve_query_fk(dst, Symbol(fk_name), actual_en_name)
            fks[resolved_fk] = fk_dict
        end
    end

    q = CQLQuery(src, dst, ens, fks, atts)
    _typecheck_query(q)
    q
end

"""Resolve a query attribute name against the target schema, using entity context for disambiguation."""
function _resolve_query_att(sch::CQLSchema, name::Symbol, entity::Symbol)::Symbol
    haskey(sch.atts, name) && return name
    # Try entity-qualified name
    if has_att(sch, name)
        candidates = att_candidates(sch, name)
        for c in candidates
            haskey(sch.atts, c) || continue
            (att_src, _) = sch.atts[c]
            if att_src == entity
                return c
            end
        end
        length(candidates) == 1 && return candidates[1]
    end
    qualified = Symbol(entity, :__, name)
    haskey(sch.atts, qualified) && return qualified
    name
end

"""Resolve a query FK name against the target schema, using entity context for disambiguation."""
function _resolve_query_fk(sch::CQLSchema, name::Symbol, entity::Symbol)::Symbol
    haskey(sch.fks, name) && return name
    if has_fk(sch, name)
        candidates = fk_candidates(sch, name)
        for c in candidates
            haskey(sch.fks, c) || continue
            (fk_src, _) = sch.fks[c]
            if fk_src == entity
                return c
            end
        end
        length(candidates) == 1 && return candidates[1]
    end
    qualified = Symbol(entity, :__, name)
    haskey(sch.fks, qualified) && return qualified
    name
end

"""Type-check a query: verify attribute terms produce the correct target types."""
function _typecheck_query(q::CQLQuery)
    for (att_name, att_term) in q.atts
        (att_src_en, att_tgt_ty) = q.dst.atts[att_name]
        (ctx, _) = q.ens[att_src_en]
        actual_ty = _infer_type_term(q.src, ctx, att_term)
        if actual_ty !== nothing && actual_ty != att_tgt_ty
            # In the sql typeside, types like String/Text/Varchar/Smallint etc. can be
            # mixed in queries (Java CQL maps them all through java_type coercions).
            if length(q.src.typeside.tys) > 5
                continue  # lenient for multi-type typesides like sql
            end
            throw(CQLException(
                "Type mismatch in query attribute $att_name: " *
                "expected $att_tgt_ty, got $actual_ty"))
        end
    end
end

"""Infer the type (entity or typeside type) of a query term. Returns a Symbol or nothing."""
function _infer_type_term(src::CQLSchema, ctx::Dict{Symbol,Symbol}, t::CQLTerm)::Union{Symbol, Nothing}
    if t isa CQLVar
        get(ctx, t.name, nothing)
    elseif t isa CQLFk
        inner_en = _infer_entity_term(src, ctx, t.arg)
        inner_en === nothing && return nothing
        haskey(src.fks, t.fk) || return nothing
        (fk_src, fk_tgt) = src.fks[t.fk]
        fk_src == inner_en || return nothing
        fk_tgt
    elseif t isa CQLAtt
        inner_en = _infer_entity_term(src, ctx, t.arg)
        inner_en === nothing && return nothing
        haskey(src.atts, t.att) || return nothing
        (att_src, att_tgt) = src.atts[t.att]
        att_src == inner_en || return nothing
        att_tgt
    elseif t isa CQLSym
        haskey(src.typeside.syms, t.sym) || return nothing
        (_, ret_ty) = src.typeside.syms[t.sym]
        ret_ty
    else
        nothing
    end
end

"""Infer the entity type of an entity-side query term."""
function _infer_entity_term(src::CQLSchema, ctx::Dict{Symbol,Symbol}, t::CQLTerm)::Union{Symbol, Nothing}
    if t isa CQLVar
        get(ctx, t.name, nothing)
    elseif t isa CQLFk
        inner_en = _infer_entity_term(src, ctx, t.arg)
        inner_en === nothing && return nothing
        haskey(src.fks, t.fk) || return nothing
        (fk_src, fk_tgt) = src.fks[t.fk]
        fk_src == inner_en || return nothing
        fk_tgt
    else
        nothing
    end
end

"""Translate a raw term in a query context to a CQLTerm.
Accepts an optional source schema for resolving qualified FK/att names."""
function _trans_query_term(var_names, fk_names, att_names, syms, raw::RawTerm;
                           src_schema::Union{CQLSchema,Nothing}=nothing,
                           from_ctx::Union{Dict{Symbol,Symbol},Nothing}=nothing)::CQLTerm
    s = Symbol(raw.head)

    # Handle @Type annotations: @TypeName(inner_term)
    if startswith(raw.head, "@") && length(raw.args) == 1
        return _trans_query_term(var_names, fk_names, att_names, syms, raw.args[1];
                                  src_schema=src_schema, from_ctx=from_ctx)
    end

    if isempty(raw.args) && s in var_names
        return CQLVar(s)
    elseif length(raw.args) == 1 && s in fk_names
        return CQLFk(s, _trans_query_term(var_names, fk_names, att_names, syms, raw.args[1];
                                           src_schema=src_schema, from_ctx=from_ctx))
    elseif length(raw.args) == 1 && s in att_names
        return CQLAtt(s, _trans_query_term(var_names, fk_names, att_names, syms, raw.args[1];
                                            src_schema=src_schema, from_ctx=from_ctx))
    elseif length(raw.args) == 1 && src_schema !== nothing && has_fk(src_schema, s)
        # Qualified FK resolution using entity context
        inner = _trans_query_term(var_names, fk_names, att_names, syms, raw.args[1];
                                   src_schema=src_schema, from_ctx=from_ctx)
        inner_en = _infer_query_term_entity(src_schema, from_ctx, inner)
        if inner_en !== nothing
            qname = resolve_fk(src_schema, s, inner_en)
            return CQLFk(qname, inner)
        end
        candidates = fk_candidates(src_schema, s)
        !isempty(candidates) && return CQLFk(candidates[1], inner)
        throw(CQLException("Cannot type query term: $(raw.head)"))
    elseif length(raw.args) == 1 && src_schema !== nothing && has_att(src_schema, s)
        inner = _trans_query_term(var_names, fk_names, att_names, syms, raw.args[1];
                                   src_schema=src_schema, from_ctx=from_ctx)
        inner_en = _infer_query_term_entity(src_schema, from_ctx, inner)
        if inner_en !== nothing
            qname = resolve_att(src_schema, s, inner_en)
            return CQLAtt(qname, inner)
        end
        candidates = att_candidates(src_schema, s)
        !isempty(candidates) && return CQLAtt(candidates[1], inner)
        throw(CQLException("Cannot type query term: $(raw.head)"))
    elseif haskey(syms, s)
        return CQLSym(s, CQLTerm[_trans_query_term(var_names, fk_names, att_names, syms, a;
                                                     src_schema=src_schema, from_ctx=from_ctx) for a in raw.args])
    elseif isempty(raw.args)
        # Bare identifier not in from-clause: treat as typeside constant
        return CQLSym(s, CQLTerm[])
    else
        throw(CQLException("Cannot type query term: $(raw.head)"))
    end
end

"""Infer the entity of a query term from the from-clause context."""
function _infer_query_term_entity(src::CQLSchema, from_ctx::Union{Dict{Symbol,Symbol},Nothing}, t::CQLTerm)::Union{Symbol, Nothing}
    if t isa CQLVar
        from_ctx !== nothing && return get(from_ctx, t.name, nothing)
        return nothing
    elseif t isa CQLFk
        haskey(src.fks, t.fk) && return src.fks[t.fk][2]
        return nothing
    else
        return nothing
    end
end

# ============================================================================
# Quotient query: quotient_query I { entity blocks... }
# ============================================================================

"""
Evaluate a quotient_query: identify elements in an instance based on query conditions.

For each entity block `entity E -> {from a:E b:E where condition}`, enumerate
all pairs (a, b) satisfying the where-clause and add equations to merge them.
"""
function eval_quotient_query(inst::CQLInstance, raw_query, opts::CQLOptions)
    sch = inst.schema
    alg = inst.algebra

    new_eqs = Set{Equation}()
    ts_rules = _build_typeside_rules(sch.typeside)
    fk_names = collect(keys(sch.fks))
    att_names = collect(keys(sch.atts))

    if raw_query !== nothing
        for (en_name, block) in raw_query
            en = Symbol(en_name)
            (from_bindings, where_raw, _, _) = block

            # Build context
            ctx = Dict{Symbol,Symbol}()
            var_names = Symbol[]
            for (v, e) in from_bindings
                ctx[Symbol(v)] = Symbol(e)
                push!(var_names, Symbol(v))
            end

            # Resolve where-clause raw terms to CQLTerms
            where_eqs = Equation[]
            for (lhs_raw, rhs_raw) in where_raw
                lhs = _trans_query_term(var_names, fk_names, att_names,
                    sch.typeside.syms, lhs_raw; src_schema=sch, from_ctx=ctx)
                rhs = _trans_query_term(var_names, fk_names, att_names,
                    sch.typeside.syms, rhs_raw; src_schema=sch, from_ctx=ctx)
                push!(where_eqs, Equation(lhs, rhs))
            end

            # Enumerate all variable assignments and find satisfying pairs
            src_entities = [ctx[v] for v in var_names]
            src_carriers = [collect(carrier(alg, e)) for e in src_entities]
            isempty(src_carriers) && continue

            for combo in Iterators.product(src_carriers...)
                assignment = Dict{Symbol, Any}(var_names[i] => combo[i] for i in eachindex(var_names))

                all_ok = true
                for eq in where_eqs
                    if _is_type_level(eq.lhs) || _is_type_level(eq.rhs)
                        lval = _reduce_typeside(ts_rules, _eval_query_term_type(alg, assignment, eq.lhs))
                        rval = _reduce_typeside(ts_rules, _eval_query_term_type(alg, assignment, eq.rhs))
                        if lval != rval && !inst.dp(Equation(lval, rval))
                            # Try native evaluation of external functions
                            lv = _try_eval_native(lval)
                            rv = _try_eval_native(rval)
                            if lv === nothing || rv === nothing || lv != rv
                                all_ok = false; break
                            end
                        end
                    else
                        lval = _eval_query_term_entity(alg, assignment, eq.lhs)
                        rval = _eval_query_term_entity(alg, assignment, eq.rhs)
                        if lval != rval
                            all_ok = false; break
                        end
                    end
                end

                if all_ok && length(var_names) >= 2
                    # Identify the first two variables' elements
                    x1 = assignment[var_names[1]]
                    x2 = assignment[var_names[2]]
                    if x1 != x2
                        t1 = repr_x(alg, x1)
                        t2 = repr_x(alg, x2)
                        if t1 != t2
                            push!(new_eqs, Equation(t1, t2))
                        end
                    end
                end
            end
        end
    end

    if isempty(new_eqs)
        return inst  # No merging needed
    end

    # Add identification equations to presentation and rebuild
    merged_eqs = union(inst.pres.eqs, new_eqs)
    new_pres = Presentation(inst.pres.gens, inst.pres.sks, merged_eqs, copy(inst.pres.gen_order))

    col = presentation_to_collage(sch, new_pres)
    prover = create_prover(col, opts)
    dp_fn = eq -> prover(Ctx(), eq)

    initial_instance(new_pres, dp_fn, sch)
end

# ============================================================================
# Aggregation support
# ============================================================================

"""Build a CQLAgg term from a structured __agg__ RawTerm."""
function _build_agg_term(outer_var_names, fk_names, att_names, syms, raw::RawTerm;
                          src_schema=nothing, from_ctx=nothing)::CQLAgg
    # Decode from-clause: __from__ with "var:entity" children
    from_raw = raw.args[1]
    agg_from_ctx = Dict{Symbol, Symbol}()
    for part in from_raw.args
        pieces = split(part.head, ":")
        agg_from_ctx[Symbol(pieces[1])] = Symbol(pieces[2])
    end

    # Combined variable names (outer + inner) for resolving terms
    all_var_names = union(Set(outer_var_names), Set(keys(agg_from_ctx)))
    all_var_list = collect(all_var_names)
    combined_ctx = from_ctx !== nothing ? merge(from_ctx, agg_from_ctx) : agg_from_ctx

    # Decode where-clause: __where__ with alternating lhs/rhs RawTerms
    where_raw = raw.args[2]
    agg_where = Equation[]
    for i in 1:2:length(where_raw.args)
        lhs = _trans_query_term(all_var_list, fk_names, att_names, syms, where_raw.args[i];
                                src_schema=src_schema, from_ctx=combined_ctx)
        rhs = _trans_query_term(all_var_list, fk_names, att_names, syms, where_raw.args[i+1];
                                src_schema=src_schema, from_ctx=combined_ctx)
        push!(agg_where, Equation(lhs, rhs))
    end

    # Decode return term (in combined context)
    ret = _trans_query_term(all_var_list, fk_names, att_names, syms, raw.args[3];
                             src_schema=src_schema, from_ctx=combined_ctx)

    # Decode zero term (outer context only — typically a constant)
    zero = _trans_query_term(collect(outer_var_names), fk_names, att_names, syms, raw.args[4];
                              src_schema=src_schema, from_ctx=from_ctx)

    # Decode lambda args
    lambda_raw = raw.args[5]
    arg1 = Symbol(lambda_raw.args[1].head)
    arg2 = Symbol(lambda_raw.args[2].head)

    # Decode body (lambda args are the variables in scope)
    body_var_list = [arg1, arg2]
    body = _trans_query_term(body_var_list, fk_names, att_names, syms, raw.args[6];
                              src_schema=src_schema, from_ctx=from_ctx)

    CQLAgg(agg_from_ctx, agg_where, ret, zero, (arg1, arg2), body)
end

"""Evaluate an aggregation term given an outer variable assignment.

Enumerates all inner from-variable combinations satisfying the where-clause,
evaluates the return term for each, and folds using the aggregate function."""
function _eval_agg_term(alg::Algebra, outer_assignment::Dict{Symbol, Any},
                        agg::CQLAgg, ts_rules, dp_fn)::CQLTerm
    inner_vars = collect(keys(agg.from_ctx))
    inner_entities = [agg.from_ctx[v] for v in inner_vars]
    inner_carriers = Any[]
    for en in inner_entities
        if haskey(alg.en, en)
            push!(inner_carriers, collect(carrier(alg, en)))
        else
            push!(inner_carriers, Any[])
        end
    end

    result = agg.zero

    if any(isempty, inner_carriers)
        return _reduce_typeside(ts_rules, result)
    end

    for combo in Iterators.product(inner_carriers...)
        # Build combined assignment: outer + inner
        assignment = copy(outer_assignment)
        for (j, v) in enumerate(inner_vars)
            assignment[v] = combo[j]
        end

        # Check where-clause
        all_ok = true
        for eq in agg.where_eqs
            if _is_type_level(eq.lhs) || _is_type_level(eq.rhs)
                lval = _reduce_typeside(ts_rules, _eval_query_term_type(alg, assignment, eq.lhs))
                rval = _reduce_typeside(ts_rules, _eval_query_term_type(alg, assignment, eq.rhs))
                if lval != rval && !dp_fn(Equation(lval, rval))
                    all_ok = false; break
                end
            else
                lval = _eval_query_term_entity(alg, assignment, eq.lhs)
                rval = _eval_query_term_entity(alg, assignment, eq.rhs)
                if lval != rval
                    all_ok = false; break
                end
            end
        end

        if all_ok
            # Evaluate return term
            ret_val = _reduce_typeside(ts_rules, _eval_query_term_type(alg, assignment, agg.ret_term))
            # Apply lambda: result = body[arg1 := result, arg2 := ret_val]
            result = _reduce_typeside(ts_rules,
                _subst_agg_lambda(agg.lambda_body, agg.lambda_args[1], result, agg.lambda_args[2], ret_val))
        end
    end

    _reduce_typeside(ts_rules, result)
end

"""Substitute lambda argument variables in an aggregation body."""
function _subst_agg_lambda(t::CQLTerm, arg1::Symbol, val1::CQLTerm,
                            arg2::Symbol, val2::CQLTerm)::CQLTerm
    if t isa CQLVar
        t.name == arg1 && return val1
        t.name == arg2 && return val2
        return t
    elseif t isa CQLSym
        return CQLSym(t.sym, CQLTerm[_subst_agg_lambda(a, arg1, val1, arg2, val2) for a in t.args])
    elseif t isa CQLFk
        return CQLFk(t.fk, _subst_agg_lambda(t.arg, arg1, val1, arg2, val2))
    elseif t isa CQLAtt
        return CQLAtt(t.att, _subst_agg_lambda(t.arg, arg1, val1, arg2, val2))
    else
        return t
    end
end
