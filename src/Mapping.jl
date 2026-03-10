"""
Mappings: morphisms between schemas.

A mapping F: S -> T consists of:
- Entity mapping: en_S -> en_T
- FK translation: fk_S -> path in T
- Attribute translation: att_S -> term in T
"""

"""A CQL mapping between schemas."""
struct CQLMapping
    src::CQLSchema
    dst::CQLSchema
    ens::Dict{Symbol, Symbol}       # src entity -> dst entity
    fks::Dict{Symbol, CQLTerm}      # src fk -> dst path term (Var/Fk chain)
    atts::Dict{Symbol, CQLTerm}     # src att -> dst type-side term
end

function Base.:(==)(a::CQLMapping, b::CQLMapping)
    a.src == b.src && a.dst == b.dst && a.ens == b.ens && a.fks == b.fks && a.atts == b.atts
end

function Base.show(io::IO, m::CQLMapping)
    println(io, "mapping {")
    println(io, "  entities")
    for (s, t) in m.ens
        println(io, "    ", s, " -> ", t)
    end
    println(io, "  foreign_keys")
    for (k, v) in m.fks
        println(io, "    ", k, " -> ", v)
    end
    println(io, "  attributes")
    for (k, v) in m.atts
        println(io, "    ", k, " -> ", v)
    end
    println(io, "}")
end

"""Convert a mapping to a morphism for type-checking."""
function mapping_to_morphism(m::CQLMapping)::Morphism
    Morphism(
        schema_to_collage(m.src),
        schema_to_collage(m.dst),
        m.ens, m.fks, m.atts,
        Dict{Symbol,CQLTerm}(),  # no gen mappings
        Dict{Symbol,CQLTerm}(),  # no sk mappings
    )
end

"""Typecheck a mapping."""
function typecheck_mapping(m::CQLMapping)
    typecheck_morphism(mapping_to_morphism(m))
end

"""Validate that a mapping preserves equations."""
function validate_mapping(m::CQLMapping)
    mor = mapping_to_morphism(m)

    for (en, eq) in m.src.path_eqs
        l = translate_entity_term(mor, eq.lhs)
        r = translate_entity_term(mor, eq.rhs)
        en2 = m.ens[en]
        m.dst.eq(en2, Equation(l, r)) || throw(CQLException(
            "$eq translates to $(Equation(l, r)) which is not provable in target"))
    end

    for (en, eq) in m.src.obs_eqs
        l = translate_term(mor, eq.lhs)
        r = translate_term(mor, eq.rhs)
        en2 = m.ens[en]
        m.dst.eq(en2, Equation(l, r)) || throw(CQLException(
            "$eq translates to $(Equation(l, r)) which is not provable in target"))
    end
end

"""Compose two mappings: F: A -> B, G: B -> C => G . F: A -> C."""
function compose_mapping(f::CQLMapping, g::CQLMapping)
    f.dst == g.src || throw(CQLException("Source and target schemas do not match"))
    g_mor = mapping_to_morphism(g)

    new_ens = Dict(k => g.ens[v] for (k, v) in f.ens)
    new_fks = Dict(k => translate_entity_term(g_mor, v) for (k, v) in f.fks)
    new_atts = Dict(k => translate_term(g_mor, v) for (k, v) in f.atts)

    CQLMapping(f.src, g.dst, new_ens, new_fks, new_atts)
end

"""Create an identity mapping on a schema."""
function identity_mapping(sch::CQLSchema)
    ens = Dict(en => en for en in sch.ens)
    fks = Dict(fk => CQLFk(fk, CQLVar(Symbol("_unit"))) for fk in keys(sch.fks))
    atts = Dict(att => CQLAtt(att, CQLVar(Symbol("_unit"))) for att in keys(sch.atts))
    CQLMapping(sch, sch, ens, fks, atts)
end

# ============================================================================
# Raw mapping evaluation
# ============================================================================

"""Raw mapping data from parsing."""
struct MappingExpRaw
    src_ref::Any  # SchemaExp
    dst_ref::Any  # SchemaExp
    ens::Vector{Tuple{String, String}}
    fks::Vector{Tuple{String, Vector{String}}}
    atts::Vector{Tuple{String, Any}}  # String -> Either (var, entity_hint, RawTerm) or [String] path
    options::Vector{Tuple{String, String}}
    imports::Vector{Any}  # MappingExp references
end

"""Evaluate a raw mapping."""
function eval_mapping_raw(src::CQLSchema, dst::CQLSchema, raw::MappingExpRaw,
                          imports::Vector{CQLMapping}=CQLMapping[])
    ens = Dict{Symbol,Symbol}()
    for (s, t) in raw.ens
        ens[Symbol(s)] = Symbol(t)
    end
    for imp in imports
        merge!(ens, imp.ens)
    end

    dst_ens = collect(dst.ens)
    dst_fk_names = collect(keys(dst.fks))

    fks = Dict{Symbol,CQLTerm}()
    for (fk_name, path) in raw.fks
        fk_sym = Symbol(fk_name)
        # Resolve the source FK name (might be qualified)
        resolved_fk = _resolve_src_fk(src, fk_sym)
        if isempty(path)
            # Identity mapping: FK maps to identity path (CQLVar(:_unit))
            fks[resolved_fk] = CQLVar(Symbol("_unit"))
        else
            fks[resolved_fk] = _infer_path_ext(dst, dst_ens, dst_fk_names, reverse(path))
        end
    end
    for imp in imports
        merge!(fks, imp.fks)
    end

    atts = Dict{Symbol,CQLTerm}()
    for (att_name, raw_val) in raw.atts
        s = Symbol(att_name)
        # Extract entity context and actual value
        # New format: raw_val = (src_entity_name, actual_val)
        # Old format: raw_val = Vector{String} or (var, hint, term)
        entity_hint = nothing
        val = raw_val
        if raw_val isa Tuple && length(raw_val) == 2 && raw_val[1] isa String
            entity_hint = Symbol(raw_val[1])
            val = raw_val[2]
        end
        # Resolve the source att name with entity context
        resolved_att = _resolve_src_att(src, s, entity_hint)
        if val isa Vector{String}
            atts[resolved_att] = _infer_path_with_atts_ext(dst, dst_ens, dst_fk_names, collect(keys(dst.atts)), dst.typeside.syms, reverse(val))
        elseif val isa Tuple
            (var, _, term) = val
            atts[resolved_att] = _infer_mapping_term_ext(dst, var, dst_fk_names, collect(keys(dst.atts)), dst.typeside.syms, term)
        else
            throw(CQLException("Bad attribute mapping for $att_name"))
        end
    end
    for imp in imports
        merge!(atts, imp.atts)
    end

    CQLMapping(src, dst, ens, fks, atts)
end

"""Resolve a source FK name, handling qualified names."""
function _resolve_src_fk(src::CQLSchema, name::Symbol)::Symbol
    haskey(src.fks, name) && return name
    # Check if it matches a qualified name
    if has_fk(src, name)
        candidates = fk_candidates(src, name)
        length(candidates) == 1 && return candidates[1]
        # Multiple candidates — can't resolve without more context
        # Return as-is; validation will catch errors
    end
    name
end

"""Resolve a source att name, handling qualified names."""
function _resolve_src_att(src::CQLSchema, name::Symbol, entity_hint::Union{Symbol,Nothing}=nothing)::Symbol
    haskey(src.atts, name) && return name
    if has_att(src, name)
        candidates = att_candidates(src, name)
        length(candidates) == 1 && return candidates[1]
        # Multiple candidates: use entity_hint to disambiguate
        if entity_hint !== nothing
            for c in candidates
                haskey(src.atts, c) || continue
                (att_src, _) = src.atts[c]
                if att_src == entity_hint
                    return c
                end
            end
            # Try qualified name directly
            qualified = Symbol(entity_hint, :__, name)
            haskey(src.atts, qualified) && return qualified
        end
    end
    # Try qualified name directly with entity_hint
    if entity_hint !== nothing
        qualified = Symbol(entity_hint, :__, name)
        haskey(src.atts, qualified) && return qualified
    end
    name
end

"""Infer path with qualified FK support in target schema."""
function _infer_path_ext(dst, ens, fk_names, path)::CQLTerm
    if isempty(path)
        return CQLVar(Symbol("_unit"))
    end
    s = Symbol(path[1])
    rest = path[2:end]
    if s in ens
        return _infer_path_ext(dst, ens, fk_names, rest)
    elseif s in fk_names
        return CQLFk(s, _infer_path_ext(dst, ens, fk_names, rest))
    elseif has_fk(dst, s)
        inner = _infer_path_ext(dst, ens, fk_names, rest)
        candidates = fk_candidates(dst, s)
        !isempty(candidates) && return CQLFk(candidates[1], inner)
        throw(CQLException("Not a target fk or entity: $s"))
    else
        throw(CQLException("Not a target fk or entity: $s"))
    end
end

function _infer_path_with_atts_ext(dst, ens, fk_names, att_names, syms, path)::CQLTerm
    if isempty(path)
        return CQLVar(Symbol("_unit"))
    end
    s = Symbol(path[1])
    rest = path[2:end]
    if s in ens
        return _infer_path_with_atts_ext(dst, ens, fk_names, att_names, syms, rest)
    elseif s in att_names
        return CQLAtt(s, _infer_path_ext(dst, ens, fk_names, rest))
    elseif has_att(dst, s)
        candidates = att_candidates(dst, s)
        !isempty(candidates) && return CQLAtt(candidates[1], _infer_path_ext(dst, ens, fk_names, rest))
        throw(CQLException("Not a target symbol: $s"))
    elseif s in fk_names
        return CQLFk(s, _infer_path_with_atts_ext(dst, ens, fk_names, att_names, syms, rest))
    elseif has_fk(dst, s)
        inner = _infer_path_with_atts_ext(dst, ens, fk_names, att_names, syms, rest)
        candidates = fk_candidates(dst, s)
        !isempty(candidates) && return CQLFk(candidates[1], inner)
        throw(CQLException("Not a target symbol: $s"))
    elseif haskey(syms, s)
        # Typeside function: wrap the rest of the path as an argument
        inner = _infer_path_with_atts_ext(dst, ens, fk_names, att_names, syms, rest)
        return CQLSym(s, CQLTerm[inner])
    else
        throw(CQLException("Not a target symbol: $s"))
    end
end

function _infer_mapping_term_ext(dst, var, fk_names, att_names, syms, raw::RawTerm)::CQLTerm
    s = Symbol(raw.head)
    if isempty(raw.args) && raw.head == var
        return CQLVar(Symbol("_unit"))
    elseif length(raw.args) == 1 && s in fk_names
        return CQLFk(s, _infer_mapping_term_ext(dst, var, fk_names, att_names, syms, raw.args[1]))
    elseif length(raw.args) == 1 && s in att_names
        return CQLAtt(s, _infer_mapping_term_ext(dst, var, fk_names, att_names, syms, raw.args[1]))
    elseif length(raw.args) == 1 && has_fk(dst, s)
        candidates = fk_candidates(dst, s)
        !isempty(candidates) && return CQLFk(candidates[1], _infer_mapping_term_ext(dst, var, fk_names, att_names, syms, raw.args[1]))
        throw(CQLException("Cannot type mapping term: $(raw.head)"))
    elseif length(raw.args) == 1 && has_att(dst, s)
        candidates = att_candidates(dst, s)
        !isempty(candidates) && return CQLAtt(candidates[1], _infer_mapping_term_ext(dst, var, fk_names, att_names, syms, raw.args[1]))
        throw(CQLException("Cannot type mapping term: $(raw.head)"))
    elseif haskey(syms, s)
        return CQLSym(s, CQLTerm[_infer_mapping_term_ext(dst, var, fk_names, att_names, syms, a) for a in raw.args])
    else
        throw(CQLException("Cannot type mapping term: $(raw.head)"))
    end
end

function _infer_path(ens, fk_names, path)::CQLTerm
    if isempty(path)
        return CQLVar(Symbol("_unit"))
    end
    s = Symbol(path[1])
    rest = path[2:end]
    if s in ens
        return _infer_path(ens, fk_names, rest)
    elseif s in fk_names
        return CQLFk(s, _infer_path(ens, fk_names, rest))
    else
        throw(CQLException("Not a target fk or entity: $s"))
    end
end

function _infer_path_with_atts(ens, fk_names, att_names, path)::CQLTerm
    if isempty(path)
        return CQLVar(Symbol("_unit"))
    end
    s = Symbol(path[1])
    rest = path[2:end]
    if s in ens
        return _infer_path_with_atts(ens, fk_names, att_names, rest)
    elseif s in att_names
        return CQLAtt(s, _infer_path(ens, fk_names, rest))
    elseif s in fk_names
        return CQLFk(s, _infer_path_with_atts(ens, fk_names, att_names, rest))
    else
        throw(CQLException("Not a target symbol: $s"))
    end
end

function _infer_mapping_term(var, fk_names, att_names, syms, raw::RawTerm)::CQLTerm
    s = Symbol(raw.head)
    if isempty(raw.args) && raw.head == var
        return CQLVar(Symbol("_unit"))
    elseif length(raw.args) == 1 && s in fk_names
        return CQLFk(s, _infer_mapping_term(var, fk_names, att_names, syms, raw.args[1]))
    elseif length(raw.args) == 1 && s in att_names
        return CQLAtt(s, _infer_mapping_term(var, fk_names, att_names, syms, raw.args[1]))
    elseif haskey(syms, s)
        return CQLSym(s, CQLTerm[_infer_mapping_term(var, fk_names, att_names, syms, a) for a in raw.args])
    else
        throw(CQLException("Cannot type mapping term: $(raw.head)"))
    end
end

# ============================================================================
# Expression types
# ============================================================================

abstract type MappingExp end

struct MappingVar <: MappingExp
    name::String
end

struct MappingId <: MappingExp
    schema::SchemaExp
end

struct MappingComp <: MappingExp
    first::MappingExp
    second::MappingExp
end

struct MappingRawExp <: MappingExp
    raw::MappingExpRaw
end

"""Mapping from pivot schema to original schema."""
struct MappingPivot <: MappingExp
    instance::Any  # InstanceExp
end

"""Mapping inclusion: include src_schema tgt_schema"""
struct MappingInclude <: MappingExp
    src_schema::SchemaExp
    tgt_schema::SchemaExp
end

"""Mapping to prefixed schema: to_prefix schema prefix_str"""
struct MappingToPrefix <: MappingExp
    schema::SchemaExp
    prefix_str::String
end

"""Mapping from prefixed schema: from_prefix schema prefix_str"""
struct MappingFromPrefix <: MappingExp
    schema::SchemaExp
    prefix_str::String
end

function deps(e::MappingExp)::Vector{Tuple{String,Kind}}
    if e isa MappingVar
        [(e.name, MAPPING)]
    elseif e isa MappingId
        deps(e.schema)
    elseif e isa MappingComp
        vcat(deps(e.first), deps(e.second))
    elseif e isa MappingRawExp
        src_deps = e.raw.src_ref isa SchemaExp ? deps(e.raw.src_ref) : Tuple{String,Kind}[]
        dst_deps = e.raw.dst_ref isa SchemaExp ? deps(e.raw.dst_ref) : Tuple{String,Kind}[]
        vcat(src_deps, dst_deps, vcat([deps(i) for i in e.raw.imports]...))
    elseif e isa MappingPivot
        deps(e.instance)
    elseif e isa MappingInclude
        vcat(deps(e.src_schema), deps(e.tgt_schema))
    elseif e isa MappingToPrefix
        deps(e.schema)
    elseif e isa MappingFromPrefix
        deps(e.schema)
    else
        Tuple{String,Kind}[]
    end
end
