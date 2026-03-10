"""
Schemas: entities, foreign keys, attributes, and equations.

A schema extends a typeside with:
- A set of entity types
- Foreign keys between entities
- Attributes from entities to types
- Path equations (entity-side)
- Observation equations (type-side)
"""

"""A CQL schema."""
struct CQLSchema
    typeside::Typeside
    ens::Set{Symbol}
    fks::Dict{Symbol, Tuple{Symbol, Symbol}}    # fk -> (src entity, tgt entity)
    atts::Dict{Symbol, Tuple{Symbol, Symbol}}    # att -> (src entity, tgt type)
    path_eqs::Set{Tuple{Symbol, Equation}}       # (entity, equation) - entity side
    obs_eqs::Set{Tuple{Symbol, Equation}}        # (entity, equation) - type side
    eq::Function  # (en::Symbol, eq::Equation) -> Bool
    fk_by_name::Dict{Symbol, Vector{Symbol}}     # plain name -> qualified name(s)
    att_by_name::Dict{Symbol, Vector{Symbol}}     # plain name -> qualified name(s)
    fk_order::Vector{Symbol}                     # FK declaration order
end

# Constructor backward compatibility: accept without fk_by_name/att_by_name
function CQLSchema(ts, ens, fks, atts, peqs, oeqs, eq_fn)
    CQLSchema(ts, ens, fks, atts, peqs, oeqs, eq_fn,
              Dict{Symbol,Vector{Symbol}}(), Dict{Symbol,Vector{Symbol}}(),
              collect(keys(fks)))
end

function Base.:(==)(a::CQLSchema, b::CQLSchema)
    a.typeside == b.typeside && a.ens == b.ens && a.fks == b.fks &&
    a.atts == b.atts && a.path_eqs == b.path_eqs && a.obs_eqs == b.obs_eqs
end

function Base.show(io::IO, sch::CQLSchema)
    println(io, "schema {")
    println(io, "  entities")
    for en in sch.ens
        println(io, "    ", en)
    end
    println(io, "  foreign_keys")
    for (fk, (s, t)) in sch.fks
        println(io, "    ", _display_name(fk), " : ", s, " -> ", t)
    end
    println(io, "  attributes")
    for (att, (s, t)) in sch.atts
        println(io, "    ", _display_name(att), " : ", s, " -> ", t)
    end
    println(io, "  path_equations")
    for (en, eq) in sch.path_eqs
        println(io, "    forall x : ", en, " . ", eq)
    end
    println(io, "  observation_equations")
    for (en, eq) in sch.obs_eqs
        println(io, "    forall x : ", en, " . ", eq)
    end
    println(io, "}")
end

"""Strip Entity__ prefix from qualified names for display."""
function _display_name(name::Symbol)::String
    s = string(name)
    idx = findfirst("__", s)
    idx === nothing ? s : s[last(idx)+1:end]
end

"""Get foreign keys from a given entity."""
function schema_fks_from(sch::CQLSchema, en::Symbol)
    [(fk, tgt) for (fk, (src, tgt)) in sch.fks if src == en]
end

"""Get attributes from a given entity."""
function schema_atts_from(sch::CQLSchema, en::Symbol)
    [(att, ty) for (att, (src, ty)) in sch.atts if src == en]
end

# ============================================================================
# FK/Att name resolution helpers
# ============================================================================

"""Resolve a FK name, handling qualified disambiguation."""
function resolve_fk(sch::CQLSchema, name::Symbol, src_entity::Symbol)::Symbol
    haskey(sch.fks, name) && return name  # non-ambiguous or already qualified
    # Try qualified name
    qualified = Symbol(src_entity, :__, name)
    haskey(sch.fks, qualified) && return qualified
    # Search fk_by_name
    if haskey(sch.fk_by_name, name)
        for qname in sch.fk_by_name[name]
            haskey(sch.fks, qname) && sch.fks[qname][1] == src_entity && return qname
        end
    end
    throw(CQLException("Unknown FK: $name from entity $src_entity"))
end

"""Check if a FK name exists (plain or qualified)."""
function has_fk(sch::CQLSchema, name::Symbol)::Bool
    haskey(sch.fks, name) && return true
    haskey(sch.fk_by_name, name) && return true
    false
end

"""Get all qualified FK names for a plain name."""
function fk_candidates(sch::CQLSchema, name::Symbol)::Vector{Symbol}
    haskey(sch.fks, name) && return [name]
    get(sch.fk_by_name, name, Symbol[])
end

"""Resolve an attribute name, handling qualified disambiguation."""
function resolve_att(sch::CQLSchema, name::Symbol, src_entity::Symbol)::Symbol
    haskey(sch.atts, name) && return name
    qualified = Symbol(src_entity, :__, name)
    haskey(sch.atts, qualified) && return qualified
    if haskey(sch.att_by_name, name)
        for qname in sch.att_by_name[name]
            haskey(sch.atts, qname) && sch.atts[qname][1] == src_entity && return qname
        end
    end
    throw(CQLException("Unknown attribute: $name from entity $src_entity"))
end

"""Check if an attribute name exists (plain or qualified)."""
function has_att(sch::CQLSchema, name::Symbol)::Bool
    haskey(sch.atts, name) && return true
    haskey(sch.att_by_name, name) && return true
    false
end

"""Get all qualified att names for a plain name."""
function att_candidates(sch::CQLSchema, name::Symbol)::Vector{Symbol}
    haskey(sch.atts, name) && return [name]
    get(sch.att_by_name, name, Symbol[])
end

"""Convert a schema to a collage for type-checking."""
function schema_to_collage(sch::CQLSchema)::Collage
    ts_col = typeside_to_collage(sch.typeside)

    ceqs = Set{Tuple{Ctx, Equation}}()

    # Path equations: variable is Left(()) mapping to Right(entity)
    for (en, eq) in sch.path_eqs
        ctx = Ctx(Symbol("_unit") => Right(en))
        push!(ceqs, (ctx, eq))
    end

    # Observation equations
    for (en, eq) in sch.obs_eqs
        ctx = Ctx(Symbol("_unit") => Right(en))
        push!(ceqs, (ctx, eq))
    end

    # Typeside equations (re-contextualized)
    for (ctx, eq) in ts_col.ceqs
        # Prefix typeside variables to avoid collision
        new_ctx = Ctx()
        for (v, sort) in ctx
            new_ctx[Symbol("_ts_", v)] = sort
        end
        new_eq = Equation(
            map_term(eq.lhs; on_var = v -> Symbol("_ts_", v)),
            map_term(eq.rhs; on_var = v -> Symbol("_ts_", v)),
        )
        push!(ceqs, (new_ctx, new_eq))
    end

    Collage(ceqs, ts_col.ctys, sch.ens, ts_col.csyms, sch.fks, sch.atts,
            Dict{Symbol,Symbol}(), Dict{Symbol,Symbol}())
end

"""Typecheck a schema."""
function typecheck_schema(sch::CQLSchema)
    typecheck_collage(schema_to_collage(sch))
end

"""Create a schema from just a typeside (no entities)."""
function typeside_to_schema(ts::Typeside)
    CQLSchema(ts, Set{Symbol}(),
              Dict{Symbol,Tuple{Symbol,Symbol}}(),
              Dict{Symbol,Tuple{Symbol,Symbol}}(),
              Set{Tuple{Symbol,Equation}}(),
              Set{Tuple{Symbol,Equation}}(),
              (en, eq) -> error("Empty schema has no equations"))
end

# ============================================================================
# Raw schema evaluation
# ============================================================================

"""Raw schema data from parsing."""
struct SchemaRaw
    typeside_ref::Any  # TypesideExp or reference
    ens::Vector{String}
    fks::Vector{Tuple{String, Tuple{String, String}}}
    atts::Vector{Tuple{String, Tuple{String, String}}}
    path_eqs::Vector{Tuple{Vector{String}, Vector{String}}}  # paths as lists of names
    obs_eqs::Vector{Tuple{String, Union{Nothing,String}, RawTerm, RawTerm}}
    options::Vector{Tuple{String, String}}
    imports::Vector{Any}  # SchemaExp references
end

"""Evaluate a raw schema into a CQLSchema."""
function eval_schema_raw(opts::CQLOptions, ts::Typeside, raw::SchemaRaw,
                         imports::Vector{CQLSchema}=CQLSchema[])
    # Merge imports
    imported_ens = Set{Symbol}()
    imported_fks = Dict{Symbol,Tuple{Symbol,Symbol}}()
    imported_atts = Dict{Symbol,Tuple{Symbol,Symbol}}()
    imported_peqs = Set{Tuple{Symbol,Equation}}()
    imported_oeqs = Set{Tuple{Symbol,Equation}}()
    imported_fk_by_name = Dict{Symbol,Vector{Symbol}}()
    imported_att_by_name = Dict{Symbol,Vector{Symbol}}()
    for imp in imports
        union!(imported_ens, imp.ens)
        union!(imported_peqs, imp.path_eqs)
        union!(imported_oeqs, imp.obs_eqs)
        # Merge FKs with conflict detection
        _merge_items_with_conflicts!(imported_fks, imported_fk_by_name, imp.fks, imp.fk_by_name)
        # Merge atts with conflict detection
        _merge_items_with_conflicts!(imported_atts, imported_att_by_name, imp.atts, imp.att_by_name)
    end

    ens = union(imported_ens, Set{Symbol}(Symbol(e) for e in raw.ens))

    # Collect raw FK declarations, detecting duplicates
    raw_fk_list = Tuple{Symbol, Symbol, Symbol}[]  # (name, src, tgt)
    for (name, (s, t)) in raw.fks
        push!(raw_fk_list, (Symbol(name), Symbol(s), Symbol(t)))
    end
    # Also include imported FKs (already stored with their possibly-qualified names)
    for (qname, (s, t)) in imported_fks
        # Already stored
    end

    # Detect duplicate FK names across raw declarations
    fk_name_counts = Dict{Symbol, Int}()
    for (name, _, _) in raw_fk_list
        fk_name_counts[name] = get(fk_name_counts, name, 0) + 1
    end

    fks = copy(imported_fks)
    fk_by_name = copy(imported_fk_by_name)

    for (name, src, tgt) in raw_fk_list
        if fk_name_counts[name] > 1
            # Qualify the FK name
            qualified = Symbol(src, :__, name)
            fks[qualified] = (src, tgt)
            if !haskey(fk_by_name, name)
                fk_by_name[name] = Symbol[]
            end
            push!(fk_by_name[name], qualified)
        else
            # Check if imported FKs already have this name (conflict with import)
            if haskey(fks, name) || haskey(fk_by_name, name)
                qualified = Symbol(src, :__, name)
                fks[qualified] = (src, tgt)
                if !haskey(fk_by_name, name)
                    fk_by_name[name] = Symbol[]
                end
                push!(fk_by_name[name], qualified)
            else
                fks[name] = (src, tgt)
            end
        end
    end

    # Same for attributes
    raw_att_list = Tuple{Symbol, Symbol, Symbol}[]
    for (name, (s, t)) in raw.atts
        push!(raw_att_list, (Symbol(name), Symbol(s), Symbol(t)))
    end

    att_name_counts = Dict{Symbol, Int}()
    for (name, _, _) in raw_att_list
        att_name_counts[name] = get(att_name_counts, name, 0) + 1
    end

    atts = copy(imported_atts)
    att_by_name = copy(imported_att_by_name)

    for (name, src, tgt) in raw_att_list
        if att_name_counts[name] > 1
            qualified = Symbol(src, :__, name)
            atts[qualified] = (src, tgt)
            if !haskey(att_by_name, name)
                att_by_name[name] = Symbol[]
            end
            push!(att_by_name[name], qualified)
        else
            if haskey(atts, name) || haskey(att_by_name, name)
                qualified = Symbol(src, :__, name)
                atts[qualified] = (src, tgt)
                if !haskey(att_by_name, name)
                    att_by_name[name] = Symbol[]
                end
                push!(att_by_name[name], qualified)
            else
                atts[name] = (src, tgt)
            end
        end
    end

    fk_names = collect(keys(fks))
    att_names = collect(keys(atts))
    en_list = collect(ens)

    # Build FK declaration order: imported FKs first, then raw FKs
    fk_order = Symbol[]
    for imp in imports
        for fk in imp.fk_order
            fk in fk_order || push!(fk_order, fk)
        end
    end
    for (name, src, tgt) in raw_fk_list
        actual_name = if fk_name_counts[name] > 1
            Symbol(src, :__, name)
        elseif haskey(imported_fks, name) || any(v -> name in v, values(imported_fk_by_name))
            Symbol(src, :__, name)
        else
            name
        end
        actual_name in fk_order || push!(fk_order, actual_name)
    end

    # Process path equations
    path_eqs = copy(imported_peqs)
    for (lpath, rpath) in raw.path_eqs
        lhs = _proc_path_ext(en_list, fk_names, fk_by_name, fks, reverse(lpath))
        rhs = _proc_path_ext(en_list, fk_names, fk_by_name, fks, reverse(rpath))
        en = _find_path_entity_ext(en_list, fks, fk_by_name, lpath)
        push!(path_eqs, (en, Equation(lhs, rhs)))
    end

    # Process observation equations
    obs_eqs = copy(imported_oeqs)
    for (v, en_hint, lhs_raw, rhs_raw) in raw.obs_eqs
        en = if en_hint !== nothing
            Symbol(en_hint)
        else
            _infer_eq_entity_ext(v, fks, atts, fk_by_name, att_by_name, lhs_raw, rhs_raw)
        end
        lhs = _proc_obs_term_ext(v, en, fk_names, att_names, fk_by_name, att_by_name, fks, atts, ts.syms, lhs_raw)
        rhs = _proc_obs_term_ext(v, en, fk_names, att_names, fk_by_name, att_by_name, fks, atts, ts.syms, rhs_raw)
        push!(obs_eqs, (en, Equation(lhs, rhs)))
    end

    sch_no_prover = CQLSchema(ts, ens, fks, atts, path_eqs, obs_eqs,
                               (en, eq) -> error("Prover not initialized"),
                               fk_by_name, att_by_name, fk_order)

    # Create prover — schemas inherently have uninhabited entity sorts
    local_opts = isempty(raw.options) ? opts : to_options(opts, raw.options)
    if !get_bool(local_opts, ALLOW_EMPTY_SORTS_UNSAFE)
        local_opts = to_options(local_opts, [("allow_empty_sorts_unsafe", "true")])
    end
    col = schema_to_collage(sch_no_prover)
    prover = create_prover(col, local_opts)

    eq_fn = (en, eq) -> begin
        ctx = Ctx(Symbol("_unit") => Right(en))
        prover(ctx, eq)
    end

    CQLSchema(ts, ens, fks, atts, path_eqs, obs_eqs, eq_fn, fk_by_name, att_by_name, fk_order)
end

# ============================================================================
# Extended path/obs processing with qualified FK support
# ============================================================================

function _proc_path_ext(ens, fk_names, fk_by_name, fks, path)
    if isempty(path)
        return CQLVar(Symbol("_unit"))
    end
    s = Symbol(path[1])
    rest = path[2:end]
    if s in ens
        return _proc_path_ext(ens, fk_names, fk_by_name, fks, rest)
    elseif s in fk_names
        return CQLFk(s, _proc_path_ext(ens, fk_names, fk_by_name, fks, rest))
    elseif haskey(fk_by_name, s)
        # Resolve: need entity context from what follows
        inner = _proc_path_ext(ens, fk_names, fk_by_name, fks, rest)
        entity = _entity_of_path_term(ens, fks, fk_by_name, inner)
        if entity !== nothing
            for qname in fk_by_name[s]
                haskey(fks, qname) && fks[qname][1] == entity && return CQLFk(qname, inner)
            end
        end
        # If we can't resolve unambiguously, try the first candidate
        return CQLFk(fk_by_name[s][1], inner)
    else
        throw(CQLException("Unknown path element: $s"))
    end
end

"""Determine entity of a path term (for FK resolution)."""
function _entity_of_path_term(ens, fks, fk_by_name, t::CQLTerm)::Union{Symbol, Nothing}
    if t isa CQLVar
        return nothing  # unknown without context
    elseif t isa CQLFk
        haskey(fks, t.fk) && return fks[t.fk][2]
        return nothing
    else
        return nothing
    end
end

function _find_path_entity_ext(ens, fks, fk_by_name, path)
    for s in path
        sym = Symbol(s)
        sym in ens && return sym
        if haskey(fks, sym)
            return fks[sym][1]
        end
        # Check fk_by_name
        if haskey(fk_by_name, sym)
            for qname in fk_by_name[sym]
                haskey(fks, qname) && return fks[qname][1]
            end
        end
    end
    throw(CQLException("Path equation cannot be typed"))
end

function _proc_obs_term_ext(var, en, fk_names, att_names, fk_by_name, att_by_name,
                             fks, atts, syms, raw::RawTerm)
    s = Symbol(raw.head)
    if isempty(raw.args) && raw.head == var
        return CQLVar(Symbol("_unit"))
    elseif length(raw.args) == 1 && s in fk_names
        return CQLFk(s, _proc_obs_term_ext(var, en, fk_names, att_names, fk_by_name, att_by_name, fks, atts, syms, raw.args[1]))
    elseif length(raw.args) == 1 && s in att_names
        return CQLAtt(s, _proc_obs_term_ext(var, en, fk_names, att_names, fk_by_name, att_by_name, fks, atts, syms, raw.args[1]))
    elseif length(raw.args) == 1 && haskey(fk_by_name, s)
        # Qualified FK: resolve using entity context
        inner = _proc_obs_term_ext(var, en, fk_names, att_names, fk_by_name, att_by_name, fks, atts, syms, raw.args[1])
        inner_en = _infer_term_entity(var, en, fks, fk_by_name, inner)
        if inner_en !== nothing
            for qname in fk_by_name[s]
                haskey(fks, qname) && fks[qname][1] == inner_en && return CQLFk(qname, inner)
            end
        end
        return CQLFk(fk_by_name[s][1], inner)
    elseif length(raw.args) == 1 && haskey(att_by_name, s)
        inner = _proc_obs_term_ext(var, en, fk_names, att_names, fk_by_name, att_by_name, fks, atts, syms, raw.args[1])
        inner_en = _infer_term_entity(var, en, fks, fk_by_name, inner)
        if inner_en !== nothing
            for qname in att_by_name[s]
                haskey(atts, qname) && atts[qname][1] == inner_en && return CQLAtt(qname, inner)
            end
        end
        return CQLAtt(att_by_name[s][1], inner)
    elseif haskey(syms, s)
        args = [_proc_obs_term_ext(var, en, fk_names, att_names, fk_by_name, att_by_name, fks, atts, syms, a) for a in raw.args]
        return CQLSym(s, args)
    else
        throw(CQLException("Cannot type term: $(raw.head)"))
    end
end

"""Infer the entity of a CQL term in observation equation context."""
function _infer_term_entity(var, base_en, fks, fk_by_name, t::CQLTerm)::Union{Symbol, Nothing}
    if t isa CQLVar
        return base_en  # the variable has the equation's entity
    elseif t isa CQLFk
        haskey(fks, t.fk) && return fks[t.fk][2]
        return nothing
    else
        return nothing
    end
end

function _infer_eq_entity_ext(var, fks, atts, fk_by_name, att_by_name, lhs, rhs)
    types_l = _entity_types_of_ext(var, fks, atts, fk_by_name, att_by_name, lhs)
    types_r = _entity_types_of_ext(var, fks, atts, fk_by_name, att_by_name, rhs)
    all_types = unique(vcat(types_l, types_r))
    isempty(all_types) && throw(CQLException("Untypeable variable: $var"))
    all_types[1]
end

function _entity_types_of_ext(var, fks, atts, fk_by_name, att_by_name, t::RawTerm)
    result = Symbol[]
    if length(t.args) == 1
        s = Symbol(t.head)
        if t.args[1].head == var && isempty(t.args[1].args)
            if haskey(fks, s)
                push!(result, fks[s][1])
            elseif haskey(atts, s)
                push!(result, atts[s][1])
            elseif haskey(fk_by_name, s)
                for qn in fk_by_name[s]
                    haskey(fks, qn) && push!(result, fks[qn][1])
                end
            elseif haskey(att_by_name, s)
                for qn in att_by_name[s]
                    haskey(atts, qn) && push!(result, atts[qn][1])
                end
            end
        else
            append!(result, _entity_types_of_ext(var, fks, atts, fk_by_name, att_by_name, t.args[1]))
        end
    end
    for a in t.args
        append!(result, _entity_types_of_ext(var, fks, atts, fk_by_name, att_by_name, a))
    end
    result
end

"""Merge FK/att items from an imported schema, detecting and qualifying conflicts.

Handles three conflict cases:
1. Plain name exists in both target and source with different src entities
2. Plain name in source conflicts with qualified names in target's by_name
3. Plain name in target conflicts with qualified names in source's by_name
"""
function _merge_items_with_conflicts!(target::Dict{Symbol,Tuple{Symbol,Symbol}},
                                       target_by_name::Dict{Symbol,Vector{Symbol}},
                                       source::Dict{Symbol,Tuple{Symbol,Symbol}},
                                       source_by_name::Dict{Symbol,Vector{Symbol}})
    for (name, (src, tgt)) in source
        if haskey(target, name)
            existing = target[name]
            if existing == (src, tgt)
                # Same item, no conflict
                continue
            end
            # Conflict: same name, different entries
            existing_src = existing[1]
            existing_tgt = existing[2]
            # Re-qualify existing
            delete!(target, name)
            qualified_existing = Symbol(existing_src, :__, name)
            target[qualified_existing] = (existing_src, existing_tgt)
            if !haskey(target_by_name, name)
                target_by_name[name] = Symbol[]
            end
            push!(target_by_name[name], qualified_existing)
            # Qualify new
            qualified_new = Symbol(src, :__, name)
            target[qualified_new] = (src, tgt)
            push!(target_by_name[name], qualified_new)
        elseif haskey(target_by_name, name)
            # Plain name conflicts with qualified names from target
            qualified = Symbol(src, :__, name)
            target[qualified] = (src, tgt)
            push!(target_by_name[name], qualified)
        else
            target[name] = (src, tgt)
        end
    end
    # Merge by_name entries from source
    for (k, v) in source_by_name
        if haskey(target_by_name, k)
            append!(target_by_name[k], v)
        else
            target_by_name[k] = copy(v)
        end
        # If there's also a plain name in target that needs qualifying
        if haskey(target, k) && !occursin("__", string(k))
            (existing_src, existing_tgt) = target[k]
            qualified = Symbol(existing_src, :__, k)
            target[qualified] = (existing_src, existing_tgt)
            delete!(target, k)
            push!(target_by_name[k], qualified)
        end
    end
end

# ============================================================================
# Original path helpers (backward compatible, used by non-schema code)
# ============================================================================

function _proc_path(ens::Vector{Symbol}, fk_names::Vector{Symbol}, path::Vector{String})
    if isempty(path)
        return CQLVar(Symbol("_unit"))
    end
    s = Symbol(path[1])
    rest = path[2:end]
    if s in ens
        return _proc_path(ens, fk_names, rest)
    elseif s in fk_names
        return CQLFk(s, _proc_path(ens, fk_names, rest))
    else
        # Try suffix matching for colimit qualified names
        resolved = _resolve_name_suffix(s, fk_names)
        if resolved !== nothing
            return CQLFk(resolved, _proc_path(ens, fk_names, rest))
        end
        throw(CQLException("Unknown path element: $s"))
    end
end

"""Resolve a name by suffix matching against a list of qualified names.
Also handles Schema_FK → Schema_Entity_FK pattern used in colimit path equations."""
function _resolve_name_suffix(name::Symbol, qualified::Vector{Symbol})::Union{Symbol, Nothing}
    name_str = string(name)
    suffix = "_" * name_str
    for qn in qualified
        if endswith(string(qn), suffix)
            return qn
        end
    end
    # Try Schema_FK pattern: match qualified names of form Schema_Entity_FK
    # where input is Schema_FK (missing the Entity segment)
    idx = findfirst('_', name_str)
    if idx !== nothing
        prefix = name_str[1:idx-1]       # e.g. "IFC"
        fk_part = name_str[idx+1:end]     # e.g. "elementInSpace"
        candidates = Symbol[]
        for qn in qualified
            qn_str = string(qn)
            if startswith(qn_str, prefix * "_") && endswith(qn_str, "_" * fk_part)
                push!(candidates, qn)
            end
        end
        length(candidates) == 1 && return candidates[1]
    end
    nothing
end

function _find_path_entity(ens, fks, path)
    for s in path
        sym = Symbol(s)
        sym in ens && return sym
        if haskey(fks, sym)
            return fks[sym][1]
        end
        # Try suffix matching
        for (fk, (src, _)) in fks
            if endswith(string(fk), "_" * string(sym))
                return src
            end
        end
    end
    throw(CQLException("Path equation cannot be typed"))
end

function _proc_obs_term(var::String, fk_names, att_names, syms, raw::RawTerm)
    s = Symbol(raw.head)
    if isempty(raw.args) && raw.head == var
        return CQLVar(Symbol("_unit"))
    elseif length(raw.args) == 1 && s in fk_names
        return CQLFk(s, _proc_obs_term(var, fk_names, att_names, syms, raw.args[1]))
    elseif length(raw.args) == 1 && s in att_names
        return CQLAtt(s, _proc_obs_term(var, fk_names, att_names, syms, raw.args[1]))
    elseif haskey(syms, s)
        args = [_proc_obs_term(var, fk_names, att_names, syms, a) for a in raw.args]
        return CQLSym(s, args)
    else
        throw(CQLException("Cannot type term: $(raw.head)"))
    end
end

function _infer_eq_entity(var, fks, atts, lhs, rhs)
    types_l = _entity_types_of(var, fks, atts, lhs)
    types_r = _entity_types_of(var, fks, atts, rhs)
    all_types = unique(vcat(types_l, types_r))
    isempty(all_types) && throw(CQLException("Untypeable variable: $var"))
    all_types[1]
end

function _entity_types_of(var, fks, atts, t::RawTerm)
    result = Symbol[]
    if length(t.args) == 1
        s = Symbol(t.head)
        if t.args[1].head == var && isempty(t.args[1].args)
            if haskey(fks, s)
                push!(result, fks[s][1])
            elseif haskey(atts, s)
                push!(result, atts[s][1])
            end
        else
            append!(result, _entity_types_of(var, fks, atts, t.args[1]))
        end
    end
    for a in t.args
        append!(result, _entity_types_of(var, fks, atts, a))
    end
    result
end

# ============================================================================
# Expression types
# ============================================================================

abstract type SchemaExp end

struct SchemaVar <: SchemaExp
    name::String
end

struct SchemaInitial <: SchemaExp
    typeside::TypesideExp
end

struct SchemaRawExp <: SchemaExp
    raw::SchemaRaw
end

"""Schema from pivot of an instance."""
struct SchemaPivot <: SchemaExp
    instance::Any  # InstanceExp
end

"""Schema imported from JDBC (all tables)."""
struct SchemaImportJdbcAll <: SchemaExp
    connection::String
    options::Vector{Tuple{String,String}}
end

"""Schema imported from ODBC (all tables)."""
struct SchemaImportOdbcAll <: SchemaExp
    connection::String
    options::Vector{Tuple{String,String}}
end

"""Schema extracted from an instance: schemaOf I"""
struct SchemaOf <: SchemaExp
    instance::Any  # InstanceExp
end

"""Front schema of a constraint: front constraints index"""
struct SchemaFront <: SchemaExp
    constraints_name::String
    index::Int
end

"""Spanify schema: spanify S"""
struct SchemaSpanify <: SchemaExp
    schema::SchemaExp
end

"""Prefix schema: prefix S str"""
struct SchemaPrefix <: SchemaExp
    schema::SchemaExp
    prefix_str::String
end

"""Domain schema of a query: dom_q Q"""
struct SchemaDomQ <: SchemaExp
    query::Any  # QueryExp
end

"""Codomain schema of a query: cod_q Q"""
struct SchemaCodQ <: SchemaExp
    query::Any  # QueryExp
end

"""Domain schema of a mapping: dom_m M"""
struct SchemaDomM <: SchemaExp
    mapping::Any  # MappingExp
end

"""Codomain schema of a mapping: cod_m M"""
struct SchemaCodM <: SchemaExp
    mapping::Any  # MappingExp
end

function deps(e::SchemaExp)::Vector{Tuple{String,Kind}}
    if e isa SchemaVar
        [(e.name, SCHEMA)]
    elseif e isa SchemaInitial
        deps(e.typeside)
    elseif e isa SchemaRawExp
        ts_deps = e.raw.typeside_ref isa TypesideExp ? deps(e.raw.typeside_ref) : Tuple{String,Kind}[]
        vcat(ts_deps, vcat([deps(i) for i in e.raw.imports]...))
    elseif e isa SchemaPivot
        deps(e.instance)
    elseif e isa SchemaOf
        deps(e.instance)
    elseif e isa SchemaImportJdbcAll
        Tuple{String,Kind}[]
    elseif e isa SchemaImportOdbcAll
        Tuple{String,Kind}[]
    elseif e isa SchemaFront
        [(e.constraints_name, CONSTRAINTS)]
    elseif e isa SchemaSpanify
        deps(e.schema)
    elseif e isa SchemaPrefix
        deps(e.schema)
    elseif e isa SchemaDomQ
        deps(e.query)
    elseif e isa SchemaCodQ
        deps(e.query)
    elseif e isa SchemaDomM
        deps(e.mapping)
    elseif e isa SchemaCodM
        deps(e.mapping)
    else
        Tuple{String,Kind}[]
    end
end
