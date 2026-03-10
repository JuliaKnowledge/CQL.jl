"""
Schema colimits: quotient-style combination of multiple schemas.

A schema colimit merges multiple schemas by identifying entities and paths,
producing a combined schema and inclusion mappings from each source.
"""

# ============================================================================
# Symbol Union-Find (inline, path-compression)
# ============================================================================

mutable struct SymbolUF
    parent::Dict{Symbol, Symbol}
end

SymbolUF() = SymbolUF(Dict{Symbol, Symbol}())

function suf_find!(uf::SymbolUF, x::Symbol)::Symbol
    if !haskey(uf.parent, x)
        uf.parent[x] = x
        return x
    end
    root = x
    while uf.parent[root] != root
        root = uf.parent[root]
    end
    # Path compression
    curr = x
    while curr != root
        next = uf.parent[curr]
        uf.parent[curr] = root
        curr = next
    end
    root
end

function suf_union!(uf::SymbolUF, a::Symbol, b::Symbol)
    ra = suf_find!(uf, a)
    rb = suf_find!(uf, b)
    if ra != rb
        # Make 'a' the canonical representative (LHS of entity equation)
        uf.parent[rb] = ra
    end
end

# ============================================================================
# Expression types
# ============================================================================

struct SchemaColimitExp
    typeside_ref::TypesideExp
    schema_refs::Vector{Tuple{String, SchemaExp}}
    entity_eqs::Vector{Tuple{String, String}}
    path_eqs::Vector{Tuple{RawTerm, RawTerm}}
    obs_eqs::Vector{Tuple{String,Union{Nothing,String},RawTerm,RawTerm}}
    options::Vector{Tuple{String,String}}
    entity_isos::Vector{Tuple{String, String, String}}  # (name, src_dotted, tgt_dotted)
end

# Backward compatibility constructors
function SchemaColimitExp(ts, srefs, eeqs, peqs, opts::Vector{Tuple{String,String}})
    SchemaColimitExp(ts, srefs, eeqs, peqs,
                     Tuple{String,Union{Nothing,String},RawTerm,RawTerm}[], opts,
                     Tuple{String,String,String}[])
end

function SchemaColimitExp(ts, srefs, eeqs, peqs, obs_eqs, opts::Vector{Tuple{String,String}})
    SchemaColimitExp(ts, srefs, eeqs, peqs, obs_eqs, opts, Tuple{String,String,String}[])
end

"""Literal schema colimit over a graph diagram: literal graphName : typeside { nodes ... edges ... }"""
struct SchemaColimitLiteralExp
    graph_name::String
    typeside_ref::TypesideExp
    node_map::Vector{Tuple{String,Any}}   # graph_node -> schema_exp
    edge_map::Vector{Tuple{String,Any}}   # graph_edge -> mapping_exp
    options::Vector{Tuple{String,String}}
end

"""Modify an existing schema colimit: rename/remove entities, FKs, attributes."""
struct SchemaColimitModify <: Any
    base_name::String
    rename_ens::Vector{Tuple{String,String}}
    rename_fks::Vector{Tuple{String,String}}
    rename_atts::Vector{Tuple{String,String}}
    remove_fks::Vector{Tuple{String,String}}
    remove_atts::Vector{Tuple{String,String}}
end

struct SchemaGetSchema <: SchemaExp
    colimit_name::String
end

struct MappingGetMapping <: MappingExp
    colimit_name::String
    schema_name::String
end

struct MappingGetPseudo <: MappingExp
    colimit_name::String
end

function deps(e::SchemaColimitExp)::Vector{Tuple{String,Kind}}
    result = Tuple{String,Kind}[]
    append!(result, deps(e.typeside_ref))
    for (_, sexp) in e.schema_refs
        append!(result, deps(sexp))
    end
    result
end

function deps(e::SchemaColimitLiteralExp)::Vector{Tuple{String,Kind}}
    result = Tuple{String,Kind}[]
    push!(result, (e.graph_name, GRAPH))
    append!(result, deps(e.typeside_ref))
    for (_, sexp) in e.node_map
        if sexp isa SchemaExp
            append!(result, deps(sexp))
        elseif sexp isa String
            push!(result, (sexp, SCHEMA))
        end
    end
    for (_, mexp) in e.edge_map
        if mexp isa MappingExp
            append!(result, deps(mexp))
        elseif mexp isa String
            push!(result, (mexp, MAPPING))
        end
    end
    result
end

function deps(e::SchemaColimitModify)::Vector{Tuple{String,Kind}}
    [(e.base_name, SCHEMA_COLIMIT)]
end

function deps(e::SchemaGetSchema)::Vector{Tuple{String,Kind}}
    [(e.colimit_name, SCHEMA_COLIMIT)]
end

function deps(e::MappingGetMapping)::Vector{Tuple{String,Kind}}
    [(e.colimit_name, SCHEMA_COLIMIT)]
end

function deps(e::MappingGetPseudo)::Vector{Tuple{String,Kind}}
    [(e.colimit_name, SCHEMA_COLIMIT)]
end

# ============================================================================
# Result type
# ============================================================================

struct SchemaColimitResult
    schema::CQLSchema
    mappings::Dict{String, CQLMapping}
    names::Vector{String}
    entity_canonical::Dict{Symbol,Symbol}  # all prefixed entity names → canonical
    entity_isos::Vector{Tuple{String,String,String}}  # (name, src_dotted, tgt_dotted) for pseudo_quotient
end

# Backward-compatible constructor
SchemaColimitResult(schema, mappings, names, entity_canonical) =
    SchemaColimitResult(schema, mappings, names, entity_canonical, Tuple{String,String,String}[])

# ============================================================================
# Colimit computation
# ============================================================================

"""Compute a schema colimit from evaluated schemas."""
function eval_schema_colimit(opts::CQLOptions, ts::Typeside,
                             schemas::Vector{Tuple{String, CQLSchema}},
                             entity_eqs::Vector{Tuple{String, String}},
                             path_eqs::Vector{Tuple{RawTerm, RawTerm}};
                             obs_eqs::Vector{Tuple{String,Union{Nothing,String},RawTerm,RawTerm}}=Tuple{String,Union{Nothing,String},RawTerm,RawTerm}[],
                             entity_isos::Vector{Tuple{String,String,String}}=Tuple{String,String,String}[])::SchemaColimitResult
    uf = SymbolUF()

    # Step 1: Prefix all entities as SchemaName_EntityName
    all_ens = Symbol[]
    # Maps: (schema_name, original_entity) -> prefixed_entity
    prefix_map = Dict{Tuple{String, Symbol}, Symbol}()
    for (sname, sch) in schemas
        for en in sch.ens
            prefixed = Symbol(sname, "_", en)
            push!(all_ens, prefixed)
            prefix_map[(sname, en)] = prefixed
            suf_find!(uf, prefixed)
        end
    end

    # Step 2: Apply entity equations
    for (lhs_str, rhs_str) in entity_eqs
        lhs_sym = _parse_dotted_entity(lhs_str, schemas, prefix_map)
        rhs_sym = _parse_dotted_entity(rhs_str, schemas, prefix_map)
        suf_union!(uf, lhs_sym, rhs_sym)
    end

    # Build canonical name mapping
    canonical = Dict{Symbol, Symbol}()
    for en in all_ens
        canonical[en] = suf_find!(uf, en)
    end

    # Collect unique canonical entities
    combined_ens = Set{Symbol}(values(canonical))

    # Step 3: Build combined FKs and attributes with canonical entity names
    combined_fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    combined_atts = Dict{Symbol, Tuple{Symbol, Symbol}}()
    combined_path_eqs = Set{Tuple{Symbol, Equation}}()
    combined_obs_eqs = Set{Tuple{Symbol, Equation}}()

    # Track original FK/att -> prefixed FK/att for each schema
    fk_prefix_map = Dict{Tuple{String, Symbol}, Symbol}()
    att_prefix_map = Dict{Tuple{String, Symbol}, Symbol}()

    for (sname, sch) in schemas
        for (fk, (src, tgt)) in sch.fks
            # Java CQL convention: SchemaName_SourceEntity_OriginalFKName
            orig_fk = _strip_entity_prefix(fk, src)
            pfk = Symbol(sname, "_", src, "_", orig_fk)
            psrc = canonical[prefix_map[(sname, src)]]
            ptgt = canonical[prefix_map[(sname, tgt)]]
            combined_fks[pfk] = (psrc, ptgt)
            fk_prefix_map[(sname, fk)] = pfk
        end
        for (att, (src, ty)) in sch.atts
            orig_att = _strip_entity_prefix(att, src)
            patt = Symbol(sname, "_", src, "_", orig_att)
            psrc = canonical[prefix_map[(sname, src)]]
            combined_atts[patt] = (psrc, ty)
            att_prefix_map[(sname, att)] = patt
        end
        # Translate path equations
        for (en, eq) in sch.path_eqs
            pen = canonical[prefix_map[(sname, en)]]
            new_lhs = _prefix_entity_term(sname, eq.lhs, fk_prefix_map)
            new_rhs = _prefix_entity_term(sname, eq.rhs, fk_prefix_map)
            push!(combined_path_eqs, (pen, Equation(new_lhs, new_rhs)))
        end
        # Translate observation equations
        for (en, eq) in sch.obs_eqs
            pen = canonical[prefix_map[(sname, en)]]
            new_lhs = _prefix_type_term(sname, eq.lhs, fk_prefix_map, att_prefix_map)
            new_rhs = _prefix_type_term(sname, eq.rhs, fk_prefix_map, att_prefix_map)
            push!(combined_obs_eqs, (pen, Equation(new_lhs, new_rhs)))
        end
    end

    # Step 3b: Add entity isomorphism FKs
    for (iso_name, src_dotted, tgt_dotted) in entity_isos
        src_en = _parse_dotted_entity(src_dotted, schemas, prefix_map)
        tgt_en = _parse_dotted_entity(tgt_dotted, schemas, prefix_map)
        src_canonical = canonical[src_en]
        tgt_canonical = canonical[tgt_en]
        iso_fk = Symbol(iso_name)
        if src_canonical == tgt_canonical
            # Quotient: entities are merged, isomorphism FK = identity
            combined_fks[iso_fk] = (src_canonical, src_canonical)
            push!(combined_path_eqs, (src_canonical,
                Equation(CQLFk(iso_fk, CQLVar(Symbol("_unit"))), CQLVar(Symbol("_unit")))))
        else
            # Pseudo-quotient: entities are separate, add forward and inverse FKs
            combined_fks[iso_fk] = (src_canonical, tgt_canonical)
            inv_fk = Symbol(iso_name, "_inv")
            combined_fks[inv_fk] = (tgt_canonical, src_canonical)
            # Path equations: inv(fwd(x)) = x and fwd(inv(y)) = y
            push!(combined_path_eqs, (src_canonical,
                Equation(CQLFk(inv_fk, CQLFk(iso_fk, CQLVar(Symbol("_unit")))), CQLVar(Symbol("_unit")))))
            push!(combined_path_eqs, (tgt_canonical,
                Equation(CQLFk(iso_fk, CQLFk(inv_fk, CQLVar(Symbol("_unit")))), CQLVar(Symbol("_unit")))))
        end
    end

    # Step 4: Process path_equations from colimit declaration
    all_fk_names = collect(keys(combined_fks))
    all_att_names = collect(keys(combined_atts))
    # Include ALL entity names (canonical + non-canonical) so path equations
    # can reference merged entities by any of their original prefixed names
    all_en_list_for_paths = collect(keys(canonical))
    # Also build a mapping from any entity name to its canonical representative
    en_to_canonical = Dict{Symbol, Symbol}(en => canonical[en] for en in keys(canonical))

    for (lhs_raw, rhs_raw) in path_eqs
        lhs_path = _raw_term_to_path(lhs_raw)
        rhs_path = _raw_term_to_path(rhs_raw)
        lhs_term = _proc_path(all_en_list_for_paths, all_fk_names, reverse(lhs_path))
        rhs_term = _proc_path(all_en_list_for_paths, all_fk_names, reverse(rhs_path))
        en_raw = _find_path_entity(all_en_list_for_paths, combined_fks, lhs_path)
        en = get(en_to_canonical, en_raw, en_raw)
        push!(combined_path_eqs, (en, Equation(lhs_term, rhs_term)))
    end

    # Step 4b: Process observation equations from colimit declaration
    for (var, var_ty, lhs_raw, rhs_raw) in obs_eqs
        # Determine entity for the variable: if var_ty is given, use it; else infer
        en = if var_ty !== nothing
            # Try to resolve dotted name (e.g., "Olog1Schema.Patient")
            en_sym = Symbol(var_ty)
            if haskey(en_to_canonical, en_sym)
                en_sym
            else
                # Try converting dots to underscores (Schema.Entity -> Schema_Entity)
                en_underscore = Symbol(replace(var_ty, "." => "_"))
                haskey(en_to_canonical, en_underscore) ? en_underscore : en_sym
            end
        else
            # Try to infer from term structure (first entity that has the referenced attributes)
            _infer_obs_eq_entity(lhs_raw, combined_ens, combined_fks, combined_atts)
        end
        # For the canonical entity, check if it's in combined_ens or needs resolution
        canon_en = get(en_to_canonical, en, en)
        if !(canon_en in combined_ens)
            canon_en = en  # use as-is if already canonical
        end
        # Parse terms in the context of the combined schema
        all_fk_sym = Set{Symbol}(keys(combined_fks))
        all_att_sym = Set{Symbol}(keys(combined_atts))
        sym_var = Symbol(var)
        lhs_term = _proc_colimit_obs_term(sym_var, all_fk_sym, all_att_sym, keys(ts.syms), lhs_raw;
                                          var_entity=canon_en, fks_dict=combined_fks, atts_dict=combined_atts)
        rhs_term = _proc_colimit_obs_term(sym_var, all_fk_sym, all_att_sym, keys(ts.syms), rhs_raw;
                                          var_entity=canon_en, fks_dict=combined_fks, atts_dict=combined_atts)
        push!(combined_obs_eqs, (canon_en, Equation(lhs_term, rhs_term)))
    end

    # Build fk_by_name and att_by_name for the combined schema
    combined_fk_by_name = _build_by_name(combined_fks)
    combined_att_by_name = _build_by_name(combined_atts)

    # Step 5: Build the combined schema
    sch_no_prover = CQLSchema(ts, combined_ens, combined_fks, combined_atts,
                               combined_path_eqs, combined_obs_eqs,
                               (en, eq) -> error("Prover not initialized"),
                               combined_fk_by_name, combined_att_by_name,
                               collect(keys(combined_fks)))

    local_opts = opts
    if !get_bool(local_opts, ALLOW_EMPTY_SORTS_UNSAFE)
        local_opts = to_options(local_opts, [("allow_empty_sorts_unsafe", "true")])
    end
    col = schema_to_collage(sch_no_prover)
    prover = create_prover(col, local_opts)

    eq_fn = (en, eq) -> begin
        ctx = Ctx(Symbol("_unit") => Right(en))
        prover(ctx, eq)
    end

    combined_schema = CQLSchema(ts, combined_ens, combined_fks, combined_atts,
                                 combined_path_eqs, combined_obs_eqs, eq_fn,
                                 combined_fk_by_name, combined_att_by_name,
                                 collect(keys(combined_fks)))

    # Step 6: Build mappings from each source schema to the combined schema
    mappings = Dict{String, CQLMapping}()
    for (sname, sch) in schemas
        m_ens = Dict{Symbol, Symbol}()
        for en in sch.ens
            m_ens[en] = canonical[prefix_map[(sname, en)]]
        end

        m_fks = Dict{Symbol, CQLTerm}()
        for fk in keys(sch.fks)
            pfk = fk_prefix_map[(sname, fk)]
            m_fks[fk] = CQLFk(pfk, CQLVar(Symbol("_unit")))
        end

        m_atts = Dict{Symbol, CQLTerm}()
        for att in keys(sch.atts)
            patt = att_prefix_map[(sname, att)]
            m_atts[att] = CQLAtt(patt, CQLVar(Symbol("_unit")))
        end

        mappings[sname] = CQLMapping(sch, combined_schema, m_ens, m_fks, m_atts)
    end

    SchemaColimitResult(combined_schema, mappings, [s for (s, _) in schemas], canonical, entity_isos)
end

# ============================================================================
# Helpers
# ============================================================================

"""Build a by_name lookup dict from qualified names.
For each qualified name like SchemaName_Entity_AttrName, extracts the short
suffix (AttrName) and maps it to the list of qualified names."""
function _build_by_name(items::Dict{Symbol, Tuple{Symbol, Symbol}})::Dict{Symbol, Vector{Symbol}}
    by_name = Dict{Symbol, Vector{Symbol}}()
    for qname in keys(items)
        s = string(qname)
        # Extract possible short names by progressively stripping prefixes
        # Try: remove everything before first _, before second _, etc.
        parts = split(s, '_')
        for i in 2:length(parts)
            suffix = Symbol(join(parts[i:end], '_'))
            if suffix != qname
                if !haskey(by_name, suffix)
                    by_name[suffix] = Symbol[]
                end
                push!(by_name[suffix], qname)
            end
        end
    end
    # Remove entries that only have one qualified name (these are unambiguous)
    # Actually keep them — having short name mappings helps resolution
    by_name
end

"""Strip internal entity prefix (Entity__) from a qualified FK/att name."""
function _strip_entity_prefix(name::Symbol, entity::Symbol)::Symbol
    prefix = string(entity, "__")
    s = string(name)
    if startswith(s, prefix)
        return Symbol(s[length(prefix)+1:end])
    end
    name
end

"""Resolve an unqualified FK/att name by suffix matching in the combined schema."""
function _resolve_colimit_name(name::Symbol, qualified_names)::Union{Symbol, Nothing}
    name in qualified_names && return name
    suffix = "_" * string(name)
    matches = Symbol[]
    for qn in qualified_names
        if endswith(string(qn), suffix)
            push!(matches, qn)
        end
    end
    length(matches) == 1 && return matches[1]
    length(matches) > 1 && return matches[1]  # ambiguous — use first match
    nothing
end

"""Parse 'SchemaName.EntityName' into the prefixed entity symbol."""
function _parse_dotted_entity(s::String, schemas, prefix_map)::Symbol
    parts = split(s, ".")
    length(parts) == 2 || throw(CQLException("Entity equation must be Schema.Entity, got: $s"))
    sname = String(parts[1])
    ename = Symbol(parts[2])
    key = (sname, ename)
    haskey(prefix_map, key) || throw(CQLException("Unknown entity: $s"))
    prefix_map[key]
end

"""Prefix entity-side term (CQLVar/CQLFk) with schema name."""
function _prefix_entity_term(sname::String, t::CQLTerm, fk_map)::CQLTerm
    if t isa CQLVar
        t
    elseif t isa CQLFk
        pfk = fk_map[(sname, t.fk)]
        CQLFk(pfk, _prefix_entity_term(sname, t.arg, fk_map))
    else
        error("Unexpected entity term: $t")
    end
end

"""Prefix type-side term with schema name."""
function _prefix_type_term(sname::String, t::CQLTerm, fk_map, att_map)::CQLTerm
    if t isa CQLAtt
        patt = att_map[(sname, t.att)]
        CQLAtt(patt, _prefix_entity_term(sname, t.arg, fk_map))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_prefix_type_term(sname, a, fk_map, att_map) for a in t.args])
    elseif t isa CQLVar
        t
    elseif t isa CQLFk
        _prefix_entity_term(sname, t, fk_map)
    elseif t isa CQLSk
        t
    else
        error("Unexpected type term: $t")
    end
end

"""Convert a RawTerm dot chain into a path list of strings."""
function _raw_term_to_path(t::RawTerm)::Vector{String}
    if isempty(t.args)
        return [t.head]
    elseif length(t.args) == 1
        return vcat(_raw_term_to_path(t.args[1]), [t.head])
    else
        throw(CQLException("Path equation term must be a dot-chain, got: $t"))
    end
end

"""Process a raw term in colimit observation equation context."""
function _proc_colimit_obs_term(var::Symbol, fk_names, att_names, sym_names, raw::RawTerm;
                                var_entity::Union{Symbol,Nothing}=nothing,
                                fks_dict::Union{Dict{Symbol,Tuple{Symbol,Symbol}},Nothing}=nothing,
                                atts_dict::Union{Dict{Symbol,Tuple{Symbol,Symbol}},Nothing}=nothing)::CQLTerm
    s = Symbol(raw.head)
    kwargs = (var_entity=var_entity, fks_dict=fks_dict, atts_dict=atts_dict)
    if isempty(raw.args) && s == var
        return CQLVar(Symbol("_unit"))  # normalize to _unit for schema prover
    elseif length(raw.args) == 1 && s in fk_names
        return CQLFk(s, _proc_colimit_obs_term(var, fk_names, att_names, sym_names, raw.args[1]; kwargs...))
    elseif length(raw.args) == 1 && s in att_names
        return CQLAtt(s, _proc_colimit_obs_term(var, fk_names, att_names, sym_names, raw.args[1]; kwargs...))
    elseif length(raw.args) == 1
        inner = _proc_colimit_obs_term(var, fk_names, att_names, sym_names, raw.args[1]; kwargs...)
        # Try entity-context-aware resolution first
        if fks_dict !== nothing && atts_dict !== nothing && var_entity !== nothing
            inner_en = _entity_of_colimit_term(inner, var_entity, fks_dict)
            if inner_en !== nothing
                suffix = "_" * string(s)
                # Try FK from inner_en
                for qn in fk_names
                    if endswith(string(qn), suffix) && haskey(fks_dict, qn) && fks_dict[qn][1] == inner_en
                        return CQLFk(qn, inner)
                    end
                end
                # Try att from inner_en
                for qn in att_names
                    if endswith(string(qn), suffix) && haskey(atts_dict, qn) && atts_dict[qn][1] == inner_en
                        return CQLAtt(qn, inner)
                    end
                end
            end
        end
        # Fallback: suffix-matching for unqualified names
        resolved_fk = _resolve_colimit_name(s, fk_names)
        if resolved_fk !== nothing
            return CQLFk(resolved_fk, inner)
        end
        resolved_att = _resolve_colimit_name(s, att_names)
        if resolved_att !== nothing
            return CQLAtt(resolved_att, inner)
        end
        throw(CQLException("Cannot type colimit obs eq term: $(raw.head)"))
    elseif s in sym_names
        return CQLSym(s, CQLTerm[_proc_colimit_obs_term(var, fk_names, att_names, sym_names, a; kwargs...) for a in raw.args])
    elseif isempty(raw.args)
        # Treat as variable reference
        return CQLVar(s)
    else
        throw(CQLException("Cannot type colimit obs eq term: $(raw.head)"))
    end
end

"""Determine entity of a colimit obs eq term for disambiguation."""
function _entity_of_colimit_term(t::CQLTerm, var_entity::Symbol, fks_dict::Dict{Symbol,Tuple{Symbol,Symbol}})::Union{Symbol, Nothing}
    if t isa CQLVar
        return var_entity  # _unit variable → the forall entity
    elseif t isa CQLFk
        haskey(fks_dict, t.fk) && return fks_dict[t.fk][2]
        return nothing
    else
        return nothing
    end
end

"""Infer the entity for an observation equation from the term structure."""
function _infer_obs_eq_entity(raw::RawTerm, ens, fks, atts)::Symbol
    if length(raw.args) == 1
        s = Symbol(raw.head)
        if haskey(atts, s)
            return atts[s][1]
        elseif haskey(fks, s)
            return fks[s][1]
        end
        # Try suffix matching for prefixed colimit names
        resolved_att = _resolve_colimit_name(s, Set{Symbol}(keys(atts)))
        if resolved_att !== nothing
            return atts[resolved_att][1]
        end
        resolved_fk = _resolve_colimit_name(s, Set{Symbol}(keys(fks)))
        if resolved_fk !== nothing
            return fks[resolved_fk][1]
        end
        # Recurse into argument
        return _infer_obs_eq_entity(raw.args[1], ens, fks, atts)
    end
    # Default: first entity
    first(ens)
end

"""Evaluate a modify colimit expression: apply rename/remove to a base colimit."""
function eval_modify_colimit(base::SchemaColimitResult,
                              rename_ens::Vector{Tuple{String,String}},
                              rename_fks::Vector{Tuple{String,String}},
                              rename_atts::Vector{Tuple{String,String}},
                              remove_fks::Vector{Tuple{String,String}},
                              remove_atts::Vector{Tuple{String,String}})::SchemaColimitResult
    sch = base.schema
    ts = sch.typeside

    # Build rename maps — resolve through canonical entity names
    en_rename = Dict{Symbol,Symbol}()
    for (old, new_name) in rename_ens
        old_sym = Symbol(old)
        # If old_sym is a non-canonical entity, resolve to canonical
        canonical_sym = get(base.entity_canonical, old_sym, old_sym)
        en_rename[canonical_sym] = Symbol(new_name)
    end

    # Build reverse entity rename map: new_name -> old_name (canonical)
    en_reverse = Dict{Symbol,Symbol}(v => k for (k, v) in en_rename)

    fk_rename = Dict{Symbol,Symbol}()
    for (old, new_name) in rename_fks
        # old might be "Entity.fk_name" — extract the fk part
        fk_sym = _extract_fk_name(old, sch, en_reverse)
        fk_rename[fk_sym] = Symbol(new_name)
    end

    att_rename = Dict{Symbol,Symbol}()
    for (old, new_name) in rename_atts
        att_sym = _extract_att_name(old, sch, en_reverse)
        att_rename[att_sym] = Symbol(new_name)
    end

    # Apply entity renames
    new_ens = Set{Symbol}()
    for en in sch.ens
        push!(new_ens, get(en_rename, en, en))
    end

    # Apply FK renames and entity renames to FK src/tgt, excluding removed FKs
    # Build reverse FK rename to handle removes that reference renamed FKs
    fk_reverse = Dict{Symbol,Symbol}(new_name => old_name for (old_name, new_name) in fk_rename)
    removed_fk_syms = Set{Symbol}()
    removed_fk_replacement = Dict{Symbol, Vector{Symbol}}()  # removed fk → replacement path FKs
    new_path_eqs = Set{Tuple{Symbol, Equation}}()
    for (old, replacement) in remove_fks
        fk_sym = _extract_fk_name(old, sch, en_reverse)
        # If not found directly, try through FK rename (remove may use renamed names)
        if !haskey(sch.fks, fk_sym)
            parts = split(old, ".")
            if length(parts) == 2
                fk_short = Symbol(parts[2])
                orig = get(fk_reverse, fk_short, fk_short)
                if haskey(sch.fks, orig)
                    fk_sym = orig
                end
            end
        end
        push!(removed_fk_syms, fk_sym)
        # Parse replacement path (e.g., "f" or "g1.g2")
        repl_parts = Symbol.(split(replacement, "."))
        removed_fk_replacement[fk_sym] = repl_parts
    end

    # Collect FK renames and detect duplicate target names
    fk_entries = Tuple{Symbol, Symbol, Symbol, Symbol}[]  # (new_fk, new_src, new_tgt, old_fk)
    for (fk, (src, tgt)) in sch.fks
        fk in removed_fk_syms && continue
        new_fk = get(fk_rename, fk, fk)
        new_src = get(en_rename, src, src)
        new_tgt = get(en_rename, tgt, tgt)
        push!(fk_entries, (new_fk, new_src, new_tgt, fk))
    end

    # Detect duplicate FK names and qualify them
    fk_name_counts = Dict{Symbol, Int}()
    for (new_fk, _, _, _) in fk_entries
        fk_name_counts[new_fk] = get(fk_name_counts, new_fk, 0) + 1
    end

    new_fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    fk_qualify_rename = Dict{Symbol, Symbol}()  # old_fk → qualified new_fk
    for (new_fk, new_src, new_tgt, old_fk) in fk_entries
        actual_fk = if fk_name_counts[new_fk] > 1
            qualified = Symbol(new_src, :__, new_fk)
            fk_qualify_rename[old_fk] = qualified
            qualified
        else
            new_fk
        end
        new_fks[actual_fk] = (new_src, new_tgt)
    end
    # Merge fk_qualify_rename into fk_rename for use in term renaming
    for (old_fk, qualified) in fk_qualify_rename
        fk_rename[old_fk] = qualified
    end

    removed_att_syms = Set{Symbol}()
    for (old, _) in remove_atts
        att_sym = _extract_att_name(old, sch, en_reverse)
        push!(removed_att_syms, att_sym)
    end

    # Collect att renames and detect duplicate target names
    att_entries = Tuple{Symbol, Symbol, Symbol, Symbol}[]  # (new_att, new_src, type, old_att)
    for (att, (src, ty)) in sch.atts
        att in removed_att_syms && continue
        new_att = get(att_rename, att, att)
        new_src = get(en_rename, src, src)
        push!(att_entries, (new_att, new_src, ty, att))
    end

    att_name_counts = Dict{Symbol, Int}()
    for (new_att, _, _, _) in att_entries
        att_name_counts[new_att] = get(att_name_counts, new_att, 0) + 1
    end

    new_atts = Dict{Symbol, Tuple{Symbol, Symbol}}()
    for (new_att, new_src, ty, old_att) in att_entries
        actual_att = if att_name_counts[new_att] > 1
            qualified = Symbol(new_src, :__, new_att)
            att_rename[old_att] = qualified
            qualified
        else
            new_att
        end
        new_atts[actual_att] = (new_src, ty)
    end

    # Build removed FK path substitutions with entity-context-aware resolution
    # Single-step removals get added to fk_rename; multi-step need path expansion
    removed_fk_paths = Dict{Symbol, Vector{Symbol}}()
    for (removed, repl_path) in removed_fk_replacement
        # Get source entity of removed FK (in renamed entity space)
        cur_entity = get(en_rename, sch.fks[removed][1], sch.fks[removed][1])

        # Resolve each FK in path using entity context to handle qualified names
        resolved = Symbol[]
        for fk in repl_path
            actual_fk = if haskey(new_fks, fk) && new_fks[fk][1] == cur_entity
                fk  # Direct match with correct source entity
            else
                # Try entity-qualified name: CurEntity__fk
                qualified = Symbol(cur_entity, :__, fk)
                if haskey(new_fks, qualified)
                    qualified
                else
                    # Fallback: try fk_rename
                    get(fk_rename, fk, fk)
                end
            end
            push!(resolved, actual_fk)
            # Advance current entity to target of this FK
            if haskey(new_fks, actual_fk)
                cur_entity = new_fks[actual_fk][2]
            end
        end

        if length(resolved) == 1
            fk_rename[removed] = resolved[1]
        else
            # Key by the renamed FK name (what _rename_eq_term produces),
            # not the original FK name
            renamed_fk = get(fk_rename, removed, removed)
            removed_fk_paths[renamed_fk] = resolved
        end
    end

    # Translate path and obs equations with renames and removal substitutions
    new_peqs = Set{Tuple{Symbol, Equation}}()
    for (en, eq) in sch.path_eqs
        new_en = get(en_rename, en, en)
        new_lhs = _subst_removed_fk_paths(_rename_eq_term(eq.lhs, en_rename, fk_rename, att_rename), removed_fk_paths)
        new_rhs = _subst_removed_fk_paths(_rename_eq_term(eq.rhs, en_rename, fk_rename, att_rename), removed_fk_paths)
        push!(new_peqs, (new_en, Equation(new_lhs, new_rhs)))
    end

    new_oeqs = Set{Tuple{Symbol, Equation}}()
    for (en, eq) in sch.obs_eqs
        new_en = get(en_rename, en, en)
        new_lhs = _subst_removed_fk_paths(_rename_eq_term(eq.lhs, en_rename, fk_rename, att_rename), removed_fk_paths)
        new_rhs = _subst_removed_fk_paths(_rename_eq_term(eq.rhs, en_rename, fk_rename, att_rename), removed_fk_paths)
        push!(new_oeqs, (new_en, Equation(new_lhs, new_rhs)))
    end

    # Build new schema
    opts = default_options()
    if !get_bool(opts, ALLOW_EMPTY_SORTS_UNSAFE)
        opts = to_options(opts, [("allow_empty_sorts_unsafe", "true")])
    end

    new_fk_by_name = _build_by_name(new_fks)
    new_att_by_name = _build_by_name(new_atts)

    sch_no_prover = CQLSchema(ts, new_ens, new_fks, new_atts,
                               new_peqs, new_oeqs,
                               (en, eq) -> error("Prover not initialized"),
                               new_fk_by_name, new_att_by_name,
                               collect(keys(new_fks)))

    col = schema_to_collage(sch_no_prover)
    prover = create_prover(col, opts)
    eq_fn = (en, eq) -> begin
        ctx = Ctx(Symbol("_unit") => Right(en))
        prover(ctx, eq)
    end

    new_schema = CQLSchema(ts, new_ens, new_fks, new_atts, new_peqs, new_oeqs, eq_fn,
                            new_fk_by_name, new_att_by_name,
                            collect(keys(new_fks)))

    # Update mappings with renames and removed FK substitutions
    new_mappings = Dict{String, CQLMapping}()
    for (sname, m) in base.mappings
        m_ens = Dict{Symbol, Symbol}()
        for (en, tgt) in m.ens
            m_ens[en] = get(en_rename, tgt, tgt)
        end
        m_fks = Dict{Symbol, CQLTerm}()
        for (fk, term) in m.fks
            renamed = _rename_eq_term(term, en_rename, fk_rename, att_rename)
            # Apply multi-step path substitutions for removed FKs
            m_fks[fk] = _subst_removed_fk_paths(renamed, removed_fk_paths)
        end
        m_atts = Dict{Symbol, CQLTerm}()
        for (att, term) in m.atts
            renamed = _rename_eq_term(term, en_rename, fk_rename, att_rename)
            m_atts[att] = _subst_removed_fk_paths(renamed, removed_fk_paths)
        end
        new_mappings[sname] = CQLMapping(m.src, new_schema, m_ens, m_fks, m_atts)
    end

    # Update canonical map with entity renames
    new_canonical = Dict{Symbol,Symbol}()
    for (k, v) in base.entity_canonical
        new_canonical[k] = get(en_rename, v, v)
    end
    SchemaColimitResult(new_schema, new_mappings, base.names, new_canonical)
end

"""Rename terms in equations based on rename maps."""
function _rename_eq_term(t::CQLTerm, en_rename, fk_rename, att_rename)::CQLTerm
    if t isa CQLVar
        t
    elseif t isa CQLFk
        new_fk = get(fk_rename, t.fk, t.fk)
        CQLFk(new_fk, _rename_eq_term(t.arg, en_rename, fk_rename, att_rename))
    elseif t isa CQLAtt
        new_att = get(att_rename, t.att, t.att)
        CQLAtt(new_att, _rename_eq_term(t.arg, en_rename, fk_rename, att_rename))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_rename_eq_term(a, en_rename, fk_rename, att_rename) for a in t.args])
    elseif t isa CQLGen
        t
    elseif t isa CQLSk
        t
    else
        t
    end
end

"""Substitute removed FK references with multi-step replacement paths.
E.g., if fk 'g' was removed with replacement 'g1.g2',
then CQLFk(:g, arg) becomes CQLFk(:g2, CQLFk(:g1, arg))."""
function _subst_removed_fk_paths(t::CQLTerm, paths::Dict{Symbol, Vector{Symbol}})::CQLTerm
    isempty(paths) && return t
    if t isa CQLFk
        inner = _subst_removed_fk_paths(t.arg, paths)
        if haskey(paths, t.fk)
            # Build path: fk_path = [fk1, fk2, ...] means fk_n(...(fk1(arg)))
            result = inner
            for fk in paths[t.fk]
                result = CQLFk(fk, result)
            end
            return result
        end
        return CQLFk(t.fk, inner)
    elseif t isa CQLAtt
        return CQLAtt(t.att, _subst_removed_fk_paths(t.arg, paths))
    elseif t isa CQLSym
        return CQLSym(t.sym, CQLTerm[_subst_removed_fk_paths(a, paths) for a in t.args])
    else
        return t
    end
end

"""Extract FK symbol from dotted name 'Entity.fk_name' in the context of a schema."""
function _extract_fk_name(dotted::String, sch::CQLSchema, en_reverse::Dict{Symbol,Symbol}=Dict{Symbol,Symbol}())::Symbol
    parts = split(dotted, ".")
    if length(parts) == 2
        # Entity.fk_name — search for matching FK
        en = Symbol(parts[1])
        # If entity name was renamed, map back to original name
        en_orig = get(en_reverse, en, en)
        fk_name = Symbol(parts[2])
        # Try direct match first
        haskey(sch.fks, fk_name) && return fk_name
        # Try matching with both new and original entity names
        for (fk, (src, _)) in sch.fks
            if (src == en || src == en_orig) && (fk == fk_name || endswith(string(fk), "_" * string(fk_name)))
                return fk
            end
        end
        return fk_name  # return as-is
    end
    Symbol(dotted)
end

"""Extract attribute symbol from dotted name 'Entity.att_name'."""
function _extract_att_name(dotted::String, sch::CQLSchema, en_reverse::Dict{Symbol,Symbol}=Dict{Symbol,Symbol}())::Symbol
    parts = split(dotted, ".")
    if length(parts) == 2
        en = Symbol(parts[1])
        en_orig = get(en_reverse, en, en)
        att_name = Symbol(parts[2])
        haskey(sch.atts, att_name) && return att_name
        for (att, (src, _)) in sch.atts
            if (src == en || src == en_orig)
                att_str = string(att)
                if att == att_name || endswith(att_str, "_" * string(att_name))
                    return att
                end
                # Handle entity-qualified names: Entity__suffix matches Entity_suffix
                dbl_idx = findfirst("__", att_str)
                if dbl_idx !== nothing
                    # Reconstruct with single underscore for comparison
                    single_form = att_str[1:first(dbl_idx)] * att_str[last(dbl_idx)+1:end]
                    if Symbol(single_form) == att_name
                        return att
                    end
                end
            end
        end
        return att_name
    end
    Symbol(dotted)
end
