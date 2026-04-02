# ============================================================================
# Pivot: instance -> schema + mapping
# ============================================================================

"""
Compute the pivot schema of an instance.

Given instance I on schema S, pivot(I) is a schema where:
- Each carrier element becomes an entity
- Each FK application becomes a FK in the pivot schema
- Each attribute becomes an attribute in the pivot schema
"""
function _pivot_schema(inst::CQLInstance)::CQLSchema
    alg = inst.algebra
    sch = inst.schema
    ts = sch.typeside

    pivot_ens = Set{Symbol}()
    pivot_fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    pivot_atts = Dict{Symbol, Tuple{Symbol, Symbol}}()
    pivot_path_eqs = Set{Tuple{Symbol, Equation}}()

    # Build entity for each carrier element
    for (en, elements) in alg.en
        for x in elements
            x_name = _element_name(alg, x)
            push!(pivot_ens, x_name)
        end
    end

    # Build FKs: for each original FK f: E1 -> E2, and each element x in E1,
    # create FK f: x -> f(x)
    fk_by_name = Dict{Symbol, Vector{Symbol}}()
    for (fk_name, (src_en, tgt_en)) in sch.fks
        for x in carrier(alg, src_en)
            y = eval_fk(alg, fk_name, x)
            x_name = _element_name(alg, x)
            y_name = _element_name(alg, y)
            # Qualify FK name with source entity to avoid collisions
            qualified_fk = Symbol(x_name, :__, fk_name)
            pivot_fks[qualified_fk] = (x_name, y_name)
            # Track plain FK name for resolution
            plain = fk_name
            if !haskey(fk_by_name, plain)
                fk_by_name[plain] = Symbol[]
            end
            push!(fk_by_name[plain], qualified_fk)
        end
    end

    # Build attributes: for each original att a: E -> T, and each element x in E,
    # create att a: x -> T
    att_by_name = Dict{Symbol, Vector{Symbol}}()
    for (att_name, (src_en, tgt_ty)) in sch.atts
        for x in carrier(alg, src_en)
            x_name = _element_name(alg, x)
            qualified_att = Symbol(x_name, :__, att_name)
            pivot_atts[qualified_att] = (x_name, tgt_ty)
            plain = att_name
            if !haskey(att_by_name, plain)
                att_by_name[plain] = Symbol[]
            end
            push!(att_by_name[plain], qualified_att)
        end
    end

    # Build path equations from FK composition
    # For each path equation forall x:E . f.g(x) = h(x) in the original schema,
    # we get for each element e in carrier(E): fk_g(fk_f(e)) = fk_h(e) in pivot schema
    for (en, eq) in sch.path_eqs
        for x in carrier(alg, en)
            x_name = _element_name(alg, x)
            lhs = _translate_pivot_path(alg, eq.lhs, x, x_name)
            rhs = _translate_pivot_path(alg, eq.rhs, x, x_name)
            if lhs !== nothing && rhs !== nothing
                push!(pivot_path_eqs, (x_name, Equation(lhs, rhs)))
            end
        end
    end

    eq_fn = (en, eq) -> eq.lhs == eq.rhs
    CQLSchema(ts, pivot_ens, pivot_fks, pivot_atts, pivot_path_eqs,
              Set{Tuple{Symbol,Equation}}(), eq_fn, fk_by_name, att_by_name, collect(keys(pivot_fks)))
end

"""Build the pseudo-quotient mapping: colimit_schema → quotient_schema.

For pseudo_quotient with entity_isomorphisms (e.g., p : S1.A -> S2.A),
creates a quotient schema that merges isomorphic entities and maps the
colimit schema to it. If no entity_isos, returns identity mapping."""
function _eval_get_pseudo(colimit::SchemaColimitResult, opts::CQLOptions)::CQLMapping
    if isempty(colimit.entity_isos)
        return identity_mapping(colimit.schema)
    end

    src_sch = colimit.schema
    ts = src_sch.typeside

    # Build union-find for entity merging based on entity_isos
    uf = Dict{Symbol, Symbol}()  # entity → representative
    for en in src_sch.ens
        uf[en] = en
    end

    function uf_find(x)
        while uf[x] != x
            uf[x] = uf[uf[x]]
            x = uf[x]
        end
        x
    end

    function uf_union(a, b)
        ra = uf_find(a)
        rb = uf_find(b)
        if ra != rb
            # Prefer shorter name as canonical
            if length(string(ra)) <= length(string(rb))
                uf[rb] = ra
            else
                uf[ra] = rb
            end
        end
    end

    # Parse entity_isos dotted names to find which entities to merge
    for (_, src_dotted, tgt_dotted) in colimit.entity_isos
        # Parse "SchemaName.EntityName" → prefixed entity
        src_en = _resolve_dotted_entity(src_dotted, colimit)
        tgt_en = _resolve_dotted_entity(tgt_dotted, colimit)
        if src_en !== nothing && tgt_en !== nothing
            uf_union(src_en, tgt_en)
        end
    end

    # Build canonical entity mapping
    en_map = Dict{Symbol, Symbol}()
    for en in src_sch.ens
        canon = uf_find(en)
        # Strip schema prefix from canonical name for cleaner output
        en_map[en] = _strip_schema_prefix(canon, colimit.names)
    end

    # Build quotient entity set
    quot_ens = Set{Symbol}(values(en_map))

    # Build quotient FKs (skip iso FKs and their inverses)
    iso_fk_names = Set{Symbol}()
    for (name, _, _) in colimit.entity_isos
        push!(iso_fk_names, Symbol(name))
        push!(iso_fk_names, Symbol(name, "_inv"))
    end

    quot_fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    fk_map = Dict{Symbol, CQLTerm}()  # src FK → dst FK term
    entity_fk_names = Dict{Symbol, Set{Symbol}}()  # entity → set of stripped FK names
    for (fk, (src, tgt)) in src_sch.fks
        if fk in iso_fk_names
            # Isomorphism FK maps to identity in quotient
            fk_map[fk] = CQLVar(Symbol("_unit"))
            continue
        end
        qsrc = en_map[src]
        qtgt = en_map[tgt]
        # Strip schema prefix from FK name
        stripped = _strip_schema_prefix(fk, colimit.names)
        # Also strip entity prefix from FK name
        stripped = _strip_pseudo_entity_prefix(stripped, qsrc)
        # Check for same-entity collision
        used = get!(entity_fk_names, qsrc, Set{Symbol}())
        if stripped in used
            stripped = fk  # keep full colimit name
        end
        push!(used, stripped)
        # Use Entity__stripped as dict key for cross-entity scoping
        qfk = Symbol(qsrc, "__", stripped)
        quot_fks[qfk] = (qsrc, qtgt)
        fk_map[fk] = CQLFk(qfk, CQLVar(Symbol("_unit")))
    end

    # Build attribute equivalences from obs_eqs.
    # Obs_eqs like "att1(x) = att2(iso_fk(x))" tell us att1 and att2 are the
    # same attribute after entity merging, and one should be eliminated.
    att_uf = Dict{Symbol, Symbol}()  # union-find for colimit att names
    for (att, _) in src_sch.atts
        att_uf[att] = att
    end
    function att_find(x)
        while att_uf[x] != x
            att_uf[x] = att_uf[att_uf[x]]
            x = att_uf[x]
        end
        x
    end

    for (_, eq) in src_sch.obs_eqs
        lhs_att = _extract_pseudo_att(eq.lhs, iso_fk_names)
        rhs_att = _extract_pseudo_att(eq.rhs, iso_fk_names)
        if lhs_att !== nothing && rhs_att !== nothing && lhs_att != rhs_att
            ra = att_find(lhs_att)
            rb = att_find(rhs_att)
            ra != rb && (att_uf[rb] = ra)  # prefer LHS as representative
        end
    end

    # Build quotient attributes using equivalence classes.
    # Attributes in the same equiv class (via obs_eqs) share one quotient name.
    # Use Entity__att format to scope names per entity (matching Java's per-entity
    # attribute scoping). _simplify_att_name in the dump script strips Entity__ prefixes.
    # For same-entity name collisions (e.g., two different IDs from merged schemas),
    # the second keeps its full colimit name (matching Java).
    quot_atts = Dict{Symbol, Tuple{Symbol, Symbol}}()
    att_map = Dict{Symbol, CQLTerm}()
    rep_to_qatt = Dict{Symbol, Symbol}()  # representative colimit att → quotient att name
    # Track stripped names per entity to detect same-entity collisions
    entity_att_names = Dict{Symbol, Set{Symbol}}()  # entity → set of stripped names used

    for (att, (src, ty)) in sort(collect(src_sch.atts), by=x->string(x[1]))
        qsrc = en_map[src]
        rep = att_find(att)

        if haskey(rep_to_qatt, rep)
            # Already have a quotient att for this equivalence class
            att_map[att] = CQLAtt(rep_to_qatt[rep], CQLVar(Symbol("_unit")))
            continue
        end

        # Compute stripped name (remove schema and entity prefixes)
        stripped = _strip_schema_prefix(att, colimit.names)
        stripped = _strip_pseudo_entity_prefix(stripped, qsrc)

        # Check for same-entity collision
        used = get!(entity_att_names, qsrc, Set{Symbol}())
        if stripped in used
            # Same-entity collision: keep full colimit name (e.g., Olog2Schema_Patient_ID)
            stripped = att
        end
        push!(used, stripped)

        # Use Entity__stripped as the dict key to avoid cross-entity collisions
        qatt = Symbol(qsrc, "__", stripped)

        rep_to_qatt[rep] = qatt
        quot_atts[qatt] = (qsrc, ty)
        att_map[att] = CQLAtt(qatt, CQLVar(Symbol("_unit")))
    end

    # Build quotient path equations
    quot_path_eqs = Set{Tuple{Symbol, Equation}}()
    for (en, eq) in src_sch.path_eqs
        qen = en_map[en]
        new_lhs = _translate_pseudo_term(eq.lhs, fk_map)
        new_rhs = _translate_pseudo_term(eq.rhs, fk_map)
        if new_lhs != new_rhs
            push!(quot_path_eqs, (qen, Equation(new_lhs, new_rhs)))
        end
    end

    # Build quotient obs equations
    quot_obs_eqs = Set{Tuple{Symbol, Equation}}()
    for (en, eq) in src_sch.obs_eqs
        qen = en_map[en]
        new_lhs = _translate_pseudo_type_term(eq.lhs, fk_map, att_map)
        new_rhs = _translate_pseudo_type_term(eq.rhs, fk_map, att_map)
        if new_lhs != new_rhs
            push!(quot_obs_eqs, (qen, Equation(new_lhs, new_rhs)))
        end
    end

    quot_fk_by_name = _build_pseudo_by_name(quot_fks)
    quot_att_by_name = _build_pseudo_by_name(quot_atts)

    eq_fn = (en, eq) -> eq.lhs == eq.rhs  # simple equality for now
    quot_sch = CQLSchema(ts, quot_ens, quot_fks, quot_atts,
                          quot_path_eqs, quot_obs_eqs, eq_fn,
                          quot_fk_by_name, quot_att_by_name,
                          collect(keys(quot_fks)))

    CQLMapping(src_sch, quot_sch, en_map, fk_map, att_map)
end

"""Extract attribute name from an obs_eq term that is att(fk_chain(var)) where
all FKs in the chain are isomorphism FKs (which become identity in quotient)."""
function _extract_pseudo_att(t::CQLTerm, iso_fk_names::Set{Symbol})::Union{Symbol, Nothing}
    t isa CQLAtt || return nothing
    inner = t.arg
    while inner isa CQLFk
        inner.fk in iso_fk_names || return nothing
        inner = inner.arg
    end
    inner isa CQLVar ? t.att : nothing
end

"""Resolve a dotted entity name like 'Olog1Schema.Patient' to a prefixed entity in the colimit."""
function _resolve_dotted_entity(dotted::String, colimit::SchemaColimitResult)::Union{Symbol, Nothing}
    parts = split(dotted, ".")
    if length(parts) == 2
        prefixed = Symbol(parts[1], "_", parts[2])
        prefixed in colimit.schema.ens && return prefixed
    end
    nothing
end

"""Strip schema prefix from a symbol name. E.g., Olog1Schema_Patient → Patient."""
function _strip_schema_prefix(name::Symbol, schema_names::Vector{String})::Symbol
    s = string(name)
    for sn in schema_names
        prefix = sn * "_"
        if startswith(s, prefix)
            # Strip the first matching prefix
            stripped = s[length(prefix)+1:end]
            return Symbol(stripped)
        end
    end
    name
end

"""Strip entity prefix from an attribute/FK name if it matches.
E.g., Observation_ID → ID when entity is Observation.
Only strips if entity name has >= 3 chars (avoids false positives with short entity names
like G, P, T which may have attributes like G_att that are NOT entity-prefixed)."""
function _strip_pseudo_entity_prefix(name::Symbol, entity::Symbol)::Symbol
    s = string(name)
    en = string(entity)
    length(en) < 3 && return name  # don't strip short entity prefixes
    prefix = en * "_"
    if startswith(s, prefix) && length(s) > length(prefix)
        stripped = s[length(prefix)+1:end]
        # Don't strip if result starts with _ (would create invalid name)
        startswith(stripped, '_') && return name
        return Symbol(stripped)
    end
    name
end

"""Translate an entity-side term through the pseudo-quotient mapping."""
function _translate_pseudo_term(t::CQLTerm, fk_map::Dict{Symbol, CQLTerm})::CQLTerm
    if t isa CQLVar
        t
    elseif t isa CQLFk
        mapped = fk_map[t.fk]
        if mapped isa CQLVar
            # Identity FK (iso) — skip it
            _translate_pseudo_term(t.arg, fk_map)
        elseif mapped isa CQLFk
            CQLFk(mapped.fk, _translate_pseudo_term(t.arg, fk_map))
        else
            t
        end
    else
        t
    end
end

"""Translate a type-side term through the pseudo-quotient mapping."""
function _translate_pseudo_type_term(t::CQLTerm, fk_map::Dict{Symbol, CQLTerm}, att_map::Dict{Symbol, CQLTerm})::CQLTerm
    if t isa CQLAtt
        mapped = att_map[t.att]
        if mapped isa CQLAtt
            CQLAtt(mapped.att, _translate_pseudo_term(t.arg, fk_map))
        else
            t
        end
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_translate_pseudo_type_term(a, fk_map, att_map) for a in t.args])
    else
        t
    end
end

function _build_pseudo_by_name(dict)
    by_name = Dict{Symbol, Vector{Symbol}}()
    for name in keys(dict)
        s = string(name)
        # Extract short name (last part after last _)
        parts = split(s, "_")
        if length(parts) > 1
            short = Symbol(parts[end])
            push!(get!(by_name, short, Symbol[]), name)
        end
    end
    by_name
end

"""Compute the pivot mapping: pivot(I) -> S.

Maps each element entity back to its original entity,
and each qualified FK/att back to the original FK/att."""
function _pivot_mapping(inst::CQLInstance)::CQLMapping
    alg = inst.algebra
    sch = inst.schema
    pivot_sch = _pivot_schema(inst)

    ens = Dict{Symbol, Symbol}()
    fks_map = Dict{Symbol, CQLTerm}()
    atts_map = Dict{Symbol, CQLTerm}()

    # Map each element entity to its original entity
    for (en, elements) in alg.en
        for x in elements
            x_name = _element_name(alg, x)
            ens[x_name] = en
        end
    end

    # Map each qualified FK to identity path through the original FK
    for (qfk, (src_elem, tgt_elem)) in pivot_sch.fks
        # qfk = elem__fk_name, extract the original fk_name
        s = string(qfk)
        parts = split(s, "__")
        orig_fk = Symbol(parts[end])
        fks_map[qfk] = CQLFk(orig_fk, CQLVar(:_unit))
    end

    # Map each qualified att to the original attribute
    for (qatt, (src_elem, tgt_ty)) in pivot_sch.atts
        s = string(qatt)
        parts = split(s, "__")
        orig_att = Symbol(parts[end])
        atts_map[qatt] = CQLAtt(orig_att, CQLVar(:_unit))
    end

    CQLMapping(pivot_sch, sch, ens, fks_map, atts_map)
end

"""Get a stable name for an algebra carrier element."""
function _element_name(alg::Algebra, x)::Symbol
    t = repr_x(alg, x)
    if t isa CQLGen
        return t.gen
    else
        return Symbol(string(t))
    end
end

"""Translate a path equation term to pivot schema FKs."""
function _translate_pivot_path(alg::Algebra, t::CQLTerm, base_x, base_name::Symbol)::Union{CQLTerm, Nothing}
    if t isa CQLVar
        return CQLVar(:_unit)
    elseif t isa CQLFk
        inner_term = _translate_pivot_path(alg, t.arg, base_x, base_name)
        inner_term === nothing && return nothing
        # Evaluate the inner term to get the element it refers to
        inner_elem = _eval_pivot_inner(alg, t.arg, base_x)
        inner_elem === nothing && return nothing
        inner_name = _element_name(alg, inner_elem)
        qfk = Symbol(inner_name, :__, t.fk)
        return CQLFk(qfk, inner_term)
    else
        return nothing
    end
end

"""Evaluate an entity-side term starting from a base element."""
function _eval_pivot_inner(alg::Algebra, t::CQLTerm, base_x)
    if t isa CQLVar
        return base_x
    elseif t isa CQLFk
        inner = _eval_pivot_inner(alg, t.arg, base_x)
        inner === nothing && return nothing
        return eval_fk(alg, t.fk, inner)
    else
        return nothing
    end
end

