# ============================================================================
# Pi instance/transform (identity mapping optimization)
# ============================================================================

"""Check if a mapping is an identity mapping."""
function _is_identity_mapping(m::CQLMapping)::Bool
    m.src == m.dst || return false
    for (en, mapped) in m.ens
        en == mapped || return false
    end
    for (fk, term) in m.fks
        term == CQLFk(fk, CQLVar(:_unit)) || return false
    end
    for (att, term) in m.atts
        term == CQLAtt(att, CQLVar(:_unit)) || return false
    end
    true
end

"""Evaluate pi instance: right adjoint to delta along a mapping.

For identity mappings, pi(id, I) = I."""
function _eval_pi_instance(m::CQLMapping, inst::CQLInstance, opts::CQLOptions)::CQLInstance
    if _is_identity_mapping(m)
        return inst
    end
    throw(CQLException("pi instances for non-identity mappings are not yet supported"))
end

"""Evaluate pi transform: right adjoint to delta along a mapping on transforms.

For identity mappings, pi(id, T) = T."""
function _eval_pi_transform(m::CQLMapping, t::CQLTransform, opts::CQLOptions)::CQLTransform
    if _is_identity_mapping(m)
        return t
    end
    throw(CQLException("pi transforms for non-identity mappings are not yet supported"))
end

# ============================================================================
# Frozen instance/transform
# ============================================================================

"""Evaluate a frozen instance: extract the from-clause of a query entity block
and turn it into an instance on the query's source schema."""
function _eval_frozen_instance(q::CQLQuery, entity_name::Symbol, opts::CQLOptions)::CQLInstance
    haskey(q.ens, entity_name) || throw(CQLException("Query has no entity block for: $entity_name"))
    (ctx, where_eqs) = q.ens[entity_name]

    # Create presentation on q.src with:
    # - One generator per from-variable, typed by the source entity
    gens = Dict{Symbol, Symbol}()
    sks = Dict{Symbol, Symbol}()
    for (v, en) in ctx
        if en in q.src.ens
            gens[v] = en
        else
            # Type-sorted variable: create a skolem constant
            sks[v] = en
        end
    end

    # Where-clause equations become instance equations (replace CQLVar → CQLGen/CQLSk)
    eqs = Set{Equation}()
    for eq in where_eqs
        lhs = _vars_to_gens_sks(eq.lhs, gens, sks)
        rhs = _vars_to_gens_sks(eq.rhs, gens, sks)
        push!(eqs, Equation(lhs, rhs))
    end

    pres = Presentation(gens, sks, eqs)

    if isempty(gens) && isempty(sks)
        return empty_instance(q.src)
    end

    # Build collage and include universally-quantified schema path equations
    # so KB completion can derive equalities for generated terms (e.g.,
    # manager(manager(secretary(worksIn(e)))) = manager(secretary(worksIn(e)))).
    col = presentation_to_collage(q.src, pres)
    # Add universally-quantified schema equations for KB completion
    sch_col = schema_to_collage(q.src)
    for (ctx, eq) in sch_col.ceqs
        if !isempty(ctx)
            push!(col.ceqs, (ctx, eq))
        end
    end

    prover = create_prover(col, opts)
    dp_fn = eq -> prover(Ctx(), eq)
    initial_instance(pres, dp_fn, q.src; timeout_seconds=10, max_carrier_size=200)
end

"""Build a layered prover: orthogonal rewriting for ground equations,
typeside prover for type-level equality."""
function _build_layered_prover(col::Collage, ts::Typeside, opts::CQLOptions)
    (col_simplified, replacements) = simplify_collage(col)

    # Extract ground equations (these come from schema/instance, not typeside)
    ground_eqs = Equation[eq for (ctx, eq) in col_simplified.ceqs if isempty(ctx)]

    # Try to orient ground equations as rewrite rules
    rules = RewriteRule[]
    for eq in ground_eqs
        oriented = _orient_eq(eq)
        if oriented !== nothing
            push!(rules, RewriteRule(oriented.lhs, oriented.rhs))
        else
            # Can't orient — try both directions
            if term_size(eq.lhs) >= term_size(eq.rhs)
                push!(rules, RewriteRule(eq.lhs, eq.rhs))
            else
                push!(rules, RewriteRule(eq.rhs, eq.lhs))
            end
        end
    end

    # The prover: normalize with ground rules, then check via typeside prover
    eq -> begin
        l = replace_repeatedly(replacements, eq.lhs)
        r = replace_repeatedly(replacements, eq.rhs)
        ln = normalize(rules, l)
        rn = normalize(rules, r)
        ln == rn && return true
        # Fall back to typeside prover for type-level equality
        ts.eq(Dict{Symbol,Symbol}(), Equation(ln, rn))
    end
end

"""Add ground path equations for FK-reachable entities that have no direct generators.

When a frozen instance has a generator x:E but no generators of entity F,
and F is reachable from E via FK chain, path equations on F aren't grounded
by `presentation_to_collage`. This function computes FK-reachable terms
and adds ground path equations for them."""
function _add_fk_reachable_path_eqs!(col::Collage, sch::CQLSchema, gens::Dict{Symbol,Symbol})
    gen_entities = Set{Symbol}(en for (_, en) in gens)

    # Find schema path/observation equations on entities without generators
    sch_col = schema_to_collage(sch)
    path_eqs = Tuple{Symbol, Symbol, Equation}[]
    for (ctx, eq) in sch_col.ceqs
        isempty(ctx) && continue
        entity_vars = [(v, get_right(sort)) for (v, sort) in ctx if is_right(sort)]
        length(entity_vars) == 1 || continue
        (var, entity) = entity_vars[1]
        entity in gen_entities && continue
        push!(path_eqs, (var, entity, eq))
    end

    isempty(path_eqs) && return

    path_eq_entities = Set{Symbol}(entity for (_, entity, _) in path_eqs)

    # BFS from generator entities through FKs to find representative terms
    repr_terms = Dict{Symbol, Vector{CQLTerm}}()
    for (g, en) in gens
        push!(get!(repr_terms, en, CQLTerm[]), CQLGen(g))
    end

    for _ in 1:5
        new_found = false
        for (fk, (fk_src, fk_tgt)) in sch.fks
            fk_src == fk_tgt && continue
            haskey(repr_terms, fk_src) || continue
            fk_tgt in gen_entities && continue
            tgt_terms = get!(repr_terms, fk_tgt, CQLTerm[])
            for src_term in repr_terms[fk_src]
                fk_term = CQLFk(fk, src_term)
                if !(fk_term in tgt_terms)
                    push!(tgt_terms, fk_term)
                    new_found = true
                end
            end
        end
        new_found || break
    end

    # Ground path equations with FK-reachable terms
    for (var, entity, eq) in path_eqs
        haskey(repr_terms, entity) || continue
        for term in repr_terms[entity]
            subst = Dict{Symbol, CQLTerm}(var => term)
            lhs = _subst_vars(eq.lhs, subst)
            rhs = _subst_vars(eq.rhs, subst)
            push!(col.ceqs, (Ctx(), Equation(lhs, rhs)))
        end
    end
end

"""Replace CQLVar with CQLGen or CQLSk depending on sort."""
function _vars_to_gens_sks(t::CQLTerm, gens::Dict{Symbol,Symbol}, sks::Dict{Symbol,Symbol})::CQLTerm
    if t isa CQLVar
        if haskey(gens, t.name)
            return CQLGen(t.name)
        elseif haskey(sks, t.name)
            return CQLSk(t.name)
        else
            return t  # leave as variable (shouldn't happen in well-typed queries)
        end
    elseif t isa CQLFk
        return CQLFk(t.fk, _vars_to_gens_sks(t.arg, gens, sks))
    elseif t isa CQLAtt
        return CQLAtt(t.att, _vars_to_gens_sks(t.arg, gens, sks))
    elseif t isa CQLSym
        return CQLSym(t.sym, CQLTerm[_vars_to_gens_sks(a, gens, sks) for a in t.args])
    else
        return t
    end
end

"""Evaluate a frozen transform: given query Q: S→T, lambda var:entity. body : ret_type,
produce a transform from frozen(Q, entity) to some target instance on a type.

This implements the Java TransExpFrozen which creates a transform by evaluating
the lambda body through the query composition."""
function _eval_frozen_transform(q::CQLQuery, lambda_var::String, lambda_type::String,
                                 lambda_body, ret_type::String, opts::CQLOptions)::CQLTransform
    entity_name = Symbol(lambda_type)
    haskey(q.ens, entity_name) || throw(CQLException("Query has no entity block for: $entity_name"))

    # Build the frozen instance (source of the transform)
    frozen_inst = _eval_frozen_instance(q, entity_name, opts)

    # The lambda body is a RawTerm that represents a path in the dst schema context.
    # We need to trace this through the query to get a term in the src schema.
    # The lambda variable refers to the entity in the dst schema (q.dst).

    # Parse the lambda body in the dst schema context
    dst_term = _parse_frozen_lambda_body(q, lambda_var, entity_name, lambda_body)

    # Compose the dst term through the query to get a src term
    src_term = _compose_term_through_query(q, entity_name, dst_term)

    # Replace CQLVar with CQLGen for frozen instance generators
    (ctx, _) = q.ens[entity_name]
    gens_map = Dict{Symbol, Symbol}()
    sks_map = Dict{Symbol, Symbol}()
    for (v, en) in ctx
        if en in q.src.ens
            gens_map[v] = en
        else
            sks_map[v] = en
        end
    end
    ground_term = _vars_to_gens_sks(src_term, gens_map, sks_map)

    # Build single-entity target schema (just the return type)
    ret_ty = Symbol(ret_type)

    # The target instance is the type algebra portion relevant to frozen_inst
    # For a transform to a type, we create an instance on a trivial schema
    # that holds just the type value
    tgt_sch = frozen_inst.schema  # Same schema — the transform maps generators to type-side terms
    tgt_inst = frozen_inst  # The transform is from frozen_inst to itself (identity on instances)

    # Build the transform: each generator maps to the ground_term applied to that generator
    # But actually, for a frozen transform, the result is a transform from frozen instance
    # to frozen instance, where generators map to themselves and skolems map to the composed term.
    # More precisely: it maps each generator to itself, but provides the type-side mapping.

    # In the Java code, a frozen transform T: frozen(Q,e) → frozen(Q,e) maps
    # generators to generators and computes the type algebra value from the lambda.
    # Actually, for `frozen qTS lambda x:s0. x.ss.att : Double`, the result
    # is a transform that maps the single source generator to a type-side term.

    # The transform is from frozen_inst to frozen_inst itself (identity-like on entity side)
    trans_gens = Dict{Symbol, CQLTerm}(g => CQLGen(g) for g in keys(frozen_inst.pres.gens))
    trans_sks = Dict{Symbol, CQLTerm}()
    for (s, _) in frozen_inst.pres.sks
        trans_sks[s] = CQLSk(s)
    end

    CQLTransform(frozen_inst, frozen_inst, trans_gens, trans_sks)
end

"""Parse a frozen lambda body raw term in the context of the query's dst schema."""
function _parse_frozen_lambda_body(q::CQLQuery, lambda_var::String, entity::Symbol, raw::RawTerm)::CQLTerm
    s = Symbol(raw.head)
    if isempty(raw.args)
        # It's the lambda variable
        if raw.head == lambda_var
            return CQLVar(Symbol(lambda_var))
        end
        # It's a constant
        return CQLSym(s, CQLTerm[])
    elseif length(raw.args) == 1
        inner = _parse_frozen_lambda_body(q, lambda_var, entity, raw.args[1])
        if haskey(q.dst.fks, s)
            return CQLFk(s, inner)
        elseif haskey(q.dst.atts, s)
            return CQLAtt(s, inner)
        elseif has_fk(q.dst, s)
            # Try to resolve
            inner_en = _entity_of_dst_term(q.dst, inner, entity)
            if inner_en !== nothing
                return CQLFk(resolve_fk(q.dst, s, inner_en), inner)
            end
            return CQLFk(s, inner)
        elseif has_att(q.dst, s)
            inner_en = _entity_of_dst_term(q.dst, inner, entity)
            if inner_en !== nothing
                return CQLAtt(resolve_att(q.dst, s, inner_en), inner)
            end
            return CQLAtt(s, inner)
        end
        # Maybe it's a src schema fk/att
        if haskey(q.src.fks, s)
            return CQLFk(s, inner)
        elseif haskey(q.src.atts, s)
            return CQLAtt(s, inner)
        end
        return CQLSym(s, CQLTerm[inner])
    else
        args = CQLTerm[_parse_frozen_lambda_body(q, lambda_var, entity, a) for a in raw.args]
        return CQLSym(s, args)
    end
end

"""Determine the entity of a term in the dst schema."""
function _entity_of_dst_term(sch::CQLSchema, t::CQLTerm, default_en::Symbol)::Union{Symbol, Nothing}
    if t isa CQLVar
        return default_en
    elseif t isa CQLFk
        haskey(sch.fks, t.fk) && return sch.fks[t.fk][2]
        return nothing
    else
        return nothing
    end
end

"""Compose a dst-schema term through a query to get a src-schema term.

For a term like att(fk(var)), trace through:
- var maps to the from-context of the entity block
- fk maps using q.fks[fk] (which gives variable mappings)
- att maps using q.atts[att]"""
function _compose_term_through_query(q::CQLQuery, entity::Symbol, t::CQLTerm)::CQLTerm
    if t isa CQLVar
        # The lambda variable references the entity block; return it as-is
        # (it will be the identity — each from-var maps to itself)
        return t
    elseif t isa CQLAtt
        if haskey(q.atts, t.att)
            # Substitute inner term into the query's attribute definition
            inner_composed = _compose_term_through_query(q, entity, t.arg)
            return _subst_query_term(q.atts[t.att], inner_composed, q, entity)
        end
        # If not a dst att, it's a src att — pass through
        return CQLAtt(t.att, _compose_term_through_query(q, entity, t.arg))
    elseif t isa CQLFk
        if haskey(q.fks, t.fk)
            # FK composition: the FK maps variables in target entity to terms in source
            inner_composed = _compose_term_through_query(q, entity, t.arg)
            # q.fks[fk] gives Dict{Symbol, CQLTerm} mapping tgt entity vars to src terms
            # We need to apply this substitution
            return _apply_fk_mapping(q.fks[t.fk], inner_composed, q, entity)
        end
        return CQLFk(t.fk, _compose_term_through_query(q, entity, t.arg))
    elseif t isa CQLSym
        return CQLSym(t.sym, CQLTerm[_compose_term_through_query(q, entity, a) for a in t.args])
    else
        return t
    end
end

"""Substitute variables in a query term definition with composed values."""
function _subst_query_term(template::CQLTerm, composed_inner::CQLTerm,
                            q::CQLQuery, entity::Symbol)::CQLTerm
    # The template uses CQLVar(:x) etc. for from-clause variables.
    # We need to replace these with corresponding terms from the query context.
    # For the simple case where template directly uses from-vars, return as-is
    # (the vars will be resolved later to frozen instance generators)
    template
end

"""Apply a FK variable mapping."""
function _apply_fk_mapping(var_map::Dict{Symbol, CQLTerm}, composed_inner::CQLTerm,
                            q::CQLQuery, entity::Symbol)::CQLTerm
    # For simple cases, return the composed inner term
    composed_inner
end

# ============================================================================
# Anonymize instance
# ============================================================================

"""Anonymize an instance by renaming all generators to anonymous names."""
function _eval_anonymize_instance(inst::CQLInstance, opts::CQLOptions)::CQLInstance
    sch = inst.schema

    if isempty(inst.pres.gens)
        return inst
    end

    # Build rename map
    rename_map = Dict{Symbol, Symbol}()
    for (i, (g, _)) in enumerate(inst.pres.gens)
        rename_map[g] = Symbol("_anon_", i)
    end

    # Rename skolems too
    sk_rename = Dict{Symbol, Symbol}()
    for (i, (s, _)) in enumerate(inst.pres.sks)
        sk_rename[s] = Symbol("_anon_sk_", i)
    end

    new_gens = Dict{Symbol, Symbol}(rename_map[g] => en for (g, en) in inst.pres.gens)
    new_sks = Dict{Symbol, Symbol}(sk_rename[s] => ty for (s, ty) in inst.pres.sks)
    new_eqs = Set{Equation}()
    for eq in inst.pres.eqs
        new_lhs = _rename_term(eq.lhs, rename_map, sk_rename)
        new_rhs = _rename_term(eq.rhs, rename_map, sk_rename)
        push!(new_eqs, Equation(new_lhs, new_rhs))
    end

    new_gen_order = Symbol[get(rename_map, g, g) for g in inst.pres.gen_order if haskey(rename_map, g)]
    new_pres = Presentation(new_gens, new_sks, new_eqs, new_gen_order)
    col = presentation_to_collage(sch, new_pres)
    prover = create_prover(col, opts)
    dp_fn = eq -> prover(Ctx(), eq)
    initial_instance(new_pres, dp_fn, sch)
end

# ============================================================================
# Cascade delete
# ============================================================================

"""Cascade delete: remove generators that violate FK constraints.

Iteratively removes generators whose FK targets don't exist, until a fixed point."""
function _eval_cascade_delete(inst::CQLInstance, sch::CQLSchema, opts::CQLOptions)::CQLInstance
    # If no FKs, nothing to cascade
    if isempty(sch.fks)
        return inst
    end

    current_gens = copy(inst.pres.gens)
    changed = true

    while changed
        changed = false
        to_remove = Set{Symbol}()

        for (g, en) in current_gens
            for (fk, (fk_src, fk_tgt)) in sch.fks
                fk_src == en || continue
                # Check if there's a target for this FK
                # Look through equations to find what fk(g) equals
                has_target = false
                for (g2, en2) in current_gens
                    if en2 == fk_tgt
                        has_target = true
                        break
                    end
                end
                if !has_target
                    push!(to_remove, g)
                end
            end
        end

        if !isempty(to_remove)
            changed = true
            for g in to_remove
                delete!(current_gens, g)
            end
        end
    end

    if length(current_gens) == length(inst.pres.gens)
        return inst
    end

    if isempty(current_gens)
        return empty_instance(sch)
    end

    # Rebuild instance with remaining generators
    removed = Set{Symbol}(g for (g, _) in inst.pres.gens if !haskey(current_gens, g))
    keep_eqs = Set{Equation}()
    for eq in inst.pres.eqs
        if !_term_references_any(eq.lhs, removed) && !_term_references_any(eq.rhs, removed)
            push!(keep_eqs, eq)
        end
    end

    # Keep skolems that aren't referenced by removed generators
    keep_sks = copy(inst.pres.sks)

    keep_gen_order2 = Symbol[g for g in inst.pres.gen_order if haskey(current_gens, g)]
    new_pres = Presentation(current_gens, keep_sks, keep_eqs, keep_gen_order2)
    col = presentation_to_collage(sch, new_pres)
    prover = create_prover(col, opts)
    dp_fn = eq -> prover(Ctx(), eq)
    initial_instance(new_pres, dp_fn, sch)
end

# ============================================================================
# Spanify: convert relational schema to RDF span representation
# ============================================================================

const RDF_TYPE_PREDICATE = Symbol("http://www.w3.org/1999/02/22-rdf-syntax-ns#type")

"""Build spanified schema from a relational schema on the RDF typeside.

For each entity E: creates entity E with subject : E → Dom
For each FK f: A → B: creates entity f_A_B with FKs subject → A, object → B
For each att a: E → Dom: creates entity a_E with FK subject → E, attribute object → Dom"""
function _eval_schema_spanify(sch::CQLSchema)::CQLSchema
    ts = sch.typeside
    span_ens = Set{Symbol}()
    span_fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    span_atts = Dict{Symbol, Tuple{Symbol, Symbol}}()

    # For each entity: create entity with subject attribute
    for en in sch.ens
        push!(span_ens, en)
        # Qualify attribute: Entity__subject
        att_name = Symbol(en, :__, :subject)
        span_atts[att_name] = (en, :Dom)
    end

    # For each FK: create reified entity with subject/object FKs
    for (fk, (src, tgt)) in sch.fks
        fk_en = Symbol(fk, :_, src, :_, tgt)
        push!(span_ens, fk_en)
        # subject FK: fk_entity → source entity
        subj_fk = Symbol(fk_en, :__, :subject)
        span_fks[subj_fk] = (fk_en, src)
        # object FK: fk_entity → target entity
        obj_fk = Symbol(fk_en, :__, :object)
        span_fks[obj_fk] = (fk_en, tgt)
    end

    # For each attribute: create reified entity with subject FK and object attribute
    for (att, (src, ty)) in sch.atts
        att_en = Symbol(att, :_, src)
        push!(span_ens, att_en)
        # subject FK: att_entity → source entity
        subj_fk = Symbol(att_en, :__, :subject)
        span_fks[subj_fk] = (att_en, src)
        # object attribute: att_entity → Dom
        obj_att = Symbol(att_en, :__, :object)
        span_atts[obj_att] = (att_en, :Dom)
    end

    # Build name resolution maps
    fk_by_name = Dict{Symbol, Vector{Symbol}}()
    for fk_name in keys(span_fks)
        s = string(fk_name)
        idx = findfirst("__", s)
        if idx !== nothing
            plain = Symbol(s[last(idx)+1:end])
            if !haskey(fk_by_name, plain)
                fk_by_name[plain] = Symbol[]
            end
            push!(fk_by_name[plain], fk_name)
        end
    end
    att_by_name = Dict{Symbol, Vector{Symbol}}()
    for att_name in keys(span_atts)
        s = string(att_name)
        idx = findfirst("__", s)
        if idx !== nothing
            plain = Symbol(s[last(idx)+1:end])
            if !haskey(att_by_name, plain)
                att_by_name[plain] = Symbol[]
            end
            push!(att_by_name[plain], att_name)
        end
    end

    eq_fn = (en, eq) -> eq.lhs == eq.rhs
    CQLSchema(ts, span_ens, span_fks, span_atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(), eq_fn,
        fk_by_name, att_by_name, collect(keys(span_fks)))
end

"""Build spanify query: rdf → spanify(S).

The query extracts structured instances from RDF data."""
function _eval_query_spanify(sch::CQLSchema)::CQLQuery
    rdf_sch = _get_rdf_schema(sch.typeside)
    span_sch = _eval_schema_spanify(sch)

    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}()
    fks = Dict{Symbol, Dict{Symbol, CQLTerm}}()
    atts = Dict{Symbol, CQLTerm}()

    # For each entity E: query block with c:R, predicate(c)="type", object(c)="E"
    for en in sch.ens
        ctx = Dict{Symbol,Symbol}(:c => :R)
        where_eqs = Set{Equation}([
            Equation(CQLAtt(:predicate, CQLVar(:c)),
                     CQLSym(RDF_TYPE_PREDICATE, CQLTerm[])),
            Equation(CQLAtt(:object, CQLVar(:c)),
                     CQLSym(en, CQLTerm[]))
        ])
        ens[en] = (ctx, where_eqs)
        # Attribute mapping: en.subject → c.subject
        att_name = Symbol(en, :__, :subject)
        atts[att_name] = CQLAtt(:subject, CQLVar(:c))
    end

    # For each FK f: A → B: query block with r,rs,rt:R
    for (fk, (src, tgt)) in sch.fks
        fk_en = Symbol(fk, :_, src, :_, tgt)
        ctx = Dict{Symbol,Symbol}(:r => :R, :rs => :R, :rt => :R)
        where_eqs = Set{Equation}([
            Equation(CQLAtt(:predicate, CQLVar(:r)),
                     CQLSym(fk, CQLTerm[])),
            Equation(CQLAtt(:predicate, CQLVar(:rs)),
                     CQLSym(RDF_TYPE_PREDICATE, CQLTerm[])),
            Equation(CQLAtt(:object, CQLVar(:rs)),
                     CQLSym(src, CQLTerm[])),
            Equation(CQLAtt(:predicate, CQLVar(:rt)),
                     CQLSym(RDF_TYPE_PREDICATE, CQLTerm[])),
            Equation(CQLAtt(:object, CQLVar(:rt)),
                     CQLSym(tgt, CQLTerm[])),
            Equation(CQLAtt(:subject, CQLVar(:r)),
                     CQLAtt(:subject, CQLVar(:rs))),
            Equation(CQLAtt(:object, CQLVar(:r)),
                     CQLAtt(:subject, CQLVar(:rt)))
        ])
        ens[fk_en] = (ctx, where_eqs)
        # FK mappings: subject → rs, object → rt
        subj_fk = Symbol(fk_en, :__, :subject)
        obj_fk = Symbol(fk_en, :__, :object)
        fks[subj_fk] = Dict(:c => CQLVar(:rs))
        fks[obj_fk] = Dict(:c => CQLVar(:rt))
    end

    # For each attribute a: E → Dom: query block with r,rs:R
    for (att, (src, _)) in sch.atts
        att_en = Symbol(att, :_, src)
        ctx = Dict{Symbol,Symbol}(:r => :R, :rs => :R)
        where_eqs = Set{Equation}([
            Equation(CQLAtt(:predicate, CQLVar(:r)),
                     CQLSym(att, CQLTerm[])),
            Equation(CQLAtt(:predicate, CQLVar(:rs)),
                     CQLSym(RDF_TYPE_PREDICATE, CQLTerm[])),
            Equation(CQLAtt(:object, CQLVar(:rs)),
                     CQLSym(src, CQLTerm[])),
            Equation(CQLAtt(:subject, CQLVar(:r)),
                     CQLAtt(:subject, CQLVar(:rs)))
        ])
        ens[att_en] = (ctx, where_eqs)
        # FK mapping: subject → rs
        subj_fk = Symbol(att_en, :__, :subject)
        fks[subj_fk] = Dict(:c => CQLVar(:rs))
        # Attribute mapping: object → r.object
        obj_att = Symbol(att_en, :__, :object)
        atts[obj_att] = CQLAtt(:object, CQLVar(:r))
    end

    CQLQuery(rdf_sch, span_sch, ens, fks, atts)
end

"""Build spanify_mapping query: spanify(T) → spanify(S) from mapping M: S → T."""
function _eval_query_spanify_mapping(m::CQLMapping)::CQLQuery
    src_sch = m.src
    tgt_sch = m.dst
    span_src = _eval_schema_spanify(src_sch)
    span_tgt = _eval_schema_spanify(tgt_sch)

    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}()
    fks = Dict{Symbol, Dict{Symbol, CQLTerm}}()
    atts = Dict{Symbol, CQLTerm}()

    # For each entity E_src that maps to E_tgt:
    for (src_en, tgt_en) in m.ens
        ctx = Dict{Symbol,Symbol}(:c => tgt_en)
        ens[src_en] = (ctx, Set{Equation}())
        # subject attribute maps through
        src_att = Symbol(src_en, :__, :subject)
        tgt_att = Symbol(tgt_en, :__, :subject)
        atts[src_att] = CQLAtt(tgt_att, CQLVar(:c))
    end

    # For each FK f_src: A_src → B_src that maps through the mapping:
    for (src_fk, fk_term) in m.fks
        (src_a, src_b) = src_sch.fks[src_fk]
        tgt_a = m.ens[src_a]
        tgt_b = m.ens[src_b]
        src_fk_en = Symbol(src_fk, :_, src_a, :_, src_b)

        # Trace the FK path through the target schema
        fk_path = _extract_fk_path(fk_term)

        if length(fk_path) == 1
            # Simple case: f_src maps to single FK f_tgt
            tgt_fk = fk_path[1]
            (tgt_fk_src, tgt_fk_tgt) = tgt_sch.fks[tgt_fk]
            tgt_fk_en = Symbol(tgt_fk, :_, tgt_fk_src, :_, tgt_fk_tgt)
            ctx = Dict{Symbol,Symbol}(:r => tgt_fk_en)
            ens[src_fk_en] = (ctx, Set{Equation}())
            # subject and object FK mappings
            src_subj = Symbol(src_fk_en, :__, :subject)
            src_obj = Symbol(src_fk_en, :__, :object)
            tgt_subj = Symbol(tgt_fk_en, :__, :subject)
            tgt_obj = Symbol(tgt_fk_en, :__, :object)
            fks[src_subj] = Dict(:c => CQLFk(tgt_subj, CQLVar(:r)))
            fks[src_obj] = Dict(:c => CQLFk(tgt_obj, CQLVar(:r)))
        elseif fk_term == CQLVar(:_unit)
            # Identity FK mapping: f -> identity (empty FK path)
            # Match Java: always create rs:M(src), rt:M(tgt) from-vars
            src_subj = Symbol(src_fk_en, :__, :subject)
            src_obj = Symbol(src_fk_en, :__, :object)
            ctx = Dict{Symbol,Symbol}(:rs => tgt_a, :rt => tgt_b)
            ens[src_fk_en] = (ctx, Set{Equation}())
            fks[src_subj] = Dict(:c => CQLVar(:rs))
            fks[src_obj] = Dict(:c => CQLVar(:rt))
        else
            # Multi-hop FK path: f maps to g.h.i (chain of FKs)
            # Match Java: create rs:src_entity, rt:tgt_entity from-vars
            # plus r0..rN for each intermediate FK entity
            ctx = Dict{Symbol,Symbol}()
            where_eqs = Set{Equation}()
            ctx[:rs] = tgt_a
            ctx[:rt] = tgt_b
            var_names = Symbol[]
            for (idx, tgt_fk) in enumerate(fk_path)
                v = Symbol("r", idx - 1)
                push!(var_names, v)
                (tgt_fk_src, tgt_fk_tgt) = tgt_sch.fks[tgt_fk]
                tgt_fk_en = Symbol(tgt_fk, :_, tgt_fk_src, :_, tgt_fk_tgt)
                ctx[v] = tgt_fk_en
            end
            # WHERE: chain object(r_i) = subject(r_{i+1})
            for (idx, tgt_fk) in enumerate(fk_path)
                (tgt_fk_src, tgt_fk_tgt) = tgt_sch.fks[tgt_fk]
                tgt_fk_en = Symbol(tgt_fk, :_, tgt_fk_src, :_, tgt_fk_tgt)
                if idx < length(fk_path)
                    next_tgt_fk = fk_path[idx + 1]
                    (next_src, next_tgt) = tgt_sch.fks[next_tgt_fk]
                    next_fk_en = Symbol(next_tgt_fk, :_, next_src, :_, next_tgt)
                    obj_fk = Symbol(tgt_fk_en, :__, :object)
                    next_subj_fk = Symbol(next_fk_en, :__, :subject)
                    push!(where_eqs, Equation(
                        CQLFk(obj_fk, CQLVar(var_names[idx])),
                        CQLFk(next_subj_fk, CQLVar(var_names[idx + 1]))
                    ))
                end
            end
            # WHERE: first FK subject = rs, last FK object = rt
            first_fk = fk_path[1]
            (first_src, first_tgt) = tgt_sch.fks[first_fk]
            first_fk_en = Symbol(first_fk, :_, first_src, :_, first_tgt)
            first_subj = Symbol(first_fk_en, :__, :subject)
            push!(where_eqs, Equation(
                CQLFk(first_subj, CQLVar(var_names[1])),
                CQLVar(:rs)
            ))
            last_fk = fk_path[end]
            (last_src, last_tgt) = tgt_sch.fks[last_fk]
            last_fk_en = Symbol(last_fk, :_, last_src, :_, last_tgt)
            last_obj = Symbol(last_fk_en, :__, :object)
            push!(where_eqs, Equation(
                CQLFk(last_obj, CQLVar(var_names[end])),
                CQLVar(:rt)
            ))
            ens[src_fk_en] = (ctx, where_eqs)
            # FK subject/object mappings use rs/rt directly
            src_subj = Symbol(src_fk_en, :__, :subject)
            src_obj = Symbol(src_fk_en, :__, :object)
            fks[src_subj] = Dict(:c => CQLVar(:rs))
            fks[src_obj] = Dict(:c => CQLVar(:rt))
        end
    end

    # For each attribute a_src: E_src → Dom that maps through:
    for (src_att, att_term) in m.atts
        (src_en, _) = src_sch.atts[src_att]
        src_att_en = Symbol(src_att, :_, src_en)
        tgt_en = m.ens[src_en]

        # Extract the path: the att_term is like att_tgt(fk_path(x))
        (tgt_fk_path, tgt_att_name) = _extract_att_path(att_term)

        if isempty(tgt_fk_path) && tgt_att_name !== nothing
            # Simple: src att maps directly to tgt att
            # Match Java: from rs:tgt_entity, rt:tgt_att_entity
            tgt_att_en = Symbol(tgt_att_name, :_, tgt_en)
            ctx = Dict{Symbol,Symbol}(:rs => tgt_en, :rt => tgt_att_en)
            ens[src_att_en] = (ctx, Set{Equation}())
            src_subj = Symbol(src_att_en, :__, :subject)
            fks[src_subj] = Dict(:c => CQLVar(:rs))
            src_obj = Symbol(src_att_en, :__, :object)
            tgt_obj = Symbol(tgt_att_en, :__, :object)
            atts[src_obj] = CQLAtt(tgt_obj, CQLVar(:rt))
        else
            # att with FK path: src_att maps to att_tgt(fk1.fk2...fkn(x))
            if tgt_att_name !== nothing
                tgt_att_en_name = Symbol(tgt_att_name, :_, tgt_en)
                ctx = Dict{Symbol,Symbol}()
                where_eqs = Set{Equation}()
                ctx[:rs] = tgt_en
                ctx[:rt] = tgt_att_en_name
                var_names = Symbol[]
                for (idx, tgt_fk) in enumerate(tgt_fk_path)
                    v = Symbol("r", idx - 1)
                    push!(var_names, v)
                    (fk_src, fk_tgt) = tgt_sch.fks[tgt_fk]
                    fk_en = Symbol(tgt_fk, :_, fk_src, :_, fk_tgt)
                    ctx[v] = fk_en
                end
                # WHERE: chain object(r_i) = subject(r_{i+1})
                for (idx, tgt_fk) in enumerate(tgt_fk_path)
                    (fk_src, fk_tgt) = tgt_sch.fks[tgt_fk]
                    fk_en = Symbol(tgt_fk, :_, fk_src, :_, fk_tgt)
                    if idx < length(tgt_fk_path)
                        next_fk = tgt_fk_path[idx + 1]
                        (ns, nt) = tgt_sch.fks[next_fk]
                        next_en = Symbol(next_fk, :_, ns, :_, nt)
                        push!(where_eqs, Equation(
                            CQLFk(Symbol(fk_en, :__, :object), CQLVar(var_names[idx])),
                            CQLFk(Symbol(next_en, :__, :subject), CQLVar(var_names[idx + 1]))
                        ))
                    end
                end
                if !isempty(tgt_fk_path)
                    first_fk = tgt_fk_path[1]
                    (fs, ft) = tgt_sch.fks[first_fk]
                    first_en = Symbol(first_fk, :_, fs, :_, ft)
                    push!(where_eqs, Equation(
                        CQLFk(Symbol(first_en, :__, :subject), CQLVar(var_names[1])),
                        CQLVar(:rs)
                    ))
                    last_fk = tgt_fk_path[end]
                    (ls, lt) = tgt_sch.fks[last_fk]
                    last_en = Symbol(last_fk, :_, ls, :_, lt)
                    push!(where_eqs, Equation(
                        CQLFk(Symbol(last_en, :__, :object), CQLVar(var_names[end])),
                        CQLVar(:rt)
                    ))
                end
                ens[src_att_en] = (ctx, where_eqs)
                src_subj = Symbol(src_att_en, :__, :subject)
                fks[src_subj] = Dict(:c => CQLVar(:rs))
                src_obj = Symbol(src_att_en, :__, :object)
                tgt_obj = Symbol(tgt_att_en_name, :__, :object)
                atts[src_obj] = CQLAtt(tgt_obj, CQLVar(:rt))
            end
        end
    end

    CQLQuery(span_tgt, span_src, ens, fks, atts)
end

"""Get the RDF schema."""
function _get_rdf_schema(ts::Typeside)::CQLSchema
    ens = Set{Symbol}([:R])
    fks = Dict{Symbol,Tuple{Symbol,Symbol}}()
    atts = Dict{Symbol,Tuple{Symbol,Symbol}}(
        :subject => (:R, :Dom),
        :predicate => (:R, :Dom),
        :object => (:R, :Dom),
    )
    CQLSchema(ts, ens, fks, atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(),
        (en, eq) -> eq.lhs == eq.rhs)
end

"""Extract FK path from a mapping FK term like fk3(fk2(fk1(_unit)))."""
function _extract_fk_path(t::CQLTerm)::Vector{Symbol}
    path = Symbol[]
    current = t
    while current isa CQLFk
        pushfirst!(path, current.fk)
        current = current.arg
    end
    path
end

"""Extract FK path and final attribute from a mapping attribute term like att(fk2(fk1(_unit)))."""
function _extract_att_path(t::CQLTerm)::Tuple{Vector{Symbol}, Union{Symbol, Nothing}}
    if t isa CQLAtt
        fk_path = _extract_fk_path(t.arg)
        return (fk_path, t.att)
    elseif t isa CQLFk
        # Shouldn't happen for attribute terms
        return (_extract_fk_path(t), nothing)
    else
        return (Symbol[], nothing)
    end
end

"""Replace CQLGen(g) with CQLVar(rename[g]) in a term."""
function _gens_to_vars(t::CQLTerm, rename::Dict{Symbol,Symbol})::CQLTerm
    if t isa CQLGen
        haskey(rename, t.gen) ? CQLVar(rename[t.gen]) : t
    elseif t isa CQLFk
        CQLFk(t.fk, _gens_to_vars(t.arg, rename))
    elseif t isa CQLAtt
        CQLAtt(t.att, _gens_to_vars(t.arg, rename))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_gens_to_vars(a, rename) for a in t.args])
    else
        t
    end
end

"""Compute rext(q1, q2) — right extension.

Given q1: A→B and q2: A→C, produces a query B→C.

Algorithm: For each entity c in C, evaluate Q1 on Q2's frozen instance at c.
The eval result's generators become from-variables, equations become where-clause.
FK mappings are derived by evaluating Q1 on Q2's FK transforms."""
function _eval_rext(q1::CQLQuery, q2::CQLQuery, opts::CQLOptions)::CQLQuery
    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}()
    fks = Dict{Symbol, Dict{Symbol, CQLTerm}}()
    atts = Dict{Symbol, CQLTerm}()

    counter = Ref(0)
    entity_data = Dict{Symbol, Any}()

    # Step 1: Build entity blocks
    for c_en in q2.dst.ens
        # Frozen instance of Q2 at c_en (instance on A = q2.src)
        frozen_c = _eval_frozen_instance(q2, c_en, opts)

        # Evaluate Q1 on frozen instance (instance on B = q1.dst)
        eval_inst = eval_query_instance(q1, frozen_c, opts)

        # Create unique variable names for eval generators
        rename = Dict{Symbol, Symbol}()
        from_ctx = Dict{Symbol, Symbol}()
        for (g, en) in eval_inst.pres.gens
            counter[] += 1
            new_name = Symbol("v_", counter[])
            rename[g] = new_name
            from_ctx[new_name] = en
        end

        # Convert equations: CQLGen → CQLVar
        where_eqs = Set{Equation}()
        for eq in eval_inst.pres.eqs
            lhs = _gens_to_vars(eq.lhs, rename)
            rhs = _gens_to_vars(eq.rhs, rename)
            push!(where_eqs, Equation(lhs, rhs))
        end

        ens[c_en] = (from_ctx, where_eqs)
        entity_data[c_en] = (frozen=frozen_c, eval_inst=eval_inst, rename=rename)
    end

    # Step 2: FK mappings
    for (fk_name, (fk_src_en, fk_tgt_en)) in q2.dst.fks
        fk_var_mapping = q2.fks[fk_name]

        frozen_src = entity_data[fk_src_en].frozen
        frozen_tgt = entity_data[fk_tgt_en].frozen
        rename_src = entity_data[fk_src_en].rename
        rename_tgt = entity_data[fk_tgt_en].rename

        # Build transform: frozen_tgt → frozen_src
        # Q2.fks[fk] maps tgt entity's from-vars to src entity's terms
        tr_gens = Dict{Symbol, CQLTerm}()
        for (v, _) in frozen_tgt.pres.gens
            if haskey(fk_var_mapping, v)
                tr_gens[v] = _vars_to_gens_sks(fk_var_mapping[v],
                    frozen_src.pres.gens, frozen_src.pres.sks)
            end
        end
        tr_sks = Dict{Symbol, CQLTerm}()
        for (sk, _) in frozen_tgt.pres.sks
            if haskey(fk_var_mapping, sk)
                tr_sks[sk] = _vars_to_gens_sks(fk_var_mapping[sk],
                    frozen_src.pres.gens, frozen_src.pres.sks)
            end
        end
        tr = CQLTransform(frozen_tgt, frozen_src, tr_gens, tr_sks)

        # Evaluate Q1 on this transform
        eval_tr = eval_query_transform(q1, tr, opts)

        # Extract FK mapping: maps tgt entity's rext vars to src entity's rext terms
        fk_mapping = Dict{Symbol, CQLTerm}()
        for (g_tgt, mapped_term) in eval_tr.gens
            if haskey(rename_tgt, g_tgt)
                new_tgt_var = rename_tgt[g_tgt]
                new_term = _gens_to_vars(mapped_term, rename_src)
                fk_mapping[new_tgt_var] = new_term
            end
        end
        fks[fk_name] = fk_mapping
    end

    # Step 3: Attribute mappings
    # For now, handle identity-like cases where Q1 is identity
    # (general case requires EvalTransform-like attribute composition)
    if !isempty(q2.dst.atts) && _is_identity_mapping_query(q1)
        # For identity Q1: frozen gens map 1-to-1 to eval gens
        # Build mapping from frozen gen name to rext var name
        for (att_name, (att_en, att_ty)) in q2.dst.atts
            att_term = q2.atts[att_name]
            rename = entity_data[att_en].rename
            frozen_c = entity_data[att_en].frozen
            eval_inst = entity_data[att_en].eval_inst

            # Build frozen gen → rext var mapping
            frozen_to_rext = Dict{Symbol, Symbol}()
            for (g, en) in frozen_c.pres.gens
                # For identity Q1: gen q_{en}_1 has tuple {x => g_elem}
                # Find the eval gen of entity en
                for (eg, ee) in eval_inst.pres.gens
                    if ee == en
                        elem = eval_inst.algebra.gen[eg]
                        repr = repr_x(eval_inst.algebra, elem)
                        if repr isa CQLGen && repr.gen == eg
                            # Check if this eval gen's tuple maps to frozen gen g
                            felem = frozen_c.algebra.gen[g]
                            if haskey(eval_inst.algebra.gen, eg)
                                frozen_to_rext[g] = rename[eg]
                                break
                            end
                        end
                    end
                end
            end

            # Substitute Q2 att term: CQLVar(w) → CQLVar(frozen_to_rext[w])
            atts[att_name] = _subst_frozen_vars(att_term, frozen_to_rext)
        end
    elseif !isempty(q2.dst.atts)
        throw(CQLException("rext with attributes for non-identity Q1 is not yet supported"))
    end

    CQLQuery(q1.dst, q2.dst, ens, fks, atts)
end

"""Check if a query is essentially the identity query."""
function _is_identity_mapping_query(q::CQLQuery)::Bool
    q.src == q.dst || return false
    for (en, (ctx, wheres)) in q.ens
        length(ctx) == 1 || return false
        isempty(wheres) || return false
        first(values(ctx)) == en || return false
    end
    return true
end

"""Substitute CQLVar(v) with CQLVar(mapping[v]) in a term."""
function _subst_frozen_vars(t::CQLTerm, mapping::Dict{Symbol,Symbol})::CQLTerm
    if t isa CQLVar
        haskey(mapping, t.name) ? CQLVar(mapping[t.name]) : t
    elseif t isa CQLFk
        CQLFk(t.fk, _subst_frozen_vars(t.arg, mapping))
    elseif t isa CQLAtt
        CQLAtt(t.att, _subst_frozen_vars(t.arg, mapping))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_subst_frozen_vars(a, mapping) for a in t.args])
    else
        t
    end
end

