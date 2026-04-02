# ============================================================================
# Front/Back schema and query
# ============================================================================

"""Build the front (or back) schema for constraint ED at index i (0-based).

The front schema has a single entity 'Front' with attributes derived from
the universal variables (and, for back, existential variables) of the ED."""
function _eval_schema_front(c::CQLConstraints, idx::Int, is_back::Bool)::CQLSchema
    # CQL syntax uses 0-based indexing for EDs
    julia_idx = idx + 1
    (1 <= julia_idx <= length(c.egds)) || throw(CQLException("ED index $idx out of range (have $(length(c.egds)) EDs)"))
    ed = c.egds[julia_idx]
    sch = c.schema
    ts = sch.typeside

    ens = Set{Symbol}([:Front])
    fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    atts = Dict{Symbol, Tuple{Symbol, Symbol}}()

    # Front schema always has only universal variable attributes
    # (back query uses same front schema — existential vars are in FROM only)
    for (v, en) in ed.vars
        en in sch.ens || continue  # skip type-sorted vars
        for (att, ty) in schema_atts_from(sch, en)
            att_name = Symbol(string(v), "_", string(att))
            atts[att_name] = (:Front, ty)
        end
    end

    eq_fn = (en, eq) -> eq.lhs == eq.rhs
    CQLSchema(ts, ens, fks, atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(), eq_fn)
end

"""Build the front or back query for constraint ED at index i (0-based).

The query maps from the constraints schema to the front/back schema.
For front: uses only universal variables.
For back: uses both universal and existential variables, plus conclusion equations."""
function _eval_query_front_back(c::CQLConstraints, idx::Int, is_back::Bool)::CQLQuery
    julia_idx = idx + 1
    (1 <= julia_idx <= length(c.egds)) || throw(CQLException("ED index $idx out of range"))
    ed = c.egds[julia_idx]
    src_schema = c.schema
    front_schema = _eval_schema_front(c, idx, is_back)

    # Build from-clause: one generator per universal variable (entity-sorted)
    from_ctx = Dict{Symbol, Symbol}()
    for (v, en) in ed.vars
        en in src_schema.ens || continue
        from_ctx[v] = en
    end

    # Build attribute mapping
    att_mapping = Dict{Symbol, CQLTerm}()
    for (v, en) in ed.vars
        en in src_schema.ens || continue
        for (att, _) in schema_atts_from(src_schema, en)
            att_name = Symbol(string(v), "_", string(att))
            att_mapping[att_name] = CQLAtt(att, CQLVar(v))
        end
    end

    # Build where-clause from ED premises
    where_eqs = Set{Equation}(ed.premises)

    if is_back
        # Add existential variables to from-clause (but not to att_mapping)
        for (v, en) in ed.exists_vars
            en in src_schema.ens || continue
            from_ctx[v] = en
        end
        # Add conclusion equations as where-clauses for back
        for eq in ed.conclusions
            push!(where_eqs, eq)
        end
    end

    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}(
        :Front => (from_ctx, where_eqs)
    )
    fks = Dict{Symbol, Dict{Symbol, CQLTerm}}()

    CQLQuery(src_schema, front_schema, ens, fks, att_mapping)
end

"""Evaluate a fromConstraints query: `fromConstraints n c` extracts the nth ED
from constraints c and builds a query from c.schema to the ED schema.

The ED schema has two entities (front, back) connected by FK unit: back → front.
- Entity front: universal variables with premises (the "pattern")
- Entity back: all variables with all equations (the "extended pattern")
- FK unit: identity on universal variables (projects back to front)
"""
function _eval_query_from_constraints(c::CQLConstraints, idx::Int, opts::CQLOptions)::CQLQuery
    julia_idx = idx + 1  # CQL uses 0-based indexing
    (1 <= julia_idx <= length(c.egds)) || throw(CQLException(
        "ED index $idx out of range (have $(length(c.egds)) EDs)"))
    ed = c.egds[julia_idx]
    src_schema = c.schema
    ts = src_schema.typeside

    # Build the ED schema: entities front/back, FK unit: back → front, no attributes
    ed_ens = Set{Symbol}([:front, :back])
    ed_fks = Dict{Symbol, Tuple{Symbol, Symbol}}(:unit => (:back, :front))
    ed_atts = Dict{Symbol, Tuple{Symbol, Symbol}}()
    eq_fn = (en, eq) -> eq.lhs == eq.rhs
    ed_schema = CQLSchema(ts, ed_ens, ed_fks, ed_atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(), eq_fn)

    # Build from-clause for front: universal variables only
    front_ctx = Dict{Symbol, Symbol}()
    for (v, en) in ed.vars
        front_ctx[v] = en
    end

    # Build from-clause for back: all variables (universal + existential)
    back_ctx = Dict{Symbol, Symbol}()
    for (v, en) in ed.vars
        back_ctx[v] = en
    end
    for (v, en) in ed.exists_vars
        back_ctx[v] = en
    end

    # Build where-clauses
    front_where = Set{Equation}(ed.premises)
    back_where = union(Set{Equation}(ed.premises), Set{Equation}(ed.conclusions))

    # FK mapping for unit: back → front
    # Maps each front from-variable to the same variable in back's context
    unit_map = Dict{Symbol, CQLTerm}()
    for (v, _) in ed.vars
        unit_map[v] = CQLVar(v)
    end

    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}(
        :front => (front_ctx, front_where),
        :back => (back_ctx, back_where),
    )
    query_fks = Dict{Symbol, Dict{Symbol, CQLTerm}}(
        :unit => unit_map,
    )
    query_atts = Dict{Symbol, CQLTerm}()

    CQLQuery(src_schema, ed_schema, ens, query_fks, query_atts)
end

# ============================================================================
# DeltaCoEval query: toCoQuery F for a mapping F: S→T produces query S→T
# ============================================================================

"""Build the deltaCoEval query for a mapping F: S→T.

Produces a query Q: S→T such that eval(Q, I) ≅ coeval(delta(F), I).

Algorithm:
For each entity en2 in T:
  - Build a seed instance on T with one generator v:en2
  - Apply delta(F) to get a delta instance on S
  - The delta instance's carriers become from-variables
  - The delta instance's equations become the where-clause
For each FK fk2: src_en→tgt_en in T:
  - Map tgt block variables to src block variables via the FK transform
For each attribute att2: en2→ty in T:
  - Evaluate att2(v) in the seed and express using S-schema attributes
"""
function _delta_coeval_query(F::CQLMapping, opts::CQLOptions)::CQLQuery
    if _is_identity_mapping(F)
        return identity_query(F.src)
    end

    S = F.src
    T = F.dst

    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}()
    fks_map = Dict{Symbol, Dict{Symbol, CQLTerm}}()
    atts_map = Dict{Symbol, CQLTerm}()

    # Per-entity seed and delta instances
    seeds = Dict{Symbol, Any}()
    deltas = Dict{Symbol, Any}()
    e2q_maps = Dict{Symbol, Dict}()  # en2 → Dict(delta_elem → qvar_name)

    gen_id = Ref(0)

    for en2 in T.ens
        # Build seed instance on T with one generator v:en2
        seed_pres = Presentation(Dict(:v => en2), Dict{Symbol,Symbol}(), Set{Equation}())
        col = presentation_to_collage(T, seed_pres)
        prover = create_prover(col, opts)
        dp_fn = eq -> prover(Ctx(), eq)
        seed = initial_instance(seed_pres, dp_fn, T)
        seeds[en2] = seed

        # Delta(F) on the seed gives instance on S
        delta = eval_delta_instance(F, seed, opts)
        deltas[en2] = delta

        # From-variables from delta's entity carriers
        from_ctx = Dict{Symbol,Symbol}()
        e2q = Dict()

        for en1 in S.ens
            for elem in carrier(delta.algebra, en1)
                gen_id[] += 1
                qvar = Symbol("v", gen_id[])
                from_ctx[qvar] = en1
                e2q[elem] = qvar
            end
        end

        # Where-clause from delta presentation equations
        where_eqs = Set{Equation}()
        for eq in delta.pres.eqs
            lhs = _dcq_term(eq.lhs, delta.algebra, e2q)
            rhs = _dcq_term(eq.rhs, delta.algebra, e2q)
            push!(where_eqs, Equation(lhs, rhs))
        end

        ens[en2] = (from_ctx, where_eqs)
        e2q_maps[en2] = e2q
    end

    # FK mappings: for each FK fk2: src_en→tgt_en in T
    for (fk2, (src_en, tgt_en)) in T.fks
        new_fk_map = Dict{Symbol, CQLTerm}()
        seed_src = seeds[src_en]
        seed_tgt = seeds[tgt_en]
        delta_tgt = deltas[tgt_en]

        tgt_e2q = e2q_maps[tgt_en]
        src_e2q = e2q_maps[src_en]

        # For each element in delta(tgt_en), apply the FK transform
        for en1 in S.ens
            for elem in carrier(delta_tgt.algebra, en1)
                qvar_tgt = tgt_e2q[elem]
                (_, x) = elem  # x is carrier element of F(en1) in seed_tgt

                # Transform: substitute Gen(:v) → Fk(fk2, Gen(:v)) in x, then eval in seed_src
                x_subst = _dcq_subst_gen(x, :v, CQLFk(fk2, CQLGen(:v)))
                x_in_src = _dcq_eval_entity(seed_src.algebra, x_subst)

                delta_elem_src = (en1, x_in_src)
                new_fk_map[qvar_tgt] = CQLVar(src_e2q[delta_elem_src])
            end
        end

        fks_map[fk2] = new_fk_map
    end

    # Attribute mappings: for each attribute att2: en2→ty in T
    for (att2, (att_en, att_ty)) in T.atts
        e2q = e2q_maps[att_en]
        seed = seeds[att_en]
        delta = deltas[att_en]

        v_elem = seed.algebra.gen[:v]
        # The seed's nf_y for att2(v)
        seed_att_nf = seed.algebra.nf_y(Right((v_elem, att2)))

        # Search delta elements for an S-attribute that evaluates to the same type element
        found = false
        for en1 in S.ens
            for elem in carrier(delta.algebra, en1)
                for (att_S, (att_S_src, _)) in S.atts
                    att_S_src == en1 || continue
                    delta_att_nf = delta.algebra.nf_y(Right((elem, att_S)))
                    if delta_att_nf == seed_att_nf
                        atts_map[att2] = CQLAtt(att_S, CQLVar(e2q[elem]))
                        found = true
                        break
                    end
                end
                found && break
            end
            found && break
        end

        if !found
            # Fallback: try to build a compound term using typeside functions
            # Search for combinations of S-attribute terms and typeside functions
            atts_map[att2] = _dcq_find_compound_att(att2, seed_att_nf, seed, delta, S, e2q)
        end
    end

    CQLQuery(S, T, ens, fks_map, atts_map)
end

"""Convert a delta presentation term (CQLGen-based) to a query term (CQLVar-based)."""
function _dcq_term(t::CQLTerm, delta_alg, e2q)::CQLTerm
    if t isa CQLGen
        elem = delta_alg.gen[t.gen]
        CQLVar(e2q[elem])
    elseif t isa CQLFk
        CQLFk(t.fk, _dcq_term(t.arg, delta_alg, e2q))
    elseif t isa CQLAtt
        CQLAtt(t.att, _dcq_term(t.arg, delta_alg, e2q))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_dcq_term(a, delta_alg, e2q) for a in t.args])
    else
        t
    end
end

"""Substitute CQLGen(name) with replacement in an entity-level term."""
function _dcq_subst_gen(t::CQLTerm, name::Symbol, replacement::CQLTerm)::CQLTerm
    if t isa CQLGen && t.gen == name
        replacement
    elseif t isa CQLFk
        CQLFk(t.fk, _dcq_subst_gen(t.arg, name, replacement))
    else
        t
    end
end

"""Evaluate an entity-level CQLTerm (CQLGen, CQLFk) in an algebra to get a carrier element."""
function _dcq_eval_entity(alg, t::CQLTerm)
    if t isa CQLGen
        alg.gen[t.gen]
    elseif t isa CQLFk
        inner = _dcq_eval_entity(alg, t.arg)
        eval_fk(alg, t.fk, inner)
    else
        error("Cannot evaluate entity term in algebra: $t")
    end
end

"""Search for a compound type term built from S-attributes and typeside functions
that matches the target nf_y value."""
function _dcq_find_compound_att(att2, target_nf, seed, delta, S, e2q)::CQLTerm
    # Build a catalog of available base terms (S-attributes of delta elements)
    base_terms = Dict{CQLTerm, CQLTerm}()  # nf_value → query_term
    for en1 in S.ens
        for elem in carrier(delta.algebra, en1)
            for (att_S, (att_S_src, _)) in S.atts
                att_S_src == en1 || continue
                nf = delta.algebra.nf_y(Right((elem, att_S)))
                qterm = CQLAtt(att_S, CQLVar(e2q[elem]))
                base_terms[nf] = qterm
            end
        end
    end

    # Check if target is directly a base term
    if haskey(base_terms, target_nf)
        return base_terms[target_nf]
    end

    # Try applying typeside functions to base terms
    for (sym, (arg_tys, ret_ty)) in S.typeside.syms
        if length(arg_tys) == 1
            for (nf, qterm) in base_terms
                composed_nf = CQLSym(sym, CQLTerm[nf])
                if composed_nf == target_nf
                    return CQLSym(sym, CQLTerm[qterm])
                end
            end
        elseif length(arg_tys) == 2
            for (nf1, qt1) in base_terms
                for (nf2, qt2) in base_terms
                    composed_nf = CQLSym(sym, CQLTerm[nf1, nf2])
                    if composed_nf == target_nf
                        return CQLSym(sym, CQLTerm[qt1, qt2])
                    end
                end
            end
        end
    end

    # Last resort: create a Skolem-like placeholder
    throw(CQLException("Cannot find query term for T-attribute $att2 in deltaCoEval"))
end

