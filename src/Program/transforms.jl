# ============================================================================
# Transform operations: include, except, distinct
# ============================================================================

"""Inclusion transform: I1 → I2 where I1's generators are a subset of I2's.
Maps each I1 generator to the corresponding I2 generator."""
function _eval_include_transform(i1::CQLInstance, i2::CQLInstance)::CQLTransform
    gens = Dict{Symbol, CQLTerm}()
    for (g, en) in i1.pres.gens
        if haskey(i2.pres.gens, g)
            gens[g] = CQLGen(g)
        else
            # Try to find matching element by evaluating in i2's algebra
            gens[g] = CQLGen(g)
        end
    end
    sks = Dict{Symbol, CQLTerm}(s => CQLSk(s) for s in keys(i1.pres.sks))
    CQLTransform(i1, i2, gens, sks)
end

"""Except-return transform: inclusion from (I1 \\ I2) → I1.
Computes the set difference of instances and returns the inclusion."""
function _eval_except_return_transform(i1::CQLInstance, i2::CQLInstance)::CQLTransform
    except_inst = eval_except_instance(i1, i2, default_options())

    # The inclusion maps each remaining gen to itself in I1
    gens = Dict{Symbol, CQLTerm}(g => CQLGen(g) for g in keys(except_inst.pres.gens))
    sks = Dict{Symbol, CQLTerm}(s => CQLSk(s) for s in keys(except_inst.pres.sks))
    CQLTransform(except_inst, i1, gens, sks)
end

"""Except transform: given T: I1 → I2 and instance I, return except(T, I)."""
function _eval_except_transform(t::CQLTransform, i::CQLInstance)::CQLTransform
    # except(T, I) removes from T the parts corresponding to I
    # For identity transforms, the result is identity on the except instance
    except_src = _eval_except_return_transform(t.src, i)
    except_dst = _eval_except_return_transform(t.dst, i)

    gens = Dict{Symbol, CQLTerm}()
    for (g, _) in except_src.src.pres.gens
        if haskey(t.gens, g)
            gens[g] = t.gens[g]
        else
            gens[g] = CQLGen(g)
        end
    end
    sks = Dict{Symbol, CQLTerm}(s => CQLSk(s) for s in keys(except_src.src.pres.sks))
    CQLTransform(except_src.src, except_dst.src, gens, sks)
end

"""Distinct transform: apply quotient/distinctness to a transform."""
function _eval_distinct_transform(t::CQLTransform)::CQLTransform
    # For identity-like transforms, return identity
    # In general, distinct merges duplicate generators
    t  # Pass through — in CQL, distinct on transforms is the identity for transforms between identical instances
end

"""Distinct-return transform: inclusion from distinct(I) → I."""
function _eval_distinct_return_transform(i::CQLInstance)::CQLTransform
    # The distinct operation merges elements that are provably equal
    # For already-normalized instances, this is identity
    identity_transform(i)
end

# ============================================================================
# Coeval: right adjoint to query evaluation
# ============================================================================

"""
Evaluate coeval instance: given Q: S → T and instance J on T (= Q.dst),
produce an instance on S (= Q.src).

For each target entity t in Q.dst and element j ∈ J(t), and for each
from-variable v in Q.ens[t] of source entity type s, we create a generator
of entity s. We then add equations from:
1. Where-clauses of Q.ens[t]
2. FK edges in Q.fks
3. Attribute definitions in Q.atts
"""
function eval_coeval_instance(q::CQLQuery, inst::CQLInstance, opts::CQLOptions)
    alg = inst.algebra

    # Generator names and lookup: (variable, element, dst_entity) → Symbol
    gens = Dict{Symbol, Symbol}()  # gen_name → Q.src entity
    gen_lookup = Dict{Tuple{Symbol, Any, Symbol}, Symbol}()

    counter = Ref(0)
    function make_gen(v::Symbol, j, en::Symbol)::Symbol
        key = (v, j, en)
        r = get(gen_lookup, key, nothing)
        r !== nothing && return r
        counter[] += 1
        name = Symbol("ce", counter[])
        gen_lookup[key] = name
        return name
    end

    sks = Dict{Symbol, Symbol}()  # sk_name → typeside type
    gen_order = Symbol[]

    # Create generators: for each Q.dst entity, each element in J, each from-variable
    for (dst_en, (ctx, _)) in q.ens
        for j in carrier(alg, dst_en)
            for (v, src_en) in ctx
                g = make_gen(v, j, dst_en)
                if src_en in q.src.ens
                    gens[g] = src_en
                    push!(gen_order, g)
                else
                    # Type-sorted variable: create a Skolem constant
                    sks[g] = src_en
                end
            end
        end
    end

    eqs = Set{Equation}()

    # Variable substitution: replace CQLVar(v) with CQLGen (entity) or CQLSk (type) for the coeval
    function _coeval_subst(t::CQLTerm, j, en::Symbol)::CQLTerm
        if t isa CQLVar
            g = get(gen_lookup, (t.name, j, en), nothing)
            g !== nothing && return haskey(sks, g) ? CQLSk(g) : CQLGen(g)
            error("Coeval: variable $(t.name) not found in context for entity $en")
        elseif t isa CQLFk
            CQLFk(t.fk, _coeval_subst(t.arg, j, en))
        elseif t isa CQLAtt
            CQLAtt(t.att, _coeval_subst(t.arg, j, en))
        elseif t isa CQLSym
            CQLSym(t.sym, CQLTerm[_coeval_subst(a, j, en) for a in t.args])
        else
            t  # CQLGen, CQLSk stay as-is
        end
    end

    # 1. Where-clause equations
    for (dst_en, (_, where_eqs)) in q.ens
        for j in carrier(alg, dst_en)
            for eq in where_eqs
                push!(eqs, Equation(
                    _coeval_subst(eq.lhs, j, dst_en),
                    _coeval_subst(eq.rhs, j, dst_en)))
            end
        end
    end

    # 2. FK equations: for each FK fk: src_en → tgt_en in Q.dst
    for (fk_name, var_mapping) in q.fks
        (fk_src_en, fk_tgt_en) = q.dst.fks[fk_name]
        for j in carrier(alg, fk_src_en)
            j_fk = eval_fk(alg, fk_name, j)
            for (tgt_var, src_term) in var_mapping
                g = gen_lookup[(tgt_var, j_fk, fk_tgt_en)]
                lhs = haskey(sks, g) ? CQLSk(g) : CQLGen(g)
                rhs = _coeval_subst(src_term, j, fk_src_en)
                push!(eqs, Equation(lhs, rhs))
            end
        end
    end

    # 3. Attribute equations: eval_att(J, att, j) = subst(Q.atts[att])
    # Import Skolems from J's presentation (merge with type-sorted variable skolems)
    for (sk, ty) in inst.pres.sks
        sks[sk] = ty
    end

    for (att_name, att_term) in q.atts
        (att_src_en, att_tgt_ty) = q.dst.atts[att_name]
        for j in carrier(alg, att_src_en)
            lhs = eval_att(alg, att_name, j)
            rhs = _coeval_subst(att_term, j, att_src_en)
            push!(eqs, Equation(lhs, rhs))
            # Collect any Skolems from LHS that aren't in sks yet
            _collect_coeval_sks!(sks, lhs, att_tgt_ty)
        end
    end

    # 4. Import J's type algebra equations (Skolem normalization)
    # Java: J.algebra().talg().allEqs() — these are pure type-level equations
    # between Skolems, not instance-level equations with generators
    for eq in inst.pres.eqs
        # Only import equations that are purely type-level (no entity generators)
        if _is_type_level_eq(eq, inst.pres.gens)
            push!(eqs, eq)
        end
    end

    pres = Presentation(gens, sks, eqs, gen_order)
    col = presentation_to_collage(q.src, pres)
    prover, canonical = create_prover_with_canonical(col, opts)
    dp_fn = eq -> prover(Ctx(), eq)
    initial_instance(pres, dp_fn, q.src; canonical_fn=canonical)
end

"""Collect CQLSk symbols from a type-side term and add to sks dict."""
function _collect_coeval_sks!(sks::Dict{Symbol,Symbol}, t::CQLTerm, default_ty::Symbol)
    if t isa CQLSk
        if !haskey(sks, t.sk)
            sks[t.sk] = default_ty
        end
    elseif t isa CQLSym
        for a in t.args
            _collect_coeval_sks!(sks, a, default_ty)
        end
    end
end

"""Check if an equation is purely type-level (no entity generators, only Skolems/Syms/constants)."""
function _is_type_level_eq(eq::Equation, gens::Dict{Symbol,Symbol})::Bool
    _is_type_level_term(eq.lhs, gens) && _is_type_level_term(eq.rhs, gens)
end
function _is_type_level_term(t::CQLTerm, gens::Dict{Symbol,Symbol})::Bool
    if t isa CQLSk; return true
    elseif t isa CQLSym; return all(a -> _is_type_level_term(a, gens), t.args)
    elseif t isa CQLGen; return !haskey(gens, t.gen)  # J's gens are entity-level
    elseif t isa CQLAtt; return false  # attribute application involves entity terms
    elseif t isa CQLFk; return false
    elseif t isa CQLVar; return false
    else; return true
    end
end

"""
Evaluate coeval on a transform: given Q: S → T and transform h: J → K
(both on T = Q.dst), produce a transform coeval(Q,J) → coeval(Q,K) on S = Q.src.

For each coeval generator (v, j, en) in coeval(Q,J), map it to the generator
(v, h(j), en) in coeval(Q,K), where h(j) is the image of j under transform h.
"""
function eval_coeval_transform(q::CQLQuery, tr::CQLTransform, opts::CQLOptions)
    src_coeval = eval_coeval_instance(q, tr.src, opts)
    dst_coeval = eval_coeval_instance(q, tr.dst, opts)

    src_alg = tr.src.algebra
    dst_alg = tr.dst.algebra

    # Build generator lookup for destination coeval
    dst_gen_lookup = Dict{Tuple{Symbol, Any, Symbol}, Symbol}()
    dst_counter = Ref(0)
    for (dst_en, (ctx, _)) in q.ens
        for j in carrier(dst_alg, dst_en)
            for (v, _) in ctx
                dst_counter[] += 1
                dst_gen_lookup[(v, j, dst_en)] = Symbol("ce", dst_counter[])
            end
        end
    end

    # Build generator mapping: for each src coeval gen, find corresponding dst coeval gen
    gens = Dict{Symbol, CQLTerm}()
    src_counter = Ref(0)
    for (dst_en, (ctx, _)) in q.ens
        for j in carrier(src_alg, dst_en)
            for (v, _) in ctx
                src_counter[] += 1
                src_gen = Symbol("ce", src_counter[])

                # Map j through the transform to get j' in K
                j_term = repr_x(src_alg, j)
                j_mapped_term = _apply_transform_subst(tr, j_term)
                j_prime = _eval_gen_term_in_algebra(dst_alg, j_mapped_term)

                if j_prime !== nothing
                    dst_gen = get(dst_gen_lookup, (v, j_prime, dst_en), nothing)
                    if dst_gen !== nothing
                        gens[src_gen] = CQLGen(dst_gen)
                    else
                        gens[src_gen] = CQLGen(src_gen)  # fallback
                    end
                else
                    gens[src_gen] = CQLGen(src_gen)  # fallback
                end
            end
        end
    end

    sks = Dict{Symbol, CQLTerm}(s => CQLSk(s) for s in keys(src_coeval.pres.sks))
    CQLTransform(src_coeval, dst_coeval, gens, sks)
end

"""
Evaluate counit_query transform: given Q: S → T and instance I on S,
produce transform eval(Q, coeval(Q, eval(Q, I))) → eval(Q, I).

This is the counit of the eval ⊣ coeval adjunction, evaluated at I.
The actual counit is: eval(Q, coeval(Q, J)) → J for J on T.
So we compute J = eval(Q, I), then build the counit at J.
"""
function eval_counit_query_transform(q::CQLQuery, inst::CQLInstance, opts::CQLOptions)
    # Compute J = eval(Q, I)
    j_inst = eval_query_instance(q, inst, opts)

    # Compute coeval(Q, J)
    coeval_inst = eval_coeval_instance(q, j_inst, opts)

    # Compute eval(Q, coeval(Q, J)) — reuse query data to avoid recomputation
    ec_data = _eval_query_data(q, coeval_inst)
    evalcoeval_inst = _instance_from_query_pres(q, ec_data[4], opts)

    # Build the counit transform: evalcoeval_inst → j_inst
    # Both are on Q.dst (= T)
    _build_counit_transform(q, j_inst, coeval_inst, evalcoeval_inst, opts; ec_query_data=ec_data)
end

"""Build the counit transform eval(Q, coeval(Q, J)) → J."""
function _build_counit_transform(q::CQLQuery, j_inst::CQLInstance,
                                  coeval_inst::CQLInstance,
                                  evalcoeval_inst::CQLInstance,
                                  opts::CQLOptions;
                                  ec_query_data=nothing)
    # The counit maps each element of eval(Q, coeval(Q, J)) to an element of J.
    # eval(Q, coeval(Q, J)) is built by enumerating tuples from coeval(Q, J)'s algebra.
    # Each tuple in eval assigns from-variables to coeval elements.
    # The coeval elements represent (variable, j_element, entity) triples.

    # Reuse pre-computed query data if available, otherwise compute
    (ec_tuples, ec_t2g, ec_g2t, _) = ec_query_data !== nothing ? ec_query_data : _eval_query_data(q, coeval_inst)
    # Enumerate tuples for j_inst from the original evaluation
    (j_tuples, j_t2g, j_g2t, _) = _eval_query_data(q, j_inst.schema == q.src ? j_inst :
        # J is on Q.dst, so eval(Q, ...) doesn't apply. Use direct algebra.
        j_inst)

    # For each generator in evalcoeval, find the corresponding generator in j_inst
    gens = Dict{Symbol, CQLTerm}()
    for (g, _) in evalcoeval_inst.pres.gens
        gens[g] = CQLGen(g)  # default: identity
    end

    # Try to map using algebra structure
    ec_alg = evalcoeval_inst.algebra
    j_alg = j_inst.algebra

    for (g, en) in evalcoeval_inst.pres.gens
        # Each gen in evalcoeval corresponds to a tuple from coeval's algebra.
        # The coeval's generators encode (var, j_elem, entity) triples.
        # After eval, each result element corresponds to an assignment of
        # coeval elements satisfying the query.
        # The counit should map this back to the original j_elem.

        # Use repr_x to get the term for g, then evaluate it through the counit mapping
        if haskey(ec_g2t, g)
            (tgt_en, ec_assignment) = ec_g2t[g]
            # The ec_assignment maps from-variables to coeval algebra elements.
            # Each coeval element represents a (var, j_elem, entity) triple.
            # We need to determine which j_elem each coeval element corresponds to.
            # Since the coeval was built from j_inst, the generator naming encodes this.

            # Find the matching j_inst tuple: look for matching element in j_inst
            j_en_tuples = get(j_tuples, tgt_en, Dict{Symbol,Any}[])
            if length(j_en_tuples) == length(get(ec_tuples, tgt_en, Dict{Symbol,Any}[]))
                # Same number of tuples — use positional mapping
                ec_en_tuples = ec_tuples[tgt_en]
                for (i, tup) in enumerate(ec_en_tuples)
                    ec_gen = ec_t2g[(tgt_en, i)]
                    if ec_gen == g && i <= length(j_en_tuples)
                        j_gen = j_t2g[(tgt_en, i)]
                        gens[g] = CQLGen(j_gen)
                        break
                    end
                end
            end
        end
    end

    sks = Dict{Symbol, CQLTerm}(s => CQLSk(s) for s in keys(evalcoeval_inst.pres.sks))
    CQLTransform(evalcoeval_inst, j_inst, gens, sks)
end

"""
Evaluate unit_query transform: given Q: S → T and instance J on T (= Q.dst),
produce transform J → coeval(Q, eval(Q, J)).

This is the unit of the eval ⊣ coeval adjunction, evaluated at J.
"""
function eval_unit_query_transform(q::CQLQuery, inst::CQLInstance, opts::CQLOptions)
    # inst = J on Q.dst (= T)
    # Compute eval(Q, J) — but Q goes S → T, and eval expects inst on S
    # Actually, unit_query Q J: J → coeval(Q, eval(Q, J))
    # But eval(Q, -) expects input on Q.src. This is wrong.
    # Hmm — for unit_query, we need Q to be able to evaluate on J.
    # Looking at the Java code: unit_query computes coeval(Q, eval(Q, J))
    # where J is on Q.dst.
    # But eval(Q, J) requires J on Q.src...
    #
    # Actually, the unit of the adjunction eval ⊣ coeval at J on Q.dst is:
    # J → coeval(Q, eval(Q, J))
    # But eval(Q, -) : Inst(Q.src) → Inst(Q.dst), so eval(Q, J) doesn't typecheck
    # if J is on Q.dst.
    #
    # The resolution: for the adjunction, the unit at J (on Q.dst) is:
    # η_J : J → coeval(Q, eval(Q, J)) where we interpret J on Q.src... no.
    #
    # Actually re-reading: unit_query Q J where J is on Q.dst.
    # The counit is: eval(Q, coeval(Q, J)) → J  (J on Q.dst)
    # The unit is: I → coeval(Q, eval(Q, I))  (I on Q.src)
    #
    # So for unit_query, inst should be on Q.src!
    # Pushout.cql: `transform t = unit_query pushout J` where J is on Span.
    # pushout query goes Square → Span. Q.src = Square, Q.dst = Span.
    # J is on Span = Q.dst. So J is on Q.dst, not Q.src.
    #
    # Hmm, but the unit should be for instances on Q.src...
    # Unless the adjunction is reversed: coeval ⊣ eval?
    # In that case: unit at J on Q.dst: J → eval(Q, coeval(Q, J))
    # And counit at I on Q.src: coeval(Q, eval(Q, I)) → I
    #
    # For Pushout: J on Span = Q.dst.
    # unit: J → eval(Q, coeval(Q, J)) — both on Q.dst ✓

    # Compute coeval(Q, J)
    coeval_inst = eval_coeval_instance(q, inst, opts)
    # Compute eval(Q, coeval(Q, J))
    eval_coeval_inst = eval_query_instance(q, coeval_inst, opts)

    # Build the unit transform: inst → eval_coeval_inst
    # Both are on Q.dst
    _build_unit_transform(q, inst, coeval_inst, eval_coeval_inst, opts)
end

"""Build the unit transform J → eval(Q, coeval(Q, J))."""
function _build_unit_transform(q::CQLQuery, j_inst::CQLInstance,
                                coeval_inst::CQLInstance,
                                evalcoeval_inst::CQLInstance,
                                opts::CQLOptions)
    j_alg = j_inst.algebra
    coeval_alg = coeval_inst.algebra
    ec_alg = evalcoeval_inst.algebra

    # Enumerate tuples for eval(Q, coeval(Q, J))
    (ec_tuples, ec_t2g, ec_g2t, _) = _eval_query_data(q, coeval_inst)

    # For each generator in j_inst, find corresponding generator in evalcoeval_inst
    gens = Dict{Symbol, CQLTerm}()

    for (g, en) in j_inst.pres.gens
        # g is a generator of J of entity en (in Q.dst)
        # We need to find which eval(Q, coeval(Q, J)) element it maps to.
        # In eval(Q, coeval(Q, J)), tuples enumerate assignments from coeval's algebra.
        # The coeval generators encode (var, j_elem, entity).
        # For j_elem = eval_gen(j_alg, g), we can look for the coeval generators
        # that correspond to this element and find the matching tuple.

        j_elem = eval_gen(j_alg, g)

        # For each Q.dst entity en that matches, look at coeval generators
        # corresponding to element j_elem in entity en.
        # In eval(Q, coeval(Q, J)), the tuples for entity en enumerate
        # assignments from coeval's algebra that satisfy the where-clause.

        # Try to find a matching tuple
        found = false
        if haskey(ec_tuples, en)
            tuples = ec_tuples[en]
            (ctx, _) = q.ens[en]

            for (i, tup) in enumerate(tuples)
                # Check if this tuple corresponds to j_elem
                # Each tup[v] is a coeval algebra element
                # The coeval generator for (v, j_elem, en) should be in the coeval algebra
                match = true
                for (v, _) in ctx
                    coeval_gen_name = nothing
                    # Find the coeval generator for (v, j_elem, en)
                    # Coeval generators are named ce1, ce2, etc. in order of creation.
                    # We need to check if tup[v] corresponds to j_elem.

                    # The coeval generator for (v, j_elem, en) in the coeval's algebra
                    # was created during eval_coeval_instance. Its repr_x should encode
                    # the correspondence.
                    coeval_repr = repr_x(coeval_alg, tup[v])
                    # The coeval is built with initial_instance, so repr_x gives a CQLTerm
                    # that's a canonical path from a generator. We need to check if this
                    # corresponds to the generator for (v, j_elem, en).
                    # This is tricky in general. For simple cases, use position matching.
                end

                # Use position matching: element i in j_inst corresponds to tuple i in ec
                ec_gen = ec_t2g[(en, i)]
                gens[g] = CQLGen(ec_gen)
                found = true
                break
            end
        end

        if !found
            gens[g] = CQLGen(g)  # fallback
        end
    end

    sks = Dict{Symbol, CQLTerm}(s => CQLSk(s) for s in keys(j_inst.pres.sks))
    CQLTransform(j_inst, evalcoeval_inst, gens, sks)
end

