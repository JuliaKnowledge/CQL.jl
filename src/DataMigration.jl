"""
Functorial data migration: Delta (pullback) and Sigma (pushforward) operations.

Given a mapping F: S -> T:
- Delta_F: instances on T -> instances on S  (restriction/pullback)
- Sigma_F: instances on S -> instances on T  (extension/pushforward)
"""

# ============================================================================
# Delta (pullback)
# ============================================================================

"""
Evaluate delta instance: pull back an instance along a mapping.

Given F: S -> T and instance I on T, produces an instance on S where:
- Carrier of entity e in S = Carrier of F(e) in T
- FK f in S interpreted via composition with F(f)
"""
function eval_delta_instance(m::CQLMapping, inst::CQLInstance{X0,Y0}, opts::CQLOptions) where {X0,Y0}
    src = m.src
    alg = inst.algebra

    # The carrier type for delta is Tuple{Symbol, X0} (entity tag + original element)
    DX = Tuple{Symbol, X0}

    # Entity carriers: en_S -> carrier of F(en_S) in T
    new_en = Dict{Symbol, Set{DX}}()
    for en in src.ens
        en_t = m.ens[en]
        new_en[en] = Set{DX}([(en, x) for x in carrier(alg, en_t)])
    end

    # Generator interpretation (populated below after building presentation)
    new_gen = Dict{Symbol, DX}()

    # FK interpretation
    new_fk = Dict{Symbol, Dict{DX, DX}}()
    for (fk, (fk_src, fk_tgt)) in src.fks
        new_fk[fk] = Dict{DX, DX}()
        src_en_t = m.ens[fk_src]
        for x in carrier(alg, src_en_t)
            result_x = _eval_path_in_algebra(alg, m.fks[fk], x)
            new_fk[fk][(fk_src, x)] = (fk_tgt, result_x)
        end
    end

    # repr
    new_repr = Dict{DX, CQLTerm}()
    for (en, xs) in new_en
        for (e, x) in xs
            new_repr[(e, x)] = CQLGen(Symbol(string(e, "_", repr_x(alg, x))))
        end
    end

    # Type carriers stay the same
    new_ty = alg.ty

    # nf_y: for attributes, compose with mapping
    new_nf_y = function(e)
        if is_left(e)
            alg.nf_y(e)  # Skolems pass through
        else
            ((en, x), att) = get_right(e)
            att_term = m.atts[att]
            _eval_type_path_in_algebra(alg, att_term, x)
        end
    end

    new_alg = Algebra{DX, Y0}(
        src, new_en, new_gen, new_fk, new_repr,
        new_ty, new_nf_y, alg.repr_y, alg.teqs,
    )

    # Build presentation from algebra (including attribute equations for sigma)
    (pres, elem_to_gen) = _delta_presentation(src, new_en, new_fk, new_nf_y, alg.repr_y)

    # Populate gen mapping: generator name -> carrier element
    for (elem, g) in elem_to_gen
        new_gen[g] = elem
    end

    # Decision procedure translates back to T
    dp = function(eq)
        l_translated = _translate_delta_term(m, alg, eq.lhs)
        r_translated = _translate_delta_term(m, alg, eq.rhs)
        inst.dp(Equation(l_translated, r_translated))
    end

    CQLInstance{DX, Y0}(src, pres, dp, new_alg)
end

"""Evaluate a path term (Var/Fk chain) in an algebra starting from element x."""
function _eval_path_in_algebra(alg::Algebra, t::CQLTerm, x)
    if t isa CQLVar
        x
    elseif t isa CQLFk
        inner = _eval_path_in_algebra(alg, t.arg, x)
        eval_fk(alg, t.fk, inner)
    else
        error("Expected path term in _eval_path_in_algebra, got: $t")
    end
end

"""Evaluate a type-side term in an algebra starting from element x."""
function _eval_type_path_in_algebra(alg::Algebra, t::CQLTerm, x)::CQLTerm
    if t isa CQLAtt
        inner = _eval_path_in_algebra(alg, t.arg, x)
        eval_att(alg, t.att, inner)
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_eval_type_path_in_algebra(alg, a, x) for a in t.args])
    elseif t isa CQLVar
        repr_x(alg, x)
    else
        error("Expected type path term, got: $t")
    end
end

"""Build a presentation and element-to-generator mapping for a delta instance."""
function _delta_presentation(src, new_en, new_fk,
                             nf_y=nothing, repr_y=nothing)
    gens = Dict{Symbol, Symbol}()
    sks = Dict{Symbol, Symbol}()
    eqs = Set{Equation}()

    gen_id = Ref(0)
    elem_to_gen = Dict()
    gen_order = Symbol[]

    for (en, xs) in new_en
        for elem in xs
            gen_id[] += 1
            g = Symbol("delta_", gen_id[])
            gens[g] = en
            elem_to_gen[elem] = g
            push!(gen_order, g)
        end
    end

    for (fk, fk_map) in new_fk
        for (from_elem, to_elem) in fk_map
            if haskey(elem_to_gen, from_elem) && haskey(elem_to_gen, to_elem)
                push!(eqs, Equation(
                    CQLFk(fk, CQLGen(elem_to_gen[from_elem])),
                    CQLGen(elem_to_gen[to_elem]),
                ))
            end
        end
    end

    # Add attribute equations from algebra (needed for sigma propagation)
    if nf_y !== nothing && repr_y !== nothing
        for (att, (src_en, _)) in src.atts
            for elem in get(new_en, src_en, Set())
                g = get(elem_to_gen, elem, nothing)
                g === nothing && continue
                val = nf_y(Right((elem, att)))
                # Convert to presentation term using repr_y
                val_term = _nf_to_pres_term(val, repr_y, sks)
                push!(eqs, Equation(CQLAtt(att, CQLGen(g)), val_term))
            end
        end
    end

    (Presentation(gens, sks, eqs, gen_order), elem_to_gen)
end

"""Convert a normalized type-algebra term to a presentation term,
registering any Skolem variables encountered."""
function _nf_to_pres_term(t::CQLTerm, repr_y, sks::Dict{Symbol,Symbol})::CQLTerm
    if t isa CQLSk
        # Skolem variable — register in sks if not already there
        # Try to get the type from repr_y
        sk_name = t.sk
        if !haskey(sks, sk_name)
            # Check if repr_y maps a TalgGen with this normalized form
            # For now, keep as CQLSk and let the prover handle it
        end
        t
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_nf_to_pres_term(a, repr_y, sks) for a in t.args])
    elseif t isa CQLAtt
        # Attribute of a generator — keep as-is
        t
    else
        t
    end
end

"""Translate a delta instance term back to the target schema."""
function _translate_delta_term(m::CQLMapping, alg::Algebra, t::CQLTerm)::CQLTerm
    if t isa CQLGen
        # Look up the original element
        repr_x(alg, t.gen)  # simplified: in practice need proper mapping
    elseif t isa CQLFk
        subst_term(m.fks[t.fk], _translate_delta_term(m, alg, t.arg))
    elseif t isa CQLAtt
        subst_term(m.atts[t.att], _translate_delta_term(m, alg, t.arg))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_translate_delta_term(m, alg, a) for a in t.args])
    elseif t isa CQLSk
        t
    else
        error("Cannot translate delta term: $t")
    end
end

# ============================================================================
# Sigma (pushforward)
# ============================================================================

"""
Evaluate sigma instance: push forward an instance along a mapping.

Given F: S -> T and instance I on S, produces an instance on T by:
- Remapping generators according to F
- Rewriting equations according to F
- Computing the initial algebra of the result
"""
function eval_sigma_instance(m::CQLMapping, inst::CQLInstance, opts::CQLOptions)
    # Build sigma presentation by substituting mapping into presentation
    new_pres = _sigma_presentation(m, inst.pres)

    # Create prover and initial instance on target schema
    col = presentation_to_collage(m.dst, new_pres)
    prover = create_prover(col, opts)
    dp_fn = eq -> prover(Ctx(), eq)

    initial_instance(new_pres, dp_fn, m.dst)
end

"""Build a sigma presentation by remapping generators and equations."""
function _sigma_presentation(m::CQLMapping, pres::Presentation)::Presentation
    # Remap generators
    new_gens = Dict{Symbol,Symbol}()
    for (g, en) in pres.gens
        new_gens[g] = m.ens[en]
    end

    # Remap equations
    new_eqs = Set{Equation}()
    for eq in pres.eqs
        new_lhs = _change_en(m.fks, m.atts, eq.lhs)
        new_rhs = _change_en(m.fks, m.atts, eq.rhs)
        push!(new_eqs, Equation(new_lhs, new_rhs))
    end

    Presentation(new_gens, pres.sks, new_eqs, copy(pres.gen_order))
end

"""Rewrite a term by substituting FK and attribute references according to a mapping."""
function _change_en(fk_map, att_map, t::CQLTerm)::CQLTerm
    if t isa CQLSym
        # Avoid allocation if no args change
        changed = false
        new_args = t.args
        for (i, a) in enumerate(t.args)
            na = _change_en(fk_map, att_map, a)
            if na !== a
                if !changed
                    new_args = copy(t.args)
                    changed = true
                end
                new_args[i] = na
            end
        end
        changed ? CQLSym(t.sym, new_args) : t
    elseif t isa CQLSk
        t
    elseif t isa CQLGen
        t
    elseif t isa CQLFk
        inner = _change_en(fk_map, att_map, t.arg)
        subst_term(fk_map[t.fk], inner)
    elseif t isa CQLAtt
        inner = _change_en(fk_map, att_map, t.arg)
        subst_term(att_map[t.att], inner)
    elseif t isa CQLVar
        t  # Variables pass through unchanged
    else
        error("Cannot change_en: $t")
    end
end

# ============================================================================
# Delta/Sigma on transforms
# ============================================================================

"""Evaluate sigma on a transform."""
function eval_sigma_transform(m::CQLMapping, tr::CQLTransform, opts::CQLOptions)
    src_sigma = eval_sigma_instance(m, tr.src, opts)
    dst_sigma = eval_sigma_instance(m, tr.dst, opts)

    # Transform generators and skolems through the mapping
    new_gens = Dict{Symbol,CQLTerm}()
    for (g, term) in tr.gens
        new_gens[g] = _change_en_entity(m.fks, term)
    end

    new_sks = Dict{Symbol,CQLTerm}()
    for (s, term) in tr.sks
        new_sks[s] = _change_en(m.fks, m.atts, term)
    end

    CQLTransform(src_sigma, dst_sigma, new_gens, new_sks)
end

"""Rewrite an entity-side term according to FK mapping."""
function _change_en_entity(fk_map, t::CQLTerm)::CQLTerm
    if t isa CQLGen
        t
    elseif t isa CQLFk
        inner = _change_en_entity(fk_map, t.arg)
        subst_term(fk_map[t.fk], inner)
    else
        error("Cannot change_en_entity: $t")
    end
end

"""
Evaluate the unit of the Δ ⊣ Σ adjunction: η_I : I → Δ_F(Σ_F(I)).

Given mapping F: S → T and instance I on S, produces a transform from I
to Δ_F(Σ_F(I)) by tracing each generator through sigma then back through delta.
"""
function eval_unit_transform(m::CQLMapping, inst::CQLInstance, opts::CQLOptions)
    sigma_inst = eval_sigma_instance(m, inst, opts)
    delta_sigma = eval_delta_instance(m, sigma_inst, opts)

    # Build reverse map: delta element -> delta generator name
    elem_to_gen = Dict()
    for (g, elem) in delta_sigma.algebra.gen
        elem_to_gen[elem] = g
    end

    # For each generator g : E in I:
    #   sigma maps g to sigma_inst.algebra.gen[g] in carrier of F(E)
    #   delta has element (E, sigma_elem) in carrier of E
    gens = Dict{Symbol, CQLTerm}()
    for (g, en) in inst.pres.gens
        sigma_elem = sigma_inst.algebra.gen[g]
        delta_elem = (en, sigma_elem)
        delta_gen = elem_to_gen[delta_elem]
        gens[g] = CQLGen(delta_gen)
    end

    sks = Dict{Symbol, CQLTerm}()
    for (s, _) in inst.pres.sks
        sks[s] = CQLSk(s)
    end

    CQLTransform(inst, delta_sigma, gens, sks)
end

"""
Evaluate the counit of the Δ ⊣ Σ adjunction: ε_J : Σ_F(Δ_F(J)) → J.

Given mapping F: S → T and instance J on T, produces a transform from
Σ_F(Δ_F(J)) to J by mapping delta generators back to their original elements.
"""
function eval_counit_transform(m::CQLMapping, inst::CQLInstance, opts::CQLOptions)
    delta_inst = eval_delta_instance(m, inst, opts)
    sigma_delta = eval_sigma_instance(m, delta_inst, opts)

    # For each generator g in sigma_delta (same names as delta_inst's generators):
    #   delta_inst.algebra.gen[g] = (en_S, x) where x ∈ carrier(inst, F(en_S))
    #   Map g to repr_x(inst.algebra, x) — the J-term for element x
    gens = Dict{Symbol, CQLTerm}()
    for (g, en_T) in sigma_delta.pres.gens
        if haskey(delta_inst.algebra.gen, g)
            delta_elem = delta_inst.algebra.gen[g]
            (en_S, x) = delta_elem
            gens[g] = repr_x(inst.algebra, x)
        else
            gens[g] = CQLGen(g)
        end
    end

    sks = Dict{Symbol, CQLTerm}()
    for (s, _) in sigma_delta.pres.sks
        sks[s] = CQLSk(s)
    end

    CQLTransform(sigma_delta, inst, gens, sks)
end

"""Evaluate delta on a transform."""
function eval_delta_transform(m::CQLMapping, tr::CQLTransform, opts::CQLOptions)
    src_delta = eval_delta_instance(m, tr.src, opts)
    dst_delta = eval_delta_instance(m, tr.dst, opts)

    # Build transform between delta instances
    new_gens = Dict{Symbol,CQLTerm}()
    for (g, en) in src_delta.pres.gens
        # Map generator through original transform's algebra
        # This is the categorical construction
        new_gens[g] = CQLGen(g)  # Simplified; proper impl traces through algebras
    end

    new_sks = Dict{Symbol,CQLTerm}()
    for (s, _) in src_delta.pres.sks
        new_sks[s] = CQLSk(s)
    end

    CQLTransform(src_delta, dst_delta, new_gens, new_sks)
end
