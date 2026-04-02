"""Evaluate a query expression."""
function eval_query(env::Env, e::QueryExp)::CQLQuery
    if e isa QueryVar
        haskey(env.queries, e.name) || throw(CQLException("Undefined query: $(e.name)"))
        env.queries[e.name]
    elseif e isa QueryId
        sch = eval_schema(env, e.schema)
        identity_query(sch)
    elseif e isa QueryRawExp
        raw = e.raw
        src = eval_schema(env, raw.src_ref)
        # Check for simple query: auto-generate target schema
        if length(raw.ens) == 1 && raw.ens[1][1] == "__simple__"
            dst = _build_simple_query_target(src, raw)
            eval_query_raw(src, dst, raw)
        else
            dst = eval_schema(env, raw.dst_ref)
            eval_query_raw(src, dst, raw)
        end
    elseif e isa QueryComp
        f = eval_query(env, e.first)
        g = eval_query(env, e.second)
        compose_query(f, g)
    elseif e isa QueryToQuery
        m = eval_mapping(env, e.mapping)
        mapping_to_query(m)
    elseif e isa QueryToCoQuery
        m = eval_mapping(env, e.mapping)
        _delta_coeval_query(m, env.options)
    elseif e isa QueryFront
        haskey(env.constraints, e.constraints_name) || throw(CQLException("Undefined constraints: $(e.constraints_name)"))
        c = env.constraints[e.constraints_name]
        _eval_query_front_back(c, e.index, false)
    elseif e isa QueryBack
        haskey(env.constraints, e.constraints_name) || throw(CQLException("Undefined constraints: $(e.constraints_name)"))
        c = env.constraints[e.constraints_name]
        _eval_query_front_back(c, e.index, true)
    elseif e isa QueryRext
        q1 = eval_query(env, e.q1)
        q2 = eval_query(env, e.q2)
        _eval_rext(q1, q2, env.options)
    elseif e isa QuerySpanify
        sch = eval_schema(env, e.schema)
        _eval_query_spanify(sch)
    elseif e isa QuerySpanifyMapping
        m = eval_mapping(env, e.mapping)
        _eval_query_spanify_mapping(m)
    elseif e isa QueryInclude
        src = eval_schema(env, e.src_schema)
        tgt = eval_schema(env, e.tgt_schema)
        _include_query(src, tgt)
    elseif e isa QueryFromCoSpan
        m1 = eval_mapping(env, e.m1)
        m2 = eval_mapping(env, e.m2)
        # fromCoSpan(M1: S1→C, M2: S2→C) = deltaCoEval(M1) ; deltaEval(M2)
        # Verify cospan: both mappings must share the same target schema
        m1.dst == m2.dst || throw(CQLException(
            "Cannot co-span: target of first mapping is not the same as target of second"))
        q1 = _delta_coeval_query(m1, env.options)  # S1 → C
        q2 = mapping_to_query(m2)                   # C → S2
        compose_query(q1, q2)                        # S1 → S2
    elseif e isa QueryFromConstraints
        haskey(env.constraints, e.constraints_name) || throw(CQLException(
            "Undefined constraints: $(e.constraints_name)"))
        c = env.constraints[e.constraints_name]
        _eval_query_from_constraints(c, e.index, env.options)
    elseif e isa QueryChase
        c = _resolve_constraints(env, e.constraints)
        q = eval_query(env, e.query)
        _chase_query(q, c, env.options)
    elseif e isa QueryReformulate
        c = _resolve_constraints(env, e.constraints)
        q = eval_query(env, e.query)
        t = eval_schema(env, e.schema)
        _reformulate_query(q, c, t, e.index, env.options)
    else
        throw(CQLException("Unknown query expression"))
    end
end

"""Resolve a constraints reference to a CQLConstraints object."""
function _resolve_constraints(env::Env, ref)::CQLConstraints
    if ref isa String
        haskey(env.constraints, ref) || throw(CQLException("Undefined constraints: $ref"))
        env.constraints[ref]
    else
        throw(CQLException("Expected constraints name, got: $ref"))
    end
end

# ============================================================================
# Query-level chase: chase each entity block's frozen instance with constraints
# ============================================================================

"""Chase a query with constraints: for each entity block, freeze it into an instance,
chase with constraints, and rebuild the query from the chased result."""
function _chase_query(q::CQLQuery, c::CQLConstraints, opts::CQLOptions)::CQLQuery
    # Only single-entity queries supported (matching Java)
    isempty(q.src.fks) || throw(CQLException("Fks not supported in chase query"))
    isempty(q.dst.fks) || throw(CQLException("Fks not supported in chase query"))

    new_ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}()
    new_atts = Dict{Symbol, CQLTerm}()
    vcounter = Ref(0)

    for (en, (ctx, where_eqs)) in q.ens
        # Build a frozen instance from this entity block
        gens = Dict{Symbol, Symbol}()
        sks = Dict{Symbol, Symbol}()
        for (v, entity) in ctx
            if entity in q.src.ens
                gens[v] = entity
            else
                sks[v] = entity
            end
        end

        inst_eqs = Set{Equation}()
        for eq in where_eqs
            lhs = _vars_to_gens_sks(eq.lhs, gens, sks)
            rhs = _vars_to_gens_sks(eq.rhs, gens, sks)
            push!(inst_eqs, Equation(lhs, rhs))
        end

        pres = Presentation(gens, sks, inst_eqs)

        if isempty(gens) && isempty(sks)
            new_ens[en] = (Dict{Symbol,Symbol}(), Set{Equation}())
            continue
        end

        # Build and chase the frozen instance
        col = presentation_to_collage(q.src, pres)
        prover = create_prover(col, opts)
        dp_fn = eq -> prover(Ctx(), eq)
        frozen_inst = initial_instance(pres, dp_fn, q.src; timeout_seconds=5, max_carrier_size=50)

        chased = chase(c, frozen_inst, opts)

        # Build gen/sk renaming maps from chased instance to fresh variable names
        gen_map = Dict{Symbol, Symbol}()
        sk_map = Dict{Symbol, Symbol}()
        new_ctx = Dict{Symbol, Symbol}()

        for (g, entity) in chased.pres.gens
            vcounter[] += 1
            fresh = Symbol("v", vcounter[])
            gen_map[g] = fresh
            new_ctx[fresh] = entity
        end
        for (s, ty) in chased.pres.sks
            vcounter[] += 1
            fresh = Symbol("v", vcounter[])
            sk_map[s] = fresh
            new_ctx[fresh] = ty
        end

        # Map equations through renaming
        new_where = Set{Equation}()
        for eq in chased.pres.eqs
            lhs = _rename_gen_sk(eq.lhs, gen_map, sk_map)
            rhs = _rename_gen_sk(eq.rhs, gen_map, sk_map)
            if lhs != rhs
                push!(new_where, Equation(lhs, rhs))
            end
        end

        new_ens[en] = (new_ctx, new_where)

        # Transform attribute terms through the chase
        # The chase produces a transform (identity on gens that survive):
        # we need to translate the original att terms through the chased instance
        for (att, _) in schema_atts_from(q.dst, en)
            if haskey(q.atts, att)
                orig_att_term = q.atts[att]
                # Translate through chase: substitute gens/sks with their chased representatives
                trans_term = _translate_through_chase(orig_att_term, chased, gens, sks)
                new_atts[att] = _rename_gen_sk(trans_term, gen_map, sk_map)
            end
        end
    end

    CQLQuery(q.src, q.dst, new_ens, Dict{Symbol,Dict{Symbol,CQLTerm}}(), new_atts)
end

"""Rename generators and skolems in a term."""
function _rename_gen_sk(t::CQLTerm, gen_map::Dict{Symbol,Symbol}, sk_map::Dict{Symbol,Symbol})::CQLTerm
    if t isa CQLGen
        haskey(gen_map, t.gen) ? CQLVar(gen_map[t.gen]) : CQLVar(t.gen)
    elseif t isa CQLSk
        haskey(sk_map, t.sk) ? CQLVar(sk_map[t.sk]) : CQLVar(t.sk)
    elseif t isa CQLVar
        t
    elseif t isa CQLFk
        CQLFk(t.fk, _rename_gen_sk(t.arg, gen_map, sk_map))
    elseif t isa CQLAtt
        CQLAtt(t.att, _rename_gen_sk(t.arg, gen_map, sk_map))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_rename_gen_sk(a, gen_map, sk_map) for a in t.args])
    else
        t
    end
end

"""Translate an attribute term through a chased instance.
The original term uses CQLVar names from the query context;
we convert to CQLGen/CQLSk then evaluate through the chased algebra."""
function _translate_through_chase(t::CQLTerm, chased::CQLInstance,
                                   gens::Dict{Symbol,Symbol}, sks::Dict{Symbol,Symbol})::CQLTerm
    # Convert query variables to instance generators/skolems
    inst_term = _vars_to_gens_sks(t, gens, sks)
    # Normalize through the chased instance's algebra
    _nf_through_instance(inst_term, chased)
end

"""Normalize a term through an instance's algebra, returning a term in gens/sks."""
function _nf_through_instance(t::CQLTerm, inst::CQLInstance)::CQLTerm
    if t isa CQLGen
        # Map through gen interpretation and back to repr
        if haskey(inst.algebra.gen, t.gen)
            x = inst.algebra.gen[t.gen]
            return inst.algebra.repr_x[x]
        end
        return t
    elseif t isa CQLSk
        return t
    elseif t isa CQLFk
        inner = _nf_through_instance(t.arg, inst)
        if inner isa CQLGen && haskey(inst.algebra.gen, inner.gen)
            x = inst.algebra.gen[inner.gen]
            if haskey(inst.algebra.fk, t.fk) && haskey(inst.algebra.fk[t.fk], x)
                result_x = inst.algebra.fk[t.fk][x]
                return inst.algebra.repr_x[result_x]
            end
        end
        return CQLFk(t.fk, inner)
    elseif t isa CQLAtt
        inner = _nf_through_instance(t.arg, inst)
        if inner isa CQLGen && haskey(inst.algebra.gen, inner.gen)
            x = inst.algebra.gen[inner.gen]
            if haskey(inst.algebra.repr_y, TalgGen(Right((x, t.att))))
                return inst.algebra.repr_y[TalgGen(Right((x, t.att)))]
            end
        end
        return CQLAtt(t.att, inner)
    elseif t isa CQLSym
        return CQLSym(t.sym, CQLTerm[_nf_through_instance(a, inst) for a in t.args])
    else
        return t
    end
end

# ============================================================================
# Reformulate: find minimal equivalent sub-queries
# ============================================================================

"""Reformulate query: find the N-th minimal sub-query equivalent to Q under constraints C,
preferring queries whose generators are in schema T."""
function _reformulate_query(q::CQLQuery, c::CQLConstraints, t::CQLSchema, idx::Int,
                            opts::CQLOptions)::CQLQuery
    length(q.ens) == 1 || throw(CQLException("Reformulate only supports single-entity queries"))
    isempty(q.src.fks) || throw(CQLException("Fks not supported in reformulate"))
    isempty(q.dst.fks) || throw(CQLException("Fks not supported in reformulate"))

    en_name = first(keys(q.ens))
    (ctx, where_eqs) = q.ens[en_name]

    # Classify context variables as entity-generators or type-skolems
    gens_set = Set{Symbol}()  # entity-sorted variables
    sks_set = Set{Symbol}()   # type-sorted variables
    for (v, entity) in ctx
        if entity in q.src.ens
            push!(gens_set, v)
        else
            push!(sks_set, v)
        end
    end

    # Build all candidate subsets of context variables
    all_vars = collect(keys(ctx))
    candidates = _power_set(all_vars)
    sort!(candidates; by=length)

    minimal_queries = CQLQuery[]

    for cand in candidates
        cand_set = Set(cand)

        # Build restricted context
        sub_ctx = Dict{Symbol,Symbol}(v => ctx[v] for v in cand if haskey(ctx, v))

        # Try to rewrite attribute terms using only candidate variables
        sub_gens = Dict{Symbol,Symbol}(v => ctx[v] for v in cand if v in gens_set)
        sub_sks = Dict{Symbol,Symbol}(v => ctx[v] for v in cand if v in sks_set)

        att_terms = Pair{Symbol, CQLTerm}[]
        valid = true
        for (att, term) in q.atts
            rewritten = _rewrite_term_to_subset(term, where_eqs, q.src, sub_gens, sub_sks, cand_set)
            if rewritten === nothing
                valid = false
                break
            end
            push!(att_terms, att => rewritten)
        end
        valid || continue

        # Extract equations that hold within the subset
        sub_where = Set{Equation}()
        for eq in where_eqs
            if _term_uses_only(eq.lhs, cand_set) && _term_uses_only(eq.rhs, cand_set)
                push!(sub_where, eq)
            end
        end

        sub_ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}(
            en_name => (sub_ctx, sub_where)
        )
        sub_atts = Dict{Symbol, CQLTerm}(att_terms)
        sub_q = CQLQuery(q.src, q.dst, sub_ens, Dict{Symbol,Dict{Symbol,CQLTerm}}(), sub_atts)

        # Check bidirectional containment under constraints
        # sq ⊆_C q: find hom from q into chase(sq, C)
        # q ⊆_C sq: find hom from sq into chase(q, C)
        chased_sq = _chase_query(sub_q, c, opts)
        if _query_hom(q, chased_sq, opts) === nothing
            continue
        end

        chased_q = _chase_query(q, c, opts)
        if _query_hom(sub_q, chased_q, opts) !== nothing
            push!(minimal_queries, sub_q)
        end
    end

    isempty(minimal_queries) && throw(CQLException(
        "No equivalent minimal queries found (index $idx)"))

    # Score and sort: prefer queries with fewer generators outside T
    sort!(minimal_queries; by = mq -> begin
        s = _score_query(mq, t)
        n = sum(length(ctx2) for (_, (ctx2, _)) in mq.ens; init=0)
        (s, n)
    end)

    idx < length(minimal_queries) || throw(CQLException(
        "Reformulate index $idx out of range (only $(length(minimal_queries)) candidates)"))

    minimal_queries[idx + 1]  # 0-indexed in CQL syntax
end

"""Score a query by counting generators outside schema T."""
function _score_query(q::CQLQuery, t::CQLSchema)::Int
    count = 0
    for (_, (ctx, _)) in q.ens
        for (_, entity) in ctx
            if !(entity in t.ens)
                count += 1
            end
        end
    end
    count
end

"""Generate the power set of a vector."""
function _power_set(items::Vector{T}) where T
    result = Vector{T}[]
    n = length(items)
    for mask in 0:(2^n - 1)
        subset = T[]
        for i in 1:n
            if (mask >> (i-1)) & 1 == 1
                push!(subset, items[i])
            end
        end
        push!(result, subset)
    end
    result
end

"""Check if a term only uses variables from the given set."""
function _term_uses_only(t::CQLTerm, vars::Set{Symbol})::Bool
    if t isa CQLVar
        t.name in vars
    elseif t isa CQLFk
        _term_uses_only(t.arg, vars)
    elseif t isa CQLAtt
        _term_uses_only(t.arg, vars)
    elseif t isa CQLSym
        all(a -> _term_uses_only(a, vars), t.args)
    elseif t isa CQLGen || t isa CQLSk
        true  # constants don't reference variables
    else
        true
    end
end

"""Try to rewrite a term so it only references variables in the subset.
Uses the where-clause equations and the decision procedure to find equivalent terms."""
function _rewrite_term_to_subset(t::CQLTerm, where_eqs::Set{Equation}, src::CQLSchema,
                                  sub_gens::Dict{Symbol,Symbol}, sub_sks::Dict{Symbol,Symbol},
                                  cand_set::Set{Symbol})::Union{CQLTerm, Nothing}
    if _term_uses_only(t, cand_set)
        return t
    end

    # For attribute terms Att(att, Var(v)) where v is not in subset:
    # try to find an equivalent att on a variable that IS in the subset
    if t isa CQLAtt && t.arg isa CQLVar && !(t.arg.name in cand_set)
        # Find a generator in subset of the same entity with a provably-equal attribute
        missing_var = t.arg.name
        for (v, en) in sub_gens
            # Check if any equation in where_eqs implies att(v) = att(missing_var)
            # by looking for equations like v.fk = missing_var or direct equality
            for eq in where_eqs
                matched = _match_att_rewrite(t, v, eq)
                if matched !== nothing
                    return matched
                end
            end
            # Also try direct attribute on same-type generators
            for (a, (src_en, _)) in src.atts
                if a == t.att && src_en == en
                    candidate = CQLAtt(a, CQLVar(v))
                    # Check via where-clause if this is equivalent
                    if _terms_equal_via_where(t, candidate, where_eqs, src)
                        return candidate
                    end
                end
            end
        end
        return nothing
    end

    if t isa CQLSym
        new_args = CQLTerm[]
        for a in t.args
            ra = _rewrite_term_to_subset(a, where_eqs, src, sub_gens, sub_sks, cand_set)
            ra === nothing && return nothing
            push!(new_args, ra)
        end
        return CQLSym(t.sym, new_args)
    end

    if t isa CQLFk
        ra = _rewrite_term_to_subset(t.arg, where_eqs, src, sub_gens, sub_sks, cand_set)
        ra === nothing && return nothing
        return CQLFk(t.fk, ra)
    end

    nothing
end

"""Try to match an attribute rewrite through an equation."""
function _match_att_rewrite(t::CQLTerm, candidate_var::Symbol, eq::Equation)::Union{CQLTerm, Nothing}
    # If equation is v.att = x.att or similar, and t references x, try v
    nothing
end

"""Check if two terms are equal given where-clause equations (syntactic check)."""
function _terms_equal_via_where(t1::CQLTerm, t2::CQLTerm, where_eqs::Set{Equation},
                                 src::CQLSchema)::Bool
    t1 == t2 && return true
    for eq in where_eqs
        if (eq.lhs == t1 && eq.rhs == t2) || (eq.lhs == t2 && eq.rhs == t1)
            return true
        end
    end
    false
end

"""Find a homomorphism from query q1 into query q2, or return nothing.
A homomorphism maps q1's generators/skolems to q2's such that equations are preserved."""
function _query_hom(q1::CQLQuery, q2::CQLQuery, opts::CQLOptions)
    q1.ens |> keys |> collect |> sort == q2.ens |> keys |> collect |> sort || return nothing
    length(q1.ens) == 1 || return nothing

    en = first(keys(q1.ens))
    (ctx1, where1) = q1.ens[en]
    (ctx2, where2) = q2.ens[en]

    # Build candidate mappings: each q1 variable maps to a q2 variable of same type
    vars1 = collect(ctx1)
    if isempty(vars1)
        # Check attributes match
        for (att, t1) in q1.atts
            haskey(q2.atts, att) || return nothing
            t1 == q2.atts[att] || return nothing
        end
        return Dict{Symbol,Symbol}()
    end

    # Build frozen instances for both queries
    gens1 = Dict{Symbol,Symbol}(v => en for (v, en) in ctx1 if en in q1.src.ens)
    sks1 = Dict{Symbol,Symbol}(v => en for (v, en) in ctx1 if !(en in q1.src.ens))
    gens2 = Dict{Symbol,Symbol}(v => en for (v, en) in ctx2 if en in q2.src.ens)
    sks2 = Dict{Symbol,Symbol}(v => en for (v, en) in ctx2 if !(en in q2.src.ens))

    # Build all possible assignments of q1 entity-gens to q2 entity-gens (same entity type)
    assignments = [Dict{Symbol,Symbol}()]
    for (g1, en1) in gens1
        new_assignments = Dict{Symbol,Symbol}[]
        for (g2, en2) in gens2
            if en1 == en2
                for a in assignments
                    na = copy(a)
                    na[g1] = g2
                    push!(new_assignments, na)
                end
            end
        end
        isempty(new_assignments) && return nothing
        assignments = new_assignments
    end

    # Also map skolems
    for (s1, ty1) in sks1
        new_assignments = Dict{Symbol,Symbol}[]
        for (s2, ty2) in sks2
            if ty1 == ty2
                for a in assignments
                    na = copy(a)
                    na[s1] = s2
                    push!(new_assignments, na)
                end
            end
        end
        isempty(new_assignments) && return nothing
        assignments = new_assignments
    end

    # Build frozen instance for q2 to check equations
    inst2_eqs = Set{Equation}()
    for eq in where2
        lhs = _vars_to_gens_sks(eq.lhs, gens2, sks2)
        rhs = _vars_to_gens_sks(eq.rhs, gens2, sks2)
        push!(inst2_eqs, Equation(lhs, rhs))
    end
    pres2 = Presentation(gens2, sks2, inst2_eqs)

    # Build prover for q2
    local dp2
    try
        col2 = presentation_to_collage(q2.src, pres2)
        prover2 = create_prover(col2, opts)
        dp2 = eq -> prover2(Ctx(), eq)
    catch
        return nothing
    end

    inst2 = try
        initial_instance(pres2, dp2, q2.src; timeout_seconds=5, max_carrier_size=50)
    catch
        return nothing
    end

    # Try each candidate assignment
    for assign in assignments
        valid = true

        # Check where-clause equations are preserved
        for eq in where1
            lhs1 = _vars_to_gens_sks(eq.lhs, gens1, sks1)
            rhs1 = _vars_to_gens_sks(eq.rhs, gens1, sks1)
            lhs2 = _apply_gen_sk_mapping(lhs1, assign)
            rhs2 = _apply_gen_sk_mapping(rhs1, assign)
            if !dp2(Equation(lhs2, rhs2))
                valid = false
                break
            end
        end
        valid || continue

        # Check attribute terms are preserved
        all_atts_ok = true
        for (att, t1) in q1.atts
            haskey(q2.atts, att) || (all_atts_ok = false; break)
            t2 = q2.atts[att]
            # Apply assignment to t1
            mapped_t1 = _apply_var_mapping(t1, assign)
            inst_t1 = _vars_to_gens_sks(mapped_t1, gens2, sks2)
            inst_t2 = _vars_to_gens_sks(t2, gens2, sks2)
            if !dp2(Equation(inst_t1, inst_t2))
                all_atts_ok = false
                break
            end
        end
        all_atts_ok || continue

        return assign
    end

    nothing
end

"""Apply a variable-to-variable mapping to a term."""
function _apply_var_mapping(t::CQLTerm, mapping::Dict{Symbol,Symbol})::CQLTerm
    if t isa CQLVar
        haskey(mapping, t.name) ? CQLVar(mapping[t.name]) : t
    elseif t isa CQLFk
        CQLFk(t.fk, _apply_var_mapping(t.arg, mapping))
    elseif t isa CQLAtt
        CQLAtt(t.att, _apply_var_mapping(t.arg, mapping))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_apply_var_mapping(a, mapping) for a in t.args])
    else
        t
    end
end

"""Apply a gen/sk name mapping to an instance-level term."""
function _apply_gen_sk_mapping(t::CQLTerm, mapping::Dict{Symbol,Symbol})::CQLTerm
    if t isa CQLGen
        haskey(mapping, t.gen) ? CQLGen(mapping[t.gen]) : t
    elseif t isa CQLSk
        haskey(mapping, t.sk) ? CQLSk(mapping[t.sk]) : t
    elseif t isa CQLFk
        CQLFk(t.fk, _apply_gen_sk_mapping(t.arg, mapping))
    elseif t isa CQLAtt
        CQLAtt(t.att, _apply_gen_sk_mapping(t.arg, mapping))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_apply_gen_sk_mapping(a, mapping) for a in t.args])
    else
        t
    end
end

"""Build target schema for a simple query: one entity with attributes inferred from query definition."""
function _build_simple_query_target(src::CQLSchema, raw::QueryExpRaw)::CQLSchema
    ts = src.typeside

    # Get entity name from options
    en_name = :Q  # default
    for (k, v) in raw.options
        if k == "simple_query_entity"
            en_name = Symbol(v)
        end
    end

    ens = Set{Symbol}([en_name])
    fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    atts = Dict{Symbol, Tuple{Symbol, Symbol}}()

    (from_bindings, _, att_raw, fk_raw) = raw.ens[1][2]

    # Build from-clause context for type inference
    ctx = Dict{Symbol,Symbol}()
    for (v, e) in from_bindings
        ctx[Symbol(v)] = Symbol(e)
    end

    # Infer attribute types from source schema terms
    for (att_name, att_term_raw) in att_raw
        att_type = _infer_raw_term_type(src, ctx, att_term_raw)
        atts[Symbol(att_name)] = (en_name, att_type)
    end

    # FK mappings define foreign keys on the target
    for (fk_name, _) in fk_raw
        fks[Symbol(fk_name)] = (en_name, en_name)  # self-referencing by default
    end

    eq_fn = (en, eq) -> false
    CQLSchema(ts, ens, fks, atts, Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(), eq_fn)
end

"""Infer the type of a raw term in the context of a source schema."""
function _infer_raw_term_type(src::CQLSchema, ctx::Dict{Symbol,Symbol}, raw::RawTerm)::Symbol
    s = Symbol(raw.head)
    if isempty(raw.args)
        # Variable or constant
        if haskey(ctx, s) && s in src.ens
            return s
        end
        # Unknown — return first typeside type as default
        return isempty(src.typeside.tys) ? :String : first(src.typeside.tys)
    elseif length(raw.args) == 1
        if haskey(src.atts, s)
            return src.atts[s][2]  # return type of attribute
        elseif haskey(src.fks, s)
            return src.fks[s][2]  # target entity of FK
        end
        # Check if parent has the info
        inner_entity = _infer_raw_term_entity(src, ctx, raw.args[1])
        if inner_entity !== nothing
            # Try to find att/fk from this entity
            if haskey(src.atts, s)
                return src.atts[s][2]
            end
        end
    end
    # Default fallback
    isempty(src.typeside.tys) ? :String : first(src.typeside.tys)
end

"""Infer the entity type of a raw term."""
function _infer_raw_term_entity(src::CQLSchema, ctx::Dict{Symbol,Symbol}, raw::RawTerm)::Union{Symbol, Nothing}
    s = Symbol(raw.head)
    if isempty(raw.args) && haskey(ctx, s)
        return ctx[s]
    elseif length(raw.args) == 1 && haskey(src.fks, s)
        return src.fks[s][2]
    end
    nothing
end

