"""
Database instances on schemas.

An instance consists of:
- A schema
- A presentation (generators + equations)
- A decision procedure
- An algebra (semantic model)
"""

"""A CQL database instance."""
struct CQLInstance{X, Y}
    schema::CQLSchema
    pres::Presentation
    dp::Function              # (eq::Equation) -> Bool (ground equation decision procedure)
    algebra::Algebra{X, Y}
end

function Base.show(io::IO, inst::CQLInstance)
    println(io, "instance {")
    println(io, "  ", inst.pres)
    println(io, "  algebra {")
    for (en, xs) in inst.algebra.en
        println(io, "    ", en, " (", length(xs), " rows)")
        for x in xs
            fk_strs = [string(fk, "=", eval_fk(inst.algebra, fk, x))
                       for (fk, _) in schema_fks_from(inst.schema, en)]
            att_strs = [string(att, "=", eval_att(inst.algebra, att, x))
                        for (att, _) in schema_atts_from(inst.schema, en)]
            println(io, "      ", repr_x(inst.algebra, x), ": ", join(vcat(fk_strs, att_strs), ", "))
        end
    end
    println(io, "  }")
    println(io, "}")
end

# ============================================================================
# Empty instance
# ============================================================================

"""Create an empty instance on a schema."""
function empty_instance(sch::CQLSchema)
    en = Dict{Symbol, Set{Nothing}}(e => Set{Nothing}() for e in sch.ens)
    ty = Dict{Symbol, Set{Nothing}}(t => Set{Nothing}() for t in sch.typeside.tys)
    alg = Algebra{Nothing, Nothing}(
        sch, en,
        Dict{Symbol,Nothing}(),
        Dict{Symbol,Dict{Nothing,Nothing}}(),
        Dict{Nothing,CQLTerm}(),
        ty, _ -> error("empty"), Dict{Nothing,CQLTerm}(), Set{Equation}(),
    )
    CQLInstance{Nothing, Nothing}(sch, Presentation(Dict{Symbol,Symbol}(), Dict{Symbol,Symbol}(), Set{Equation}()),
                                   eq -> false, alg)
end

# ============================================================================
# Initial algebra / term model
# ============================================================================

"""Compute the initial instance (term model) from a presentation."""
function initial_instance(pres::Presentation, dp_fn::Function, sch::CQLSchema;
                          timeout_seconds::Real=30, max_carrier_size::Int=10000,
                          canonical_fn=nothing)
    col = presentation_to_collage(sch, pres)

    # Close generators under foreign keys
    (carriers, timed_out) = _close_carriers(col, dp_fn;
        timeout_seconds=timeout_seconds, max_size=max_carrier_size,
        gen_order=pres.gen_order, canonical_fn=canonical_fn)

    if timed_out
        # Extend carriers one more step so all FK applications are included
        extended = CQLTerm[]
        for c in carriers
            push!(extended, c)
            en = type_of_entity_term(col, c)
            for (fk, _) in fks_from(col, en)
                push!(extended, CQLFk(fk, c))
            end
        end
        carriers = _dedup(extended, dp_fn)
    end

    ens_map = assemble_gens(col, carriers)

    # Build FK interpretation
    # Pre-build canonical indices for O(1) nf lookup
    canonical_indices = if canonical_fn !== nothing
        Dict(en => _build_canonical_index(cs, canonical_fn) for (en, cs) in ens_map)
    else
        nothing
    end

    fk_dict = Dict{Symbol, Dict{CQLTerm, CQLTerm}}()
    for (fk, (src, tgt)) in sch.fks
        fk_dict[fk] = Dict{CQLTerm, CQLTerm}()
        tgt_carriers = get(ens_map, tgt, Set{CQLTerm}())
        cidx = canonical_indices !== nothing ? get(canonical_indices, tgt, nothing) : nothing
        for x in get(ens_map, src, Set{CQLTerm}())
            fk_x = CQLFk(fk, x)
            nf_x = _find_nf(fk_x, tgt_carriers, dp_fn; lenient=timed_out,
                            canonical_fn=canonical_fn, _canonical_index=cidx)
            if timed_out && !(nf_x in tgt_carriers)
                push!(tgt_carriers, nf_x)
            end
            fk_dict[fk][x] = nf_x
        end
    end

    # Build gen interpretation
    gen_dict = Dict{Symbol, CQLTerm}()
    for (g, en) in pres.gens
        gen_term = CQLGen(g)
        cidx = canonical_indices !== nothing ? get(canonical_indices, en, nothing) : nothing
        gen_dict[g] = _find_nf(gen_term, ens_map[en], dp_fn; lenient=timed_out,
                               canonical_fn=canonical_fn, _canonical_index=cidx)
    end

    # Build repr (identity for term model)
    repr_dict = Dict{CQLTerm, CQLTerm}()
    for (_, xs) in ens_map
        for x in xs
            repr_dict[x] = x
        end
    end

    # Build type algebra
    talg_gens = Dict{Symbol, Set{TalgGen}}()
    for ty in sch.typeside.tys
        talg_gens[ty] = Set{TalgGen}()
    end
    # Add typeside constants (0-arg symbols like true:Bool, false:Bool)
    for (sym_name, (arg_tys, ret_ty)) in sch.typeside.syms
        if isempty(arg_tys)
            push!(talg_gens[ret_ty], TalgGen(Left(sym_name)))
        end
    end
    # Add skolem generators
    for (sk, ty) in pres.sks
        push!(talg_gens[ty], TalgGen(Left(sk)))
    end
    # Add attribute generators
    for (en, xs) in ens_map
        for x in xs
            for (att, ty) in schema_atts_from(sch, en)
                push!(talg_gens[ty], TalgGen(Right((x, att))))
            end
        end
    end

    # Build nf_y function
    ts_syms = sch.typeside.syms
    nf_y_fn = function(e)
        if is_left(e)
            name = get_left(e)
            # Typeside constants use CQLSym, Skolems use CQLSk
            if haskey(ts_syms, name) && isempty(ts_syms[name][1])
                CQLSym(name, CQLTerm[])
            else
                CQLSk(name)
            end
        else
            (x, att) = get_right(e)
            CQLSk(Symbol(string(x, ".", att)))
        end
    end

    # Build repr_y
    repr_y_dict = Dict{TalgGen, CQLTerm}()
    for (_, tgs) in talg_gens
        for tg in tgs
            if is_left(tg.val)
                name = get_left(tg.val)
                # Typeside constants (0-arg symbols) use CQLSym, Skolems use CQLSk
                if haskey(sch.typeside.syms, name) && isempty(sch.typeside.syms[name][1])
                    repr_y_dict[tg] = CQLSym(name, CQLTerm[])
                else
                    repr_y_dict[tg] = CQLSk(name)
                end
            else
                (x, att) = get_right(tg.val)
                repr_y_dict[tg] = CQLAtt(att, x)
            end
        end
    end

    # Compute type algebra equations
    teqs = Set{Equation}()
    for (en, eq) in sch.obs_eqs
        for x in get(ens_map, en, Set{CQLTerm}())
            lhs = _eval_schema_type_term(x, eq.lhs, fk_dict, nf_y_fn)
            rhs = _eval_schema_type_term(x, eq.rhs, fk_dict, nf_y_fn)
            if lhs != rhs
                push!(teqs, Equation(lhs, rhs))
            end
        end
    end
    # Add type equations from instance (evaluated through algebra to Skolem form)
    for eq in pres.eqs
        if has_type_type(eq.lhs)
            lhs = _eval_pres_type_term(eq.lhs, gen_dict, fk_dict, nf_y_fn)
            rhs = _eval_pres_type_term(eq.rhs, gen_dict, fk_dict, nf_y_fn)
            if lhs != rhs
                push!(teqs, Equation(lhs, rhs))
            end
        end
    end

    alg = Algebra{CQLTerm, TalgGen}(
        sch, ens_map, gen_dict, fk_dict, repr_dict,
        talg_gens, nf_y_fn, repr_y_dict, teqs,
    )

    # Simplify the algebra
    alg = simplify_algebra(alg)

    CQLInstance{CQLTerm, TalgGen}(sch, pres, dp_fn, alg)
end

"""Close carriers under foreign keys to fixed point.
Returns (carriers, timed_out) where timed_out indicates partial result."""
function _close_carriers(col::Collage, dp_fn::Function;
                         timeout_seconds::Real=30, max_size::Int=10000,
                         gen_order::Vector{Symbol}=Symbol[],
                         canonical_fn=nothing)::Tuple{Vector{CQLTerm}, Bool}
    # Use gen_order for deterministic iteration if provided; else fall back to keys
    ordered_gens = if !isempty(gen_order)
        gen_order
    else
        collect(keys(col.cgens))
    end
    carriers = CQLTerm[CQLGen(g) for g in ordered_gens if haskey(col.cgens, g)]
    start_time = time()

    # Build per-entity carrier lists for efficient dedup (avoid cross-entity comparisons)
    carriers_by_en = Dict{Symbol, Vector{CQLTerm}}()
    for c in carriers
        en = type_of_entity_term(col, c)
        push!(get!(Vector{CQLTerm}, carriers_by_en, en), c)
    end

    while true
        new_by_en = Dict{Symbol, Vector{CQLTerm}}()
        for (en, cs) in carriers_by_en
            new_cs = get!(Vector{CQLTerm}, new_by_en, en)
            for c in cs
                push!(new_cs, c)
                for (fk, tgt_en) in fks_from(col, en)
                    push!(get!(Vector{CQLTerm}, new_by_en, tgt_en), CQLFk(fk, c))
                end
            end
        end

        # Dedup per entity and check fixed point
        changed = false
        for (en, cs) in new_by_en
            deduped = _dedup(cs, dp_fn; canonical_fn=canonical_fn)
            new_by_en[en] = deduped
            old_len = length(get(carriers_by_en, en, CQLTerm[]))
            if length(deduped) != old_len
                changed = true
            end
        end

        if !changed
            # Flatten back to ordered list
            carriers = CQLTerm[]
            for en in sort!(collect(keys(new_by_en)))
                append!(carriers, new_by_en[en])
            end
            return (carriers, false)
        end

        carriers_by_en = new_by_en
        total = sum(length(v) for v in values(carriers_by_en))
        if total > max_size || time() - start_time > timeout_seconds
            carriers = CQLTerm[]
            for en in sort!(collect(keys(carriers_by_en)))
                append!(carriers, carriers_by_en[en])
            end
            return (carriers, true)
        end
    end
end

"""Deduplicate carriers by provable equality.

When canonical_fn is provided (from congruence prover), uses O(n) hash-based grouping.
Otherwise, O(n×k) pairwise comparison with early termination."""
function _dedup(carriers::Vector{CQLTerm}, dp_fn::Function;
                canonical_fn=nothing)::Vector{CQLTerm}
    # Fast path: canonical ID-based grouping (O(n) instead of O(n*k))
    if canonical_fn !== nothing
        seen = Dict{Int, CQLTerm}()
        result = CQLTerm[]
        for c in carriers
            cid = canonical_fn(c)::Int
            if !haskey(seen, cid)
                seen[cid] = c
                push!(result, c)
            end
        end
        return result
    end

    result = CQLTerm[]
    for c in carriers
        found = false
        for r in result
            # Quick structural equality check first (avoids expensive dp_fn)
            if c == r || dp_fn(Equation(c, r))
                found = true
                break
            end
        end
        if !found
            push!(result, c)
        end
    end
    result
end

"""Find the normal form of a term among a set of representatives."""
function _find_nf(t::CQLTerm, representatives::Set{CQLTerm}, dp_fn::Function;
                  lenient::Bool=false, canonical_fn=nothing,
                  _canonical_index=nothing)::CQLTerm
    # Fast path: use canonical IDs for O(1) lookup
    if canonical_fn !== nothing
        t_id = canonical_fn(t)::Int
        if _canonical_index !== nothing
            r = get(_canonical_index, t_id, nothing)
            r !== nothing && return r
        else
            for r in representatives
                if canonical_fn(r)::Int == t_id
                    return r
                end
            end
        end
        lenient && return t
        error("No normal form found for $t - please report this bug")
    end
    for r in representatives
        if dp_fn(Equation(t, r))
            return r
        end
    end
    lenient && return t
    error("No normal form found for $t - please report this bug")
end

"""Build a canonical index for a set of representatives: canonical_id → representative."""
function _build_canonical_index(representatives::Set{CQLTerm}, canonical_fn)
    idx = Dict{Int, CQLTerm}()
    for r in representatives
        cid = canonical_fn(r)::Int
        haskey(idx, cid) || (idx[cid] = r)
    end
    idx
end

"""Evaluate a schema type-side term with variable substituted by x.
Also handles entity-side terms (CQLFk/CQLVar) that may appear in observation equations."""
function _eval_schema_type_term(x::CQLTerm, t::CQLTerm, fk_dict, nf_y_fn)::CQLTerm
    if t isa CQLAtt
        x_inner = _eval_schema_entity_term(x, t.arg, fk_dict)
        nf_y_fn(Right((x_inner, t.att)))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_eval_schema_type_term(x, a, fk_dict, nf_y_fn) for a in t.args])
    elseif t isa CQLFk || t isa CQLVar
        _eval_schema_entity_term(x, t, fk_dict)
    else
        error("Bad schema type term: $t")
    end
end

function _eval_schema_entity_term(x::CQLTerm, t::CQLTerm, fk_dict)::CQLTerm
    if t isa CQLVar
        x
    elseif t isa CQLFk
        inner = _eval_schema_entity_term(x, t.arg, fk_dict)
        get(get(fk_dict, t.fk, Dict()), inner, CQLFk(t.fk, inner))
    else
        error("Bad schema entity term: $t")
    end
end

"""Evaluate a presentation type-side term through the algebra state (gen_dict, fk_dict, nf_y)."""
function _eval_pres_type_term(t::CQLTerm, gen_dict, fk_dict, nf_y_fn)::CQLTerm
    if t isa CQLAtt
        x = _eval_pres_entity_term(t.arg, gen_dict, fk_dict)
        nf_y_fn(Right((x, t.att)))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_eval_pres_type_term(a, gen_dict, fk_dict, nf_y_fn) for a in t.args])
    elseif t isa CQLSk
        nf_y_fn(Left(t.sk))
    else
        t  # Constants etc. pass through
    end
end

"""Evaluate a presentation entity-side term to a carrier element."""
function _eval_pres_entity_term(t::CQLTerm, gen_dict, fk_dict)::CQLTerm
    if t isa CQLGen
        get(gen_dict, t.gen, t)
    elseif t isa CQLFk
        inner = _eval_pres_entity_term(t.arg, gen_dict, fk_dict)
        get(get(fk_dict, t.fk, Dict{CQLTerm,CQLTerm}()), inner, CQLFk(t.fk, inner))
    else
        t
    end
end

# ============================================================================
# Saturated instance (from algebra interpretation)
# ============================================================================

"""Build an instance from a saturated presentation (one equation per fact)."""
function saturated_instance(sch::CQLSchema, pres::Presentation)
    # Build typeside rewrite rules for non-free typesides
    ts_rules = _build_typeside_rules(sch.typeside)

    fk_map = Dict{Tuple{Symbol,Symbol}, Symbol}()  # (gen, fk) -> gen'
    att_map = Dict{Tuple{Symbol,Symbol}, CQLTerm}()  # (gen, att) -> term

    for eq in pres.eqs
        if eq.lhs isa CQLFk && eq.lhs.arg isa CQLGen && eq.rhs isa CQLGen
            key = (eq.lhs.arg.gen, eq.lhs.fk)
            haskey(fk_map, key) && throw(CQLException("Duplicate binding: $(eq.lhs.arg.gen)"))
            fk_map[key] = eq.rhs.gen
        elseif eq.lhs isa CQLAtt && eq.lhs.arg isa CQLGen
            key = (eq.lhs.arg.gen, eq.lhs.att)
            haskey(att_map, key) && throw(CQLException("Duplicate binding: $(eq.lhs.arg.gen)"))
            att_map[key] = eq.rhs
        else
            throw(CQLException("Bad equation in saturated instance: $(eq)"))
        end
    end

    # Build carrier sets
    ens_map = Dict{Symbol, Set{Symbol}}()
    for en in sch.ens
        ens_map[en] = Set{Symbol}(g for (g, e) in pres.gens if e == en)
    end

    # Build FK dict
    fk_dict = Dict{Symbol, Dict{Symbol, Symbol}}()
    for (fk, (src, _)) in sch.fks
        fk_dict[fk] = Dict{Symbol, Symbol}()
        for g in ens_map[src]
            haskey(fk_map, (g, fk)) || throw(CQLException("Missing equation for $g.$fk"))
            fk_dict[fk][g] = fk_map[(g, fk)]
        end
    end

    gen_dict = Dict{Symbol, Symbol}(g => g for g in keys(pres.gens))
    repr_dict = Dict{Symbol, CQLTerm}(g => CQLGen(g) for g in keys(pres.gens))

    ty_map = Dict{Symbol, Set{Symbol}}()
    for ty in sch.typeside.tys
        ty_map[ty] = Set{Symbol}(s for (s, t) in pres.sks if t == ty)
        # Add typeside constants (0-arg symbols)
        for (sym_name, (arg_tys, ret_ty)) in sch.typeside.syms
            if isempty(arg_tys) && ret_ty == ty
                push!(ty_map[ty], sym_name)
            end
        end
    end

    nf_y_fn = function(e)
        t = if is_left(e)
            CQLSk(get_left(e))
        else
            (x, att) = get_right(e)
            get(att_map, (x, att), CQLSk(Symbol(string(x, ".", att))))
        end
        _reduce_typeside(ts_rules, t)
    end

    repr_y_dict = Dict{Symbol, CQLTerm}()
    for (s, _) in pres.sks
        repr_y_dict[s] = CQLSk(s)
    end
    # Add repr_y for typeside constants
    for (sym_name, (arg_tys, _)) in sch.typeside.syms
        if isempty(arg_tys)
            repr_y_dict[sym_name] = CQLSym(sym_name, CQLTerm[])
        end
    end

    alg = Algebra{Symbol, Symbol}(
        sch, ens_map, gen_dict, fk_dict, repr_dict,
        ty_map, nf_y_fn, repr_y_dict, Set{Equation}(),
    )

    dp = if isempty(ts_rules)
        eq -> eq.lhs == eq.rhs
    else
        eq -> _reduce_typeside(ts_rules, eq.lhs) == _reduce_typeside(ts_rules, eq.rhs)
    end
    CQLInstance{Symbol, Symbol}(sch, pres, dp, alg)
end

# ============================================================================
# Distinct instance (bisimulation quotient)
# ============================================================================

"""
Compute the distinct quotient of an instance: merge elements that are
observationally indistinguishable (same attribute values along all FK paths).

Algorithm (from Java CQL's DistinctInstance):
1. Build boolean distinguished[en][i][j] matrix per entity (initially all false)
2. Iteratively extend FK paths and mark pairs as distinguished if they diverge
3. Merge undistinguished pairs via union-find
"""
function distinct_instance(inst::CQLInstance{X,Y}) where {X,Y}
    sch = inst.schema
    alg = inst.algebra

    # Build indexed element lists per entity
    en_elems = Dict{Symbol, Vector{X}}()
    for en in sch.ens
        en_elems[en] = collect(alg.en[en])
    end

    # Build index lookups: element -> int
    en_idx = Dict{Symbol, Dict{X, Int}}()
    for en in sch.ens
        d = Dict{X, Int}()
        for (i, x) in enumerate(en_elems[en])
            d[x] = i
        end
        en_idx[en] = d
    end

    # Distinguished matrix per entity
    distinguished = Dict{Symbol, Matrix{Bool}}()
    for en in sch.ens
        n = length(en_elems[en])
        distinguished[en] = falses(n, n)
    end

    # Union-find per entity (parent array)
    uf_parent = Dict{Symbol, Vector{Int}}()
    for en in sch.ens
        n = length(en_elems[en])
        uf_parent[en] = collect(1:n)
    end

    function uf_find(en, i)
        p = uf_parent[en]
        while p[i] != i
            p[i] = p[p[i]]  # path compression
            i = p[i]
        end
        i
    end

    function uf_union(en, i, j)
        ri = uf_find(en, i)
        rj = uf_find(en, j)
        if ri != rj
            uf_parent[en][rj] = ri
        end
    end

    # FK paths: for each entity, a list of (source_entity, path::Vector{Symbol})
    # where path is a sequence of FK names to follow FROM source_entity
    paths = Dict{Symbol, Vector{Vector{Symbol}}}()
    for en in sch.ens
        paths[en] = [Symbol[]]  # start with empty path
    end

    # Check if pair (x_idx, y_idx) starting at entity `start_en`, following `path`,
    # can be distinguished. Returns true if NOT distinguished (i.e., they look the same).
    function notd!(start_en, xi, yi, path, changed)
        xi == yi && return true
        d0 = distinguished[start_en]
        if d0[xi, yi] || d0[yi, xi]
            return false
        end

        cur_en = start_en
        cur_x = en_elems[start_en][xi]
        cur_y = en_elems[start_en][yi]
        x0, y0 = xi, yi

        for fk in path
            tgt_en = sch.fks[fk][2]
            cur_x = eval_fk(alg, fk, cur_x)
            cur_y = eval_fk(alg, fk, cur_y)
            cur_en = tgt_en

            xi2 = en_idx[cur_en][cur_x]
            yi2 = en_idx[cur_en][cur_y]

            if xi2 == yi2
                return true
            end

            dm = distinguished[cur_en]
            if dm[xi2, yi2] || dm[yi2, xi2]
                d0[x0, y0] = true
                d0[y0, x0] = true
                changed[] = true
                return false
            end
        end

        # Check attributes from the current entity
        for (att, _) in schema_atts_from(sch, cur_en)
            a = eval_att(alg, att, cur_x)
            b = eval_att(alg, att, cur_y)
            if !inst.dp(Equation(a, b))
                d0[x0, y0] = true
                d0[y0, x0] = true
                changed[] = true
                return false
            end
        end

        return true
    end

    # Iterative fixpoint
    for _ in 1:1000
        changed = Ref(false)

        for en in sch.ens
            for path in paths[en]
                # The path starts at `en` — follow FKs to determine source entity
                source_en = en
                n = length(en_elems[source_en])
                for xi in 1:n
                    for yi in (xi+1):n
                        notd!(source_en, xi, yi, path, changed)
                    end
                end
            end
        end

        if !changed[]
            break
        end

        # Extend paths by one FK
        new_paths = Dict{Symbol, Vector{Vector{Symbol}}}()
        for en in sch.ens
            new_paths[en] = Vector{Symbol}[]
        end
        for en in sch.ens
            for path in paths[en]
                for (fk, tgt) in schema_fks_from(sch, en)
                    push!(new_paths[en], vcat(path, [fk]))
                end
            end
        end
        paths = new_paths
    end

    # Build union-find from undistinguished pairs
    for en in sch.ens
        d = distinguished[en]
        n = length(en_elems[en])
        for xi in 1:n
            for yi in (xi+1):n
                if !d[xi, yi]
                    uf_union(en, xi, yi)
                end
            end
        end
    end

    # Build quotient algebra
    new_en = Dict{Symbol, Set{X}}()
    for en in sch.ens
        representatives = Set{X}()
        for (i, x) in enumerate(en_elems[en])
            if uf_find(en, i) == i
                push!(representatives, x)
            end
        end
        new_en[en] = representatives
    end

    # Find representative for an element
    function find_repr(en, x)
        idx = en_idx[en][x]
        root = uf_find(en, idx)
        en_elems[en][root]
    end

    # Build FK dict mapping through representatives
    new_fk = Dict{Symbol, Dict{X, X}}()
    for (fk, (src, tgt)) in sch.fks
        fk_map = Dict{X, X}()
        for x in new_en[src]
            fk_x = eval_fk(alg, fk, x)
            fk_map[x] = find_repr(tgt, fk_x)
        end
        new_fk[fk] = fk_map
    end

    # Build gen dict mapping through representatives
    new_gen = Dict{Symbol, X}()
    for (g, x) in alg.gen
        en_g = inst.pres.gens[g]
        new_gen[g] = find_repr(en_g, x)
    end

    # Build repr_x for new elements
    new_repr_x = Dict{X, CQLTerm}()
    for (en, xs) in new_en
        for x in xs
            new_repr_x[x] = alg.repr_x[x]
        end
    end

    new_alg = Algebra{X,Y}(
        sch, new_en, new_gen, new_fk, new_repr_x,
        alg.ty, alg.nf_y, alg.repr_y, alg.teqs,
    )

    # Build new presentation reflecting the quotient
    new_pres_gens = Dict{Symbol, Symbol}()
    for (g, en) in inst.pres.gens
        # Keep only generators whose carrier element is a representative
        x = alg.gen[g]
        en_g = en
        if find_repr(en_g, x) == x
            new_pres_gens[g] = en
        end
    end

    new_pres_eqs = Set{Equation}()
    for eq in inst.pres.eqs
        push!(new_pres_eqs, eq)
    end
    # Add merge equations
    for en in sch.ens
        for (i, x) in enumerate(en_elems[en])
            root = uf_find(en, i)
            if root != i
                push!(new_pres_eqs, Equation(alg.repr_x[x], alg.repr_x[en_elems[en][root]]))
            end
        end
    end

    new_pres = Presentation(
        inst.pres.gens,  # keep all original generators
        inst.pres.sks,
        new_pres_eqs,
        copy(inst.pres.gen_order),
    )

    ts_rules = _build_typeside_rules(sch.typeside)
    dp = if isempty(ts_rules)
        eq -> begin
            # Entity-level: use find_repr if both sides are entity terms
            eq.lhs == eq.rhs
        end
    else
        eq -> _reduce_typeside(ts_rules, eq.lhs) == _reduce_typeside(ts_rules, eq.rhs)
    end

    CQLInstance{X,Y}(sch, new_pres, dp, new_alg)
end

# ============================================================================
# Algebra to presentation
# ============================================================================

"""Convert an algebra back to a saturated presentation."""
function algebra_to_presentation(alg::Algebra{X,Y}) where {X,Y}
    gens = Dict{X, Symbol}()
    for (en, xs) in alg.en
        for x in xs
            gens[x] = en
        end
    end

    sks = Dict{Y, Symbol}()
    for (ty, ys) in alg.ty
        for y in ys
            sks[y] = ty
        end
    end

    eqs = Set{Equation}()
    for (en, xs) in alg.en
        for x in xs
            for (fk, _) in schema_fks_from(alg.schema, en)
                fk_x = eval_fk(alg, fk, x)
                push!(eqs, Equation(CQLFk(fk, CQLGen(x)), CQLGen(fk_x)))
            end
            for (att, _) in schema_atts_from(alg.schema, en)
                att_x = eval_att(alg, att, x)
                push!(eqs, Equation(CQLAtt(att, CQLGen(x)), att_x))
            end
        end
    end

    Presentation(gens, sks, eqs)
end

# ============================================================================
# Raw instance evaluation
# ============================================================================

"""Raw instance data from parsing."""
struct InstExpRaw
    schema_ref::Any  # SchemaExp
    gens::Vector{Tuple{String, String}}  # (name, entity_or_type)
    eqs::Vector{Tuple{RawTerm, RawTerm}}
    options::Vector{Tuple{String, String}}
    imports::Vector{Any}  # InstanceExp references
end

"""Evaluate a raw instance expression."""
function eval_instance_raw(opts::CQLOptions, sch::CQLSchema, raw::InstExpRaw,
                           imports::Vector=CQLInstance[])
    # Split gens into entity generators and type skolems
    gen_pairs = Tuple{Symbol,Symbol}[]
    sk_pairs = Tuple{Symbol,Symbol}[]
    for (name, sort) in raw.gens
        sym_name = Symbol(name)
        sym_sort = Symbol(sort)
        if sym_sort in sch.ens
            push!(gen_pairs, (sym_name, sym_sort))
        elseif sym_sort in sch.typeside.tys
            push!(sk_pairs, (sym_name, sym_sort))
        else
            throw(CQLException("Not an entity or type: $sort"))
        end
    end

    gens = Dict{Symbol,Symbol}(gen_pairs)
    sks = Dict{Symbol,Symbol}(sk_pairs)

    # Merge imported instances' presentations
    for imp in imports
        merge!(gens, imp.pres.gens)
        merge!(sks, imp.pres.sks)
    end

    # Auto-create Skolem constants for unknown leaf terms in equations
    _auto_skolemize!(sch, gens, sks, raw.eqs)

    gen_names = keys(gens)
    sk_names = keys(sks)

    # Translate equations (pass gens dict for entity resolution of qualified FK names)
    eqs = Set{Equation}()
    for (lhs_raw, rhs_raw) in raw.eqs
        lhs = _trans_inst_term(sch, gen_names, sk_names, lhs_raw; gens_dict=gens)
        rhs = _trans_inst_term(sch, gen_names, sk_names, rhs_raw; gens_dict=gens)
        push!(eqs, Equation(lhs, rhs))
    end

    # Add imported instance equations
    for imp in imports
        union!(eqs, imp.pres.eqs)
    end

    # Preserve generator declaration order (imports come after)
    gen_order = Symbol[p[1] for p in gen_pairs]
    for imp in imports
        for g in imp.pres.gen_order
            g in gen_order || push!(gen_order, g)
        end
    end

    pres = Presentation(gens, sks, eqs, gen_order)

    typecheck_presentation(sch, pres)

    local_opts = isempty(raw.options) ? opts : to_options(opts, raw.options)

    if get_bool(local_opts, INTERPRET_AS_ALGEBRA)
        return saturated_instance(sch, pres)
    end

    col = presentation_to_collage(sch, pres)
    prover = create_prover(col, local_opts)

    dp_fn = eq -> prover(Ctx(), eq)

    timeout_seconds = get_int(local_opts, TIMEOUT)
    initial_instance(pres, dp_fn, sch; timeout_seconds=timeout_seconds)
end

function _trans_inst_term(sch, gen_names, sk_names, raw::RawTerm;
                         gens_dict::Union{Dict{Symbol,Symbol},Nothing}=nothing)::CQLTerm
    s = Symbol(raw.head)

    # Handle @Type annotations: @TypeName(inner_term)
    # The @Type annotation explicitly marks the term as type-side (Skolem),
    # even if the name also matches a generator.
    if startswith(raw.head, "@") && length(raw.args) == 1
        inner = raw.args[1]
        inner_s = Symbol(inner.head)
        if isempty(inner.args) && inner_s in sk_names
            return CQLSk(inner_s)
        end
        # For complex inner terms (e.g., function application), translate normally
        return _trans_inst_term(sch, gen_names, sk_names, inner; gens_dict=gens_dict)
    end

    if isempty(raw.args) && s in gen_names
        return CQLGen(s)
    elseif isempty(raw.args) && s in sk_names
        return CQLSk(s)
    elseif length(raw.args) == 1 && haskey(sch.fks, s)
        return CQLFk(s, _trans_inst_path(sch, gen_names, raw.args[1]; gens_dict=gens_dict))
    elseif length(raw.args) == 1 && haskey(sch.atts, s)
        return CQLAtt(s, _trans_inst_path(sch, gen_names, raw.args[1]; gens_dict=gens_dict))
    elseif length(raw.args) == 1 && has_fk(sch, s)
        # Qualified FK name — resolve using entity context
        inner = _trans_inst_path(sch, gen_names, raw.args[1]; gens_dict=gens_dict)
        en = _entity_of_inst_term(sch, gens_dict, inner)
        if en !== nothing
            qname = resolve_fk(sch, s, en)
            return CQLFk(qname, inner)
        end
        # Fallback: try first candidate
        candidates = fk_candidates(sch, s)
        !isempty(candidates) && return CQLFk(candidates[1], inner)
        throw(CQLException("Cannot resolve FK: $(raw.head)"))
    elseif length(raw.args) == 1 && has_att(sch, s)
        inner = _trans_inst_path(sch, gen_names, raw.args[1]; gens_dict=gens_dict)
        en = _entity_of_inst_term(sch, gens_dict, inner)
        if en !== nothing
            qname = resolve_att(sch, s, en)
            return CQLAtt(qname, inner)
        end
        candidates = att_candidates(sch, s)
        !isempty(candidates) && return CQLAtt(candidates[1], inner)
        throw(CQLException("Cannot resolve attribute: $(raw.head)"))
    elseif haskey(sch.typeside.syms, s)
        return CQLSym(s, CQLTerm[_trans_inst_term(sch, gen_names, sk_names, a; gens_dict=gens_dict) for a in raw.args])
    else
        throw(CQLException("Cannot type: $(raw.head)"))
    end
end

function _trans_inst_path(sch, gen_names, raw::RawTerm;
                          gens_dict::Union{Dict{Symbol,Symbol},Nothing}=nothing)::CQLTerm
    s = Symbol(raw.head)
    if isempty(raw.args) && s in gen_names
        return CQLGen(s)
    elseif length(raw.args) == 1 && haskey(sch.fks, s)
        return CQLFk(s, _trans_inst_path(sch, gen_names, raw.args[1]; gens_dict=gens_dict))
    elseif length(raw.args) == 1 && has_fk(sch, s)
        inner = _trans_inst_path(sch, gen_names, raw.args[1]; gens_dict=gens_dict)
        en = _entity_of_inst_term(sch, gens_dict, inner)
        if en !== nothing
            qname = resolve_fk(sch, s, en)
            return CQLFk(qname, inner)
        end
        candidates = fk_candidates(sch, s)
        !isempty(candidates) && return CQLFk(candidates[1], inner)
        throw(CQLException("Cannot type path: $(raw.head)"))
    else
        throw(CQLException("Cannot type path: $(raw.head)"))
    end
end

"""Determine the entity type of an instance term (generator → entity, FK → target entity)."""
function _entity_of_inst_term(sch, gens_dict, t::CQLTerm)::Union{Symbol, Nothing}
    if t isa CQLGen
        if gens_dict !== nothing
            return get(gens_dict, t.gen, nothing)
        end
        return nothing
    elseif t isa CQLFk
        haskey(sch.fks, t.fk) && return sch.fks[t.fk][2]
        return nothing
    else
        return nothing
    end
end

# ============================================================================
# Auto-Skolem: create typed constants for unknown leaf terms in equations
# ============================================================================

"""Pre-scan equations and auto-create Skolem constants for unknown leaf terms.
Uses type inference from equation context (attribute return types, etc.)."""
function _auto_skolemize!(sch, gens::Dict{Symbol,Symbol}, sks::Dict{Symbol,Symbol},
                          raw_eqs::Vector{Tuple{RawTerm,RawTerm}})
    # Multiple passes until convergence (handles cascading type inference)
    for _ in 1:3
        changed = false
        for (lhs_raw, rhs_raw) in raw_eqs
            lhs_type = _infer_raw_type(sch, gens, sks, lhs_raw)
            rhs_type = _infer_raw_type(sch, gens, sks, rhs_raw)

            if lhs_type !== nothing
                changed |= _collect_unknown_sks!(rhs_raw, gens, sks, sch, lhs_type)
            end
            if rhs_type !== nothing
                changed |= _collect_unknown_sks!(lhs_raw, gens, sks, sch, rhs_type)
            end
        end
        !changed && break
    end

    # If there's only one type in the typeside and we still have unknowns, use that type
    if length(sch.typeside.tys) == 1
        only_type = first(sch.typeside.tys)
        for (lhs_raw, rhs_raw) in raw_eqs
            _collect_unknown_sks!(lhs_raw, gens, sks, sch, only_type)
            _collect_unknown_sks!(rhs_raw, gens, sks, sch, only_type)
        end
    end
end

"""Infer the return type of a raw term (type-level for attributes/syms, nothing for entities)."""
function _infer_raw_type(sch, gens, sks, raw::RawTerm)::Union{Symbol, Nothing}
    s = Symbol(raw.head)

    # @Type annotation: the type is explicit
    if startswith(raw.head, "@") && length(raw.args) >= 1
        return Symbol(raw.head[2:end])
    end

    if isempty(raw.args)
        haskey(gens, s) && return nothing  # entity → not a type
        haskey(sks, s) && return sks[s]
        # Zero-arg typeside function (constant)
        if haskey(sch.typeside.syms, s) && isempty(sch.typeside.syms[s][1])
            return sch.typeside.syms[s][2]
        end
        return nothing
    elseif length(raw.args) == 1
        # Attribute → returns a type
        if haskey(sch.atts, s)
            return sch.atts[s][2]
        elseif has_att(sch, s)
            candidates = att_candidates(sch, s)
            !isempty(candidates) && return sch.atts[candidates[1]][2]
        end
        # FK → returns an entity (not useful for type inference)
    end
    # Multi-arg: typeside function
    if haskey(sch.typeside.syms, s)
        return sch.typeside.syms[s][2]
    end
    nothing
end

"""Collect unknown leaf terms and add them as Skolems with the expected type."""
function _collect_unknown_sks!(raw::RawTerm, gens, sks, sch, expected_type::Symbol)::Bool
    s = Symbol(raw.head)

    # @Type annotation: add inner term as Skolem of the annotated type,
    # even if the name matches a generator (the annotation explicitly says type-side)
    if startswith(raw.head, "@") && length(raw.args) >= 1
        type_name = Symbol(raw.head[2:end])
        inner = raw.args[1]
        inner_s = Symbol(inner.head)
        if isempty(inner.args) && !haskey(sks, inner_s)
            sks[inner_s] = type_name
            return true
        end
        return _collect_unknown_sks!(inner, gens, sks, sch, type_name)
    end

    if isempty(raw.args)
        # Leaf term — check if it's unknown
        # Note: only check gens, sks, and typeside syms for zero-arg terms.
        # FK/att names are NOT checked here because FKs and atts always take
        # exactly one argument — a zero-arg term with the same name is a
        # constant, not an attribute/FK application (e.g., "f" literal vs f:E->F).
        if !haskey(gens, s) && !haskey(sks, s) &&
           !haskey(sch.typeside.syms, s)
            # Unknown leaf → add as Skolem constant
            sks[s] = expected_type
            return true
        end
    else
        # Recurse into arguments
        changed = false
        if haskey(sch.typeside.syms, s)
            arg_types = sch.typeside.syms[s][1]
            for (i, a) in enumerate(raw.args)
                if i <= length(arg_types)
                    changed |= _collect_unknown_sks!(a, gens, sks, sch, arg_types[i])
                end
            end
        end
        return changed
    end
    false
end

# ============================================================================
# Expression types
# ============================================================================

abstract type InstanceExp end

struct InstanceVar <: InstanceExp
    name::String
end

struct InstanceInitial <: InstanceExp
    schema::SchemaExp
end

struct InstanceRawExp <: InstanceExp
    raw::InstExpRaw
end

struct InstanceDelta <: InstanceExp
    mapping::Any  # MappingExp
    instance::InstanceExp
    options::Vector{Tuple{String,String}}
end

struct InstanceSigma <: InstanceExp
    mapping::Any  # MappingExp
    instance::InstanceExp
    options::Vector{Tuple{String,String}}
end

struct InstanceEval <: InstanceExp
    query::Any  # QueryExp
    instance::InstanceExp
end

struct InstanceCoproduct <: InstanceExp
    instances::Vector{InstanceExp}
    schema::SchemaExp
end

struct InstancePivot <: InstanceExp
    instance::InstanceExp
end

"""Random instance: random : schema { generators entity -> count ... }"""
struct InstanceRandom <: InstanceExp
    schema::SchemaExp
    gen_counts::Vector{Tuple{String,Int}}
    options::Vector{Tuple{String,String}}
end

"""Coeval instance: coeval Q I"""
struct InstanceCoeval <: InstanceExp
    query::Any
    instance::InstanceExp
end

"""Import from CSV: import_csv "path" : schema"""
struct InstanceImportCsv <: InstanceExp
    path::String
    schema::SchemaExp
end

"""Import from JDBC: import_jdbc "conn" : schema { entity -> "SQL" ... }"""
struct InstanceImportJdbc <: InstanceExp
    conn::String
    schema::SchemaExp
    entity_sql::Vector{Tuple{String,String}}  # entity -> SQL query mappings
    options::Vector{Tuple{String,String}}
end

"""Distinct instance: distinct I"""
struct InstanceDistinct <: InstanceExp
    instance::InstanceExp
end

"""Coequalize transforms: coequalize t1 t2"""
struct InstanceCoequalize <: InstanceExp
    t1::Any  # TransformExp (defined later in include order)
    t2::Any  # TransformExp
end

"""Quotient query: quotient_query instance { entity blocks... }"""
struct InstanceQuotientQuery <: InstanceExp
    instance::InstanceExp
    raw_query::Any  # parsed query body or nothing
end

"""Domain of transform: dom_t T"""
struct InstanceDomT <: InstanceExp
    transform::Any  # TransformExp (defined later in include order)
end

"""Codomain of transform: cod_t T"""
struct InstanceCodT <: InstanceExp
    transform::Any  # TransformExp (defined later in include order)
end

"""Colimit instance: colimit graph_name schema { nodes ... edges ... }"""
struct InstanceColimit <: InstanceExp
    graph_name::String
    schema::SchemaExp
    node_map::Vector{Tuple{String,Any}}   # node -> instance_exp (may include dom_t/cod_t)
    edge_map::Vector{Tuple{String,Any}}   # edge -> transform_exp
    options::Vector{Tuple{String,String}}
end

"""Import JDBC direct: import_jdbc_direct conn rowid : schema"""
struct InstanceImportJdbcDirect <: InstanceExp
    conn::String
    rowid::String
    schema::SchemaExp
end

"""Import from ODBC: import_odbc "conn" : schema { entity -> "SQL" ... }"""
struct InstanceImportOdbc <: InstanceExp
    conn::String
    schema::SchemaExp
    entity_sql::Vector{Tuple{String,String}}
    options::Vector{Tuple{String,String}}
end

"""Import ODBC direct: import_odbc_direct conn rowid : schema"""
struct InstanceImportOdbcDirect <: InstanceExp
    conn::String
    rowid::String
    schema::SchemaExp
end

"""Import JSON-LD: import_json_ld_all path"""
struct InstanceImportJsonLd <: InstanceExp
    path::String
end

"""Import RDF: import_rdf_all path"""
struct InstanceImportRdf <: InstanceExp
    path::String
end

"""Import XML: import_xml_all path"""
struct InstanceImportXml <: InstanceExp
    path::String
end

"""Spanify instance: spanify I"""
struct InstanceSpanify <: InstanceExp
    instance::InstanceExp
end

"""Frozen instance: frozen query entity"""
struct InstanceFrozen <: InstanceExp
    query::Any  # QueryExp
    entity::String
end

"""Except instance: except I1 I2"""
struct InstanceExcept <: InstanceExp
    inst1::InstanceExp
    inst2::InstanceExp
end

"""Anonymize instance: anonymize I"""
struct InstanceAnonymize <: InstanceExp
    instance::InstanceExp
end

"""Pi instance: pi mapping instance [{ options }]"""
struct InstancePi <: InstanceExp
    mapping::Any  # MappingExp
    instance::InstanceExp
    options::Vector{Tuple{String,String}}
end

"""Cascade delete: cascade_delete instance : schema"""
struct InstanceCascadeDelete <: InstanceExp
    instance::InstanceExp
    schema::SchemaExp
end

function deps(e::InstanceExp)::Vector{Tuple{String,Kind}}
    if e isa InstanceVar
        [(e.name, INSTANCE)]
    elseif e isa InstanceInitial
        deps(e.schema)
    elseif e isa InstanceRawExp
        schema_deps = e.raw.schema_ref isa SchemaExp ? deps(e.raw.schema_ref) : Tuple{String,Kind}[]
        vcat(schema_deps, vcat([deps(i) for i in e.raw.imports]...))
    elseif e isa InstanceDelta
        vcat(deps(e.mapping), deps(e.instance))
    elseif e isa InstanceSigma
        vcat(deps(e.mapping), deps(e.instance))
    elseif e isa InstanceEval
        vcat(deps(e.query), deps(e.instance))
    elseif e isa InstanceCoproduct
        result = deps(e.schema)
        for inst in e.instances
            append!(result, deps(inst))
        end
        result
    elseif e isa InstanceChase
        vcat([(e.constraints_name, CONSTRAINTS)], deps(e.instance))
    elseif e isa InstancePivot
        deps(e.instance)
    elseif e isa InstanceRandom
        deps(e.schema)
    elseif e isa InstanceCoeval
        vcat(deps(e.query), deps(e.instance))
    elseif e isa InstanceImportCsv
        deps(e.schema)
    elseif e isa InstanceImportJdbc
        deps(e.schema)
    elseif e isa InstanceDistinct
        deps(e.instance)
    elseif e isa InstanceCoequalize
        vcat(deps(e.t1), deps(e.t2))
    elseif e isa InstanceQuotientQuery
        deps(e.instance)
    elseif e isa InstanceDomT
        deps(e.transform)
    elseif e isa InstanceCodT
        deps(e.transform)
    elseif e isa InstanceColimit
        result = deps(e.schema)
        push!(result, (e.graph_name, GRAPH))
        for (_, inst_exp) in e.node_map
            if inst_exp isa InstanceExp
                append!(result, deps(inst_exp))
            end
        end
        for (_, tr_exp) in e.edge_map
            if tr_exp isa TransformExp
                append!(result, deps(tr_exp))
            end
        end
        result
    elseif e isa InstanceImportJdbcDirect
        deps(e.schema)
    elseif e isa InstanceImportOdbc
        deps(e.schema)
    elseif e isa InstanceImportOdbcDirect
        deps(e.schema)
    elseif e isa InstanceImportJsonLd
        Tuple{String,Kind}[]
    elseif e isa InstanceImportRdf
        Tuple{String,Kind}[]
    elseif e isa InstanceImportXml
        Tuple{String,Kind}[]
    elseif e isa InstanceSpanify
        deps(e.instance)
    elseif e isa InstanceFrozen
        deps(e.query)
    elseif e isa InstanceExcept
        vcat(deps(e.inst1), deps(e.inst2))
    elseif e isa InstanceAnonymize
        deps(e.instance)
    elseif e isa InstancePi
        vcat(deps(e.mapping), deps(e.instance))
    elseif e isa InstanceCascadeDelete
        vcat(deps(e.instance), deps(e.schema))
    else
        Tuple{String,Kind}[]
    end
end
