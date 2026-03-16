# ─── Unicode operators and functional API for CQL ─────────────────────────────

# ─── Delta (Δ) — Pullback ────────────────────────────────────────────────────

"""
    Δ(F::CQLMapping) -> (inst -> CQLInstance)

Delta (pullback) data migration. Returns a curried function.

    Δ(F)(J)   # pull back instance J along mapping F
"""
function Δ(F::CQLMapping)
    inst -> eval_delta_instance(F, inst, default_options())
end

"""
    Δ(F::CQLMapping, J::CQLInstance; opts=default_options())

Delta (pullback) data migration: pull back instance J along mapping F.
"""
Δ(F::CQLMapping, J::CQLInstance; opts::CQLOptions=default_options()) =
    eval_delta_instance(F, J, opts)

# ─── Sigma (Σ) — Pushforward ─────────────────────────────────────────────────

"""
    Σ(F::CQLMapping) -> (inst -> CQLInstance)

Sigma (pushforward) data migration. Returns a curried function.

    Σ(F)(I)   # push forward instance I along mapping F
"""
function Σ(F::CQLMapping)
    inst -> eval_sigma_instance(F, inst, default_options())
end

"""
    Σ(F::CQLMapping, I::CQLInstance; opts=default_options())

Sigma (pushforward) data migration: push forward instance I along mapping F.
"""
Σ(F::CQLMapping, I::CQLInstance; opts::CQLOptions=default_options()) =
    eval_sigma_instance(F, I, opts)

# ─── Query evaluation — callable queries ─────────────────────────────────────

"""
    Q(I::CQLInstance; opts=default_options())

Evaluate query Q on instance I. Makes queries callable.

    result = Q(I)
"""
(q::CQLQuery)(inst::CQLInstance; opts::CQLOptions=default_options()) =
    eval_query_instance(q, inst, opts)

# ─── Composition (∘) ─────────────────────────────────────────────────────────

"""
    Q1 ∘ Q2

Compose two CQL queries. `(Q1 ∘ Q2)(I)` is equivalent to `Q1(Q2(I))`.
"""
Base.:∘(q1::CQLQuery, q2::CQLQuery) = compose_query(q1, q2)

"""    M1 ∘ M2 — Compose two CQL mappings."""
Base.:∘(m1::CQLMapping, m2::CQLMapping) = compose_mapping(m1, m2)

"""    T1 ∘ T2 — Compose two CQL transforms."""
Base.:∘(t1::CQLTransform, t2::CQLTransform) = compose_transform(t1, t2)

# ─── CoEval ──────────────────────────────────────────────────────────────────

"""
    coeval(Q::CQLQuery, I::CQLInstance; opts=default_options())

Right adjoint to query evaluation. Given Q: S → T and I on T,
produce an instance on S.
"""
coeval(q::CQLQuery, inst::CQLInstance; opts::CQLOptions=default_options()) =
    eval_coeval_instance(q, inst, opts)

# ─── Coproduct (⊔) ──────────────────────────────────────────────────────────

"""
    I1 ⊔ I2

Coproduct (disjoint union) of two instances on the same schema.
"""
⊔(i1::CQLInstance, i2::CQLInstance; opts::CQLOptions=default_options()) =
    eval_coproduct_instance(i1.schema, CQLInstance[i1, i2], opts)

"""
    coproduct(instances::CQLInstance...; opts=default_options())

Coproduct of multiple instances on the same schema.
"""
function coproduct(instances::CQLInstance...; opts::CQLOptions=default_options())
    isempty(instances) && error("coproduct requires at least one instance")
    sch = first(instances).schema
    eval_coproduct_instance(sch, collect(CQLInstance, instances), opts)
end

# ─── Distinct ────────────────────────────────────────────────────────────────

"""
    distinct(I::CQLInstance)

Remove duplicate elements from an instance by merging provably equal generators.
"""
distinct(i::CQLInstance) = distinct_instance(i)

# ─── Coequalize ──────────────────────────────────────────────────────────────

"""
    coequalize(f::CQLTransform, g::CQLTransform; opts=default_options())

Compute the coequalizer of two transforms f, g: I → J.
Returns the quotient instance where f(x) = g(x) for all x.
"""
coequalize(f::CQLTransform, g::CQLTransform; opts::CQLOptions=default_options()) =
    eval_coequalize(f, g, opts)

# ─── Mapping to Query ───────────────────────────────────────────────────────

"""
    to_query(F::CQLMapping)

Convert a mapping to its equivalent uber-flower query.
"""
to_query(m::CQLMapping) = mapping_to_query(m)
