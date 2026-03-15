# ─── Unicode operators for CQL ────────────────────────────────────────────────

"""
    Δ(F::CQLMapping) -> (inst -> CQLInstance)

Delta (pullback) data migration. Returns a curried function.

    Δ(F)(J)   # pull back instance J along mapping F

Equivalent to `eval_delta_instance(F, J, default_options())`.
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

"""
    Σ(F::CQLMapping) -> (inst -> CQLInstance)

Sigma (pushforward) data migration. Returns a curried function.

    Σ(F)(I)   # push forward instance I along mapping F

Equivalent to `eval_sigma_instance(F, I, default_options())`.
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

"""
    Q::CQLQuery(I::CQLInstance; opts=default_options())

Evaluate query Q on instance I. Makes queries callable.
"""
(q::CQLQuery)(inst::CQLInstance; opts::CQLOptions=default_options()) =
    eval_query_instance(q, inst, opts)

"""
    Q1 ∘ Q2

Compose two CQL queries. Returns a new query equivalent to first applying Q2 then Q1.
"""
Base.:∘(q1::CQLQuery, q2::CQLQuery) = compose_query(q1, q2)

"""
    M1 ∘ M2

Compose two CQL mappings.
"""
Base.:∘(m1::CQLMapping, m2::CQLMapping) = compose_mapping(m1, m2)

"""
    T1 ∘ T2

Compose two CQL transforms.
"""
Base.:∘(t1::CQLTransform, t2::CQLTransform) = compose_transform(t1, t2)
