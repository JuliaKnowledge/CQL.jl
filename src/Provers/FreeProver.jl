"""
Free prover: for theories with no equations, syntactic equality suffices.
"""

"""Create a free prover (syntactic equality). Requires no equations in the collage."""
function free_prover(col::Collage)
    !isempty(col.ceqs) && throw(CQLException("Cannot use free prover when there are equations"))
    (ctx::Ctx, eq::Equation) -> eq.lhs == eq.rhs
end
