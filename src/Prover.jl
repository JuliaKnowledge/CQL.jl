"""
Prover dispatch: selects and creates the appropriate decision procedure.
"""

@enum ProverName PROVER_FREE PROVER_CONGRUENCE PROVER_ORTHOGONAL PROVER_COMPLETION PROVER_AUTO PROVER_FAIL

"""Parse prover name from options."""
function prover_name_from_options(opts::CQLOptions)::ProverName
    name = get_str(opts, PROVER)
    if name == "auto"
        PROVER_AUTO
    elseif name == "completion"
        PROVER_COMPLETION
    elseif name == "program"
        PROVER_ORTHOGONAL
    elseif name == "congruence"
        PROVER_CONGRUENCE
    elseif name == "free"
        PROVER_FREE
    elseif name == "monoidal"
        PROVER_AUTO
    elseif name == "e" || name == "fail"
        # External provers (E, Vampire) are not available — use fail prover
        # which tries congruence/orthogonal but never falls through to expensive KB completion
        PROVER_FAIL
    else
        throw(CQLException("Not a prover: $name"))
    end
end

"""
Create a decision procedure from a collage and options.

Returns a function `(ctx::Ctx, eq::Equation) -> Bool` that decides
whether the equation holds in the given context.
"""
function create_prover(col::Collage, opts::CQLOptions)
    p = prover_name_from_options(opts)

    if p == PROVER_FREE
        return free_prover(col)
    elseif p == PROVER_CONGRUENCE
        prover, _ = congruence_prover(col)
        return prover
    elseif p == PROVER_ORTHOGONAL
        return orthogonal_prover(col, opts)
    elseif p == PROVER_COMPLETION
        return kb_completion_prover(col, opts)
    elseif p == PROVER_FAIL
        # Lightweight prover: tries congruence/orthogonal but never KB completion.
        # Used for external prover settings (e, fail) where the external tool is unavailable.
        if isempty(col.ceqs) || eqs_are_ground(col)
            try
                prover, _ = congruence_prover(col)
                return prover
            catch e; e isa CQLException || rethrow(); end
        end
        try; return orthogonal_prover(col, opts)
        catch e; e isa CQLException || rethrow(); end
        try
            prover, _ = congruence_prover(col)
            return prover
        catch e; e isa CQLException || rethrow(); end
        # Last resort: simplify-only prover (checks syntactic equality after simplification)
        (col_simplified, replacements) = simplify_collage(col)
        return (ctx::Ctx, eq::Equation) -> begin
            l = replace_repeatedly(replacements, eq.lhs)
            r = replace_repeatedly(replacements, eq.rhs)
            l == r
        end
    elseif p == PROVER_AUTO
        if isempty(col.ceqs) || eqs_are_ground(col)
            try
                prover, _ = congruence_prover(col)
                return prover
            catch e
                e isa CQLException || rethrow()
            end
        end
        # Try orthogonal prover first; fall back to completion
        try
            return orthogonal_prover(col, opts)
        catch e
            e isa CQLException || rethrow()
            # Orthogonal prover failed (non-size-decreasing equations) — try completion
            try
                return kb_completion_prover(col, opts)
            catch e2
                e2 isa CQLException || rethrow()
                # Both failed — rethrow original error
                throw(e)
            end
        end
    else
        error("Unknown prover: $p")
    end
end

"""Create prover with canonical function (for congruence provers).
Returns (prover, canonical_fn_or_nothing)."""
function create_prover_with_canonical(col::Collage, opts::CQLOptions)
    p = prover_name_from_options(opts)
    if p == PROVER_CONGRUENCE || p == PROVER_AUTO || p == PROVER_FAIL
        if isempty(col.ceqs) || eqs_are_ground(col)
            try
                prover, canonical = congruence_prover(col)
                return prover, canonical
            catch e
                e isa CQLException || rethrow()
            end
        end
    end
    return create_prover(col, opts), nothing
end
