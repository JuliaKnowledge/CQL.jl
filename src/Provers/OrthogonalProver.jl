"""
Orthogonal (weakly orthogonal rewriting) prover.

For size-decreasing, non-overlapping rewrite systems: normalize both sides
and check syntactic equality of normal forms.
"""

"""A rewrite rule: lhs -> rhs."""
struct RewriteRule
    lhs::CQLTerm
    rhs::CQLTerm
end

# ============================================================================
# Small array-based substitution (avoids Dict allocation/clearing overhead)
# ============================================================================

"""Fixed-capacity substitution backed by parallel arrays. O(n) lookup but
n ≤ 8 for typical rewrite rules, much faster than Dict hashing."""
mutable struct SmallSubst
    keys::Vector{Symbol}
    vals::Vector{CQLTerm}
    len::Int
end

SmallSubst(cap::Int=8) = SmallSubst(Vector{Symbol}(undef, cap), Vector{CQLTerm}(undef, cap), 0)

@inline function ss_clear!(s::SmallSubst)
    s.len = 0
end

@inline function ss_get(s::SmallSubst, k::Symbol)::Union{CQLTerm, Nothing}
    @inbounds for i in 1:s.len
        s.keys[i] === k && return s.vals[i]
    end
    nothing
end

@inline function ss_set!(s::SmallSubst, k::Symbol, v::CQLTerm)
    n = s.len + 1
    if n > length(s.keys)
        resize!(s.keys, n * 2)
        resize!(s.vals, n * 2)
    end
    @inbounds s.keys[n] = k
    @inbounds s.vals[n] = v
    s.len = n
end

"""Convert SmallSubst to Dict (needed for apply_subst compatibility)."""
function ss_to_dict(s::SmallSubst)::Dict{Symbol, CQLTerm}
    d = Dict{Symbol, CQLTerm}()
    sizehint!(d, s.len)
    @inbounds for i in 1:s.len
        d[s.keys[i]] = s.vals[i]
    end
    d
end

"""Apply a SmallSubst directly to a term (avoids Dict conversion)."""
function apply_subst(t::CQLTerm, subst::SmallSubst)::CQLTerm
    if t isa CQLVar
        v = ss_get(subst, t.name)
        v !== nothing ? v : t
    elseif t isa CQLSym
        changed = false
        new_args = t.args
        for (i, a) in enumerate(t.args)
            na = apply_subst(a, subst)
            if na !== a
                if !changed
                    new_args = copy(t.args)
                    changed = true
                end
                new_args[i] = na
            end
        end
        changed ? CQLSym(t.sym, new_args) : t
    elseif t isa CQLFk
        na = apply_subst(t.arg, subst)
        na === t.arg ? t : CQLFk(t.fk, na)
    elseif t isa CQLAtt
        na = apply_subst(t.arg, subst)
        na === t.arg ? t : CQLAtt(t.att, na)
    else
        t
    end
end

"""Attempt to match a pattern (with variables) against a ground term.
Returns a substitution Dict{Symbol, CQLTerm} or nothing."""
function match_term(pattern::CQLTerm, target::CQLTerm)::Union{Nothing, Dict{Symbol, CQLTerm}}
    subst = Dict{Symbol, CQLTerm}()
    sizehint!(subst, 4)  # most rules have ≤4 variables
    _match!(pattern, target, subst) ? subst : nothing
end

"""Match using a pre-allocated SmallSubst (cleared before use). Returns true on success."""
@inline function match_term_reuse!(pattern::CQLTerm, target::CQLTerm, subst::SmallSubst)::Bool
    ss_clear!(subst)
    _match_ss!(pattern, target, subst)
end

"""Match into a SmallSubst."""
function _match_ss!(pattern::CQLTerm, target::CQLTerm, subst::SmallSubst)::Bool
    if pattern isa CQLVar
        existing = ss_get(subst, pattern.name)
        if existing !== nothing
            return existing == target
        else
            ss_set!(subst, pattern.name, target)
            return true
        end
    elseif pattern isa CQLGen && target isa CQLGen
        return pattern.gen == target.gen
    elseif pattern isa CQLSk && target isa CQLSk
        return pattern.sk == target.sk
    elseif pattern isa CQLSym && target isa CQLSym
        pattern.sym == target.sym || return false
        length(pattern.args) == length(target.args) || return false
        for i in eachindex(pattern.args)
            _match_ss!(pattern.args[i], target.args[i], subst) || return false
        end
        return true
    elseif pattern isa CQLFk && target isa CQLFk
        pattern.fk == target.fk || return false
        return _match_ss!(pattern.arg, target.arg, subst)
    elseif pattern isa CQLAtt && target isa CQLAtt
        pattern.att == target.att || return false
        return _match_ss!(pattern.arg, target.arg, subst)
    else
        return false
    end
end

"""Match using a pre-allocated Dict (cleared before use). Returns true on success."""
@inline function match_term_reuse!(pattern::CQLTerm, target::CQLTerm, subst::Dict{Symbol, CQLTerm})::Bool
    empty!(subst)
    _match!(pattern, target, subst)
end

function _match!(pattern::CQLTerm, target::CQLTerm, subst::Dict{Symbol, CQLTerm})::Bool
    if pattern isa CQLVar
        if haskey(subst, pattern.name)
            return subst[pattern.name] == target
        else
            subst[pattern.name] = target
            return true
        end
    elseif pattern isa CQLGen && target isa CQLGen
        return pattern.gen == target.gen
    elseif pattern isa CQLSk && target isa CQLSk
        return pattern.sk == target.sk
    elseif pattern isa CQLSym && target isa CQLSym
        pattern.sym == target.sym || return false
        length(pattern.args) == length(target.args) || return false
        for i in eachindex(pattern.args)
            _match!(pattern.args[i], target.args[i], subst) || return false
        end
        return true
    elseif pattern isa CQLFk && target isa CQLFk
        pattern.fk == target.fk || return false
        return _match!(pattern.arg, target.arg, subst)
    elseif pattern isa CQLAtt && target isa CQLAtt
        pattern.att == target.att || return false
        return _match!(pattern.arg, target.arg, subst)
    else
        return false
    end
end

"""Apply a substitution to a term."""
function apply_subst(t::CQLTerm, subst::Dict{Symbol, CQLTerm})::CQLTerm
    if t isa CQLVar
        get(subst, t.name, t)
    elseif t isa CQLSym
        changed = false
        new_args = t.args
        for (i, a) in enumerate(t.args)
            na = apply_subst(a, subst)
            if na !== a
                if !changed
                    new_args = copy(t.args)
                    changed = true
                end
                new_args[i] = na
            end
        end
        changed ? CQLSym(t.sym, new_args) : t
    elseif t isa CQLFk
        na = apply_subst(t.arg, subst)
        na === t.arg ? t : CQLFk(t.fk, na)
    elseif t isa CQLAtt
        na = apply_subst(t.arg, subst)
        na === t.arg ? t : CQLAtt(t.att, na)
    elseif t isa CQLGen || t isa CQLSk
        t
    else
        t
    end
end

"""Try to rewrite a term at the top level using a list of rules.
Returns the rewritten term, or nothing if no rule applies."""
function rewrite_at_root(rules::Vector{RewriteRule}, t::CQLTerm)::Union{Nothing, CQLTerm}
    for rule in rules
        m = match_term(rule.lhs, t)
        if m !== nothing
            return apply_subst(rule.rhs, m)
        end
    end
    nothing
end

"""Try to rewrite a term at any position (outermost first).
Returns the rewritten term, or nothing if no rule applies."""
function rewrite_one_step(rules::Vector{RewriteRule}, t::CQLTerm)::Union{Nothing, CQLTerm}
    # Try root
    result = rewrite_at_root(rules, t)
    result !== nothing && return result

    # Try subterms
    if t isa CQLSym
        for i in eachindex(t.args)
            r = rewrite_one_step(rules, t.args[i])
            if r !== nothing
                new_args = copy(t.args)
                new_args[i] = r
                return CQLSym(t.sym, new_args)
            end
        end
    elseif t isa CQLFk
        r = rewrite_one_step(rules, t.arg)
        r !== nothing && return CQLFk(t.fk, r)
    elseif t isa CQLAtt
        r = rewrite_one_step(rules, t.arg)
        r !== nothing && return CQLAtt(t.att, r)
    end
    nothing
end

"""Normalize a term by repeatedly rewriting to normal form."""
function normalize(rules::Vector{RewriteRule}, t::CQLTerm; max_steps::Int=50000)::CQLTerm
    for _ in 1:max_steps
        result = rewrite_one_step(rules, t)
        result === nothing && return t
        t = result
    end
    throw(CQLException("Rewriting did not terminate after $max_steps steps"))
end

# ============================================================================
# Head-symbol indexed rule lookup (twee-lib style optimization)
# ============================================================================

"""Index of rewrite rules keyed by LHS head symbol for O(1) dispatch."""
struct RuleIndex
    by_head::Dict{Symbol, Vector{RewriteRule}}
    all_rules::Vector{RewriteRule}  # fallback for variable-headed rules
    _match_buf::SmallSubst  # reusable match buffer (array-based, no Dict overhead)
end

function RuleIndex(rules::Vector{RewriteRule})
    by_head = Dict{Symbol, Vector{RewriteRule}}()
    for r in rules
        h = _rule_head_sym(r.lhs)
        if h !== nothing
            bucket = get!(Vector{RewriteRule}, by_head, h)
            push!(bucket, r)
        end
    end
    RuleIndex(by_head, rules, SmallSubst(8))
end

"""Extract the head symbol of a rule LHS for indexing."""
function _rule_head_sym(t::CQLTerm)::Union{Symbol, Nothing}
    if t isa CQLSym; return t.sym
    elseif t isa CQLFk; return t.fk
    elseif t isa CQLAtt; return t.att
    elseif t isa CQLGen; return t.gen
    elseif t isa CQLSk; return t.sk
    else return nothing
    end
end

"""Rewrite at root using indexed rules — only checks rules matching the head symbol."""
function rewrite_at_root(idx::RuleIndex, t::CQLTerm)::Union{Nothing, CQLTerm}
    h = _rule_head_sym(t)
    if h !== nothing && haskey(idx.by_head, h)
        buf = idx._match_buf
        for rule in idx.by_head[h]
            if match_term_reuse!(rule.lhs, t, buf)
                return apply_subst(rule.rhs, buf)
            end
        end
    end
    nothing
end

"""Rewrite one step using indexed rules."""
function rewrite_one_step(idx::RuleIndex, t::CQLTerm)::Union{Nothing, CQLTerm}
    result = rewrite_at_root(idx, t)
    result !== nothing && return result

    if t isa CQLSym
        for i in eachindex(t.args)
            r = rewrite_one_step(idx, t.args[i])
            if r !== nothing
                new_args = copy(t.args)
                new_args[i] = r
                return CQLSym(t.sym, new_args)
            end
        end
    elseif t isa CQLFk
        r = rewrite_one_step(idx, t.arg)
        r !== nothing && return CQLFk(t.fk, r)
    elseif t isa CQLAtt
        r = rewrite_one_step(idx, t.arg)
        r !== nothing && return CQLAtt(t.att, r)
    end
    nothing
end

"""Normalize using indexed rules."""
function normalize(idx::RuleIndex, t::CQLTerm; max_steps::Int=50000)::CQLTerm
    for _ in 1:max_steps
        result = rewrite_one_step(idx, t)
        result === nothing && return t
        t = result
    end
    throw(CQLException("Rewriting did not terminate after $max_steps steps"))
end

"""Inner-most normalize: normalize subterms first, then apply rules at root.
More efficient for KB completion as it avoids redundant outer rewrites."""
function normalize_innermost(idx::RuleIndex, t::CQLTerm; max_steps::Int=50000)::CQLTerm
    step_count = Ref(0)
    _normalize_inner(idx, t, step_count, max_steps)
end

function _normalize_inner(idx::RuleIndex, t::CQLTerm, step_count::Ref{Int}, max_steps::Int)::CQLTerm
    step_count[] > max_steps && throw(CQLException("Rewriting did not terminate after $max_steps steps"))

    # First normalize all subterms
    if t isa CQLSym
        changed = false
        new_args = t.args
        for (i, a) in enumerate(t.args)
            na = _normalize_inner(idx, a, step_count, max_steps)
            if na !== a
                if !changed
                    new_args = copy(t.args)
                    changed = true
                end
                new_args[i] = na
            end
        end
        t = changed ? CQLSym(t.sym, new_args) : t
    elseif t isa CQLFk
        na = _normalize_inner(idx, t.arg, step_count, max_steps)
        t = na === t.arg ? t : CQLFk(t.fk, na)
    elseif t isa CQLAtt
        na = _normalize_inner(idx, t.arg, step_count, max_steps)
        t = na === t.arg ? t : CQLAtt(t.att, na)
    end

    # Then repeatedly apply rules at root until no rule fires
    while true
        step_count[] += 1
        if step_count[] > max_steps
            throw(CQLException("Rewriting did not terminate after $max_steps steps"))
        end
        result = rewrite_at_root(idx, t)
        result === nothing && return t
        # Re-normalize the result (a rule may have introduced non-normalized subterms)
        t = _normalize_inner(idx, result, step_count, max_steps)
    end
end

"""Check if an equation is size-decreasing and variable-safe (all rhs vars occur on lhs)."""
function _is_eq_decreasing(eq::Equation)::Bool
    term_size(eq.lhs) > term_size(eq.rhs) || return false
    lhs_vars = term_vars(eq.lhs)
    rhs_vars = term_vars(eq.rhs)
    for v in rhs_vars
        count(==(v), lhs_vars) >= count(==(v), rhs_vars) || return false
    end
    true
end

"""Check if an equation is safe for rewriting even at equal size.
Safe when LHS root symbols don't appear in the RHS (no overlap → terminates)."""
function _is_eq_safe_equal_size(eq::Equation)::Bool
    term_size(eq.lhs) == term_size(eq.rhs) || return false
    lhs_vars = term_vars(eq.lhs)
    rhs_vars = term_vars(eq.rhs)
    # All rhs vars must appear in lhs
    for v in rhs_vars
        count(==(v), lhs_vars) >= count(==(v), rhs_vars) || return false
    end
    # LHS root function symbol must not appear anywhere in RHS
    lhs_root = _root_symbol(eq.lhs)
    lhs_root === nothing && return false
    !_symbol_occurs(lhs_root, eq.rhs)
end

"""Get the root function/fk/att symbol of a term, or nothing."""
function _root_symbol(t::CQLTerm)::Union{Symbol, Nothing}
    t isa CQLFk && return t.fk
    t isa CQLAtt && return t.att
    t isa CQLSym && return t.sym
    nothing
end

"""Check if a function/fk/att symbol occurs anywhere in a term."""
function _symbol_occurs(sym::Symbol, t::CQLTerm)::Bool
    if t isa CQLFk
        t.fk == sym && return true
        return _symbol_occurs(sym, t.arg)
    elseif t isa CQLAtt
        t.att == sym && return true
        return _symbol_occurs(sym, t.arg)
    elseif t isa CQLSym
        t.sym == sym && return true
        return any(_symbol_occurs(sym, a) for a in t.args)
    else
        return false
    end
end

"""Orient an equation so the larger side is the LHS.
Returns the oriented equation, or nothing if neither orientation works."""
function _orient_eq(eq::Equation)::Union{Equation, Nothing}
    _is_eq_decreasing(eq) && return eq
    swapped = Equation(eq.rhs, eq.lhs)
    _is_eq_decreasing(swapped) && return swapped
    # Try equal-size orientation (non-overlapping root symbols)
    _is_eq_safe_equal_size(eq) && return eq
    _is_eq_safe_equal_size(swapped) && return swapped
    nothing
end

"""Check if equations are size-decreasing (lhs strictly larger than rhs)."""
function is_decreasing(eqs::Vector{Equation})::Bool
    all(_is_eq_decreasing, eqs)
end

"""Create an orthogonal rewriting prover."""
function orthogonal_prover(col::Collage, opts)
    allow_nonterm = get_bool(opts, PROGRAM_ALLOW_NONTERMINATION_UNSAFE)
    allow_empty = get_bool(opts, ALLOW_EMPTY_SORTS_UNSAFE)
    allow_noncon = get_bool(opts, PROGRAM_ALLOW_NONCONFLUENCE_UNSAFE)

    (col_simplified, replacements) = simplify_collage(col)

    eqs = Equation[eq for (_, eq) in col_simplified.ceqs]

    # Try to orient equations so larger side is LHS
    oriented = Equation[]
    for eq in eqs
        oeq = _orient_eq(eq)
        if oeq !== nothing
            push!(oriented, oeq)
        else
            if !allow_nonterm
                throw(CQLException("Rewriting Error: not size decreasing"))
            end
            push!(oriented, eq)
        end
    end
    eqs = oriented

    if !allow_empty && !all_sorts_inhabited(col)
        throw(CQLException("Rewriting Error: contains uninhabited sorts"))
    end

    # Convert equations to rewrite rules (lhs -> rhs) with head-symbol index
    rules = RewriteRule[RewriteRule(eq.lhs, eq.rhs) for eq in eqs]
    rule_idx = RuleIndex(rules)

    function prover(ctx::Ctx, eq::Equation)::Bool
        l = replace_repeatedly(replacements, eq.lhs)
        r = replace_repeatedly(replacements, eq.rhs)
        normalize(rule_idx, l) == normalize(rule_idx, r)
    end

    prover
end
