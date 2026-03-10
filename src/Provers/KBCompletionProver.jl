"""
Knuth-Bendix completion prover with LPO ordering.

Handles non-size-decreasing equations (e.g., group axioms) by orienting
equations using a Lexicographic Path Ordering and completing the rewrite
system via critical pair computation.
"""

# ============================================================================
# Unification
# ============================================================================

"""Unify two terms. Returns a substitution Dict{Symbol,CQLTerm} or nothing."""
function unify(t1::CQLTerm, t2::CQLTerm)::Union{Nothing, Dict{Symbol, CQLTerm}}
    subst = Dict{Symbol, CQLTerm}()
    sizehint!(subst, 6)  # KB completion typically has ≤6 variables
    _unify!(t1, t2, subst) ? subst : nothing
end

"""Unify using a pre-allocated Dict (cleared before use). Returns true on success."""
@inline function unify_reuse!(t1::CQLTerm, t2::CQLTerm, subst::Dict{Symbol, CQLTerm})::Bool
    empty!(subst)
    _unify!(t1, t2, subst)
end

function _unify!(t1::CQLTerm, t2::CQLTerm, subst::Dict{Symbol, CQLTerm})::Bool
    t1 = _walk(t1, subst)
    t2 = _walk(t2, subst)

    if t1 isa CQLVar
        return _bind_var!(t1.name, t2, subst)
    elseif t2 isa CQLVar
        return _bind_var!(t2.name, t1, subst)
    elseif t1 isa CQLGen && t2 isa CQLGen
        return t1.gen == t2.gen
    elseif t1 isa CQLSk && t2 isa CQLSk
        return t1.sk == t2.sk
    elseif t1 isa CQLSym && t2 isa CQLSym
        t1.sym == t2.sym || return false
        length(t1.args) == length(t2.args) || return false
        for i in eachindex(t1.args)
            _unify!(t1.args[i], t2.args[i], subst) || return false
        end
        return true
    elseif t1 isa CQLFk && t2 isa CQLFk
        t1.fk == t2.fk || return false
        return _unify!(t1.arg, t2.arg, subst)
    elseif t1 isa CQLAtt && t2 isa CQLAtt
        t1.att == t2.att || return false
        return _unify!(t1.arg, t2.arg, subst)
    else
        return false
    end
end

"""Walk/dereference a variable through the substitution."""
function _walk(t::CQLTerm, subst::Dict{Symbol, CQLTerm})::CQLTerm
    while t isa CQLVar && haskey(subst, t.name)
        t = subst[t.name]
    end
    t
end

"""Bind a variable, performing occurs check."""
function _bind_var!(v::Symbol, t::CQLTerm, subst::Dict{Symbol, CQLTerm})::Bool
    if t isa CQLVar && t.name == v
        return true  # same variable
    end
    _occurs_in(v, t, subst) && return false  # occurs check
    subst[v] = t
    true
end

"""Check if variable v occurs in term t (with substitution applied)."""
function _occurs_in(v::Symbol, t::CQLTerm, subst::Dict{Symbol, CQLTerm})::Bool
    t = _walk(t, subst)
    if t isa CQLVar
        return t.name == v
    elseif t isa CQLSym
        for a in t.args
            _occurs_in(v, a, subst) && return true
        end
        return false
    elseif t isa CQLFk
        return _occurs_in(v, t.arg, subst)
    elseif t isa CQLAtt
        return _occurs_in(v, t.arg, subst)
    else
        return false
    end
end

"""Fully apply a substitution to a term (chase all variable bindings)."""
function full_apply_subst(t::CQLTerm, subst::Dict{Symbol, CQLTerm})::CQLTerm
    if t isa CQLVar
        t2 = _walk(t, subst)
        if t2 isa CQLVar
            return t2
        end
        return full_apply_subst(t2, subst)
    elseif t isa CQLSym
        changed = false
        new_args = t.args
        for (i, a) in enumerate(t.args)
            na = full_apply_subst(a, subst)
            if na !== a
                if !changed
                    new_args = copy(t.args)
                    changed = true
                end
                new_args[i] = na
            end
        end
        return changed ? CQLSym(t.sym, new_args) : t
    elseif t isa CQLFk
        na = full_apply_subst(t.arg, subst)
        return na === t.arg ? t : CQLFk(t.fk, na)
    elseif t isa CQLAtt
        na = full_apply_subst(t.arg, subst)
        return na === t.arg ? t : CQLAtt(t.att, na)
    else
        return t  # CQLGen, CQLSk
    end
end

# ============================================================================
# Knuth-Bendix Ordering (KBO) — primary term ordering
# ============================================================================

"""Get the head symbol for term ordering."""
function _lpo_head(t::CQLTerm)::Union{Symbol, Nothing}
    if t isa CQLSym; return t.sym
    elseif t isa CQLFk; return t.fk
    elseif t isa CQLAtt; return t.att
    elseif t isa CQLGen; return t.gen
    elseif t isa CQLSk; return t.sk
    else return nothing
    end
end

"""Get the arguments of a term."""
function _lpo_args(t::CQLTerm)::Vector{CQLTerm}
    if t isa CQLSym; return t.args
    elseif t isa CQLFk; return CQLTerm[t.arg]
    elseif t isa CQLAtt; return CQLTerm[t.arg]
    else return CQLTerm[]
    end
end

"""Get the kind rank for precedence ordering."""
function _kind_rank(t::CQLTerm)::Int
    if t isa CQLGen; return 5
    elseif t isa CQLSk; return 4
    elseif t isa CQLSym; return 3
    elseif t isa CQLFk; return 2
    elseif t isa CQLAtt; return 1
    else return 0
    end
end

"""Count variable occurrences in a term. Returns Dict{Symbol, Int}."""
function _var_counts(t::CQLTerm)::Dict{Symbol, Int}
    counts = Dict{Symbol, Int}()
    _count_vars!(t, counts)
    counts
end

function _count_vars!(t::CQLTerm, counts::Dict{Symbol, Int})
    if t isa CQLVar
        counts[t.name] = get(counts, t.name, 0) + 1
    elseif t isa CQLSym
        for a in t.args; _count_vars!(a, counts); end
    elseif t isa CQLFk
        _count_vars!(t.arg, counts)
    elseif t isa CQLAtt
        _count_vars!(t.arg, counts)
    end
end

"""Compute KBO weight of a term. Variables have weight 1, symbols use weight map."""
function _kbo_weight(t::CQLTerm, weights::Dict{Symbol, Int})::Int
    if t isa CQLVar
        return 1
    elseif t isa CQLSym
        w = get(weights, t.sym, 1)
        for a in t.args; w += _kbo_weight(a, weights); end
        return w
    elseif t isa CQLFk
        return get(weights, t.fk, 1) + _kbo_weight(t.arg, weights)
    elseif t isa CQLAtt
        return get(weights, t.att, 1) + _kbo_weight(t.arg, weights)
    elseif t isa CQLGen
        return get(weights, t.gen, 1)
    elseif t isa CQLSk
        return get(weights, t.sk, 1)
    else
        return 1
    end
end

"""
Compare two terms using Knuth-Bendix Ordering (KBO).

KBO is much faster than LPO: O(n) weight computation + O(n) variable check,
with precedence-based tiebreaking only when weights are equal.

Returns :GT, :LT, :EQ, or :INCOMPARABLE.
"""
function kbo_compare(prec::Dict{Symbol,Int}, weights::Dict{Symbol,Int},
                     s::CQLTerm, t::CQLTerm)::Symbol
    s == t && return :EQ

    # Variable special cases
    if s isa CQLVar && t isa CQLVar
        return :INCOMPARABLE
    end
    if s isa CQLVar
        return _occurs_in_simple(s.name, t) ? :LT : :INCOMPARABLE
    end
    if t isa CQLVar
        return _occurs_in_simple(t.name, s) ? :GT : :INCOMPARABLE
    end

    # Compute weights
    ws = _kbo_weight(s, weights)
    wt = _kbo_weight(t, weights)

    # Variable condition: for s > t, every variable must occur at least as
    # often in s as in t
    s_vars = _var_counts(s)
    t_vars = _var_counts(t)

    s_ge_t = true  # s has >= occurrences of all t's vars
    t_ge_s = true  # t has >= occurrences of all s's vars
    for (v, cnt) in t_vars
        if get(s_vars, v, 0) < cnt
            s_ge_t = false
            break
        end
    end
    for (v, cnt) in s_vars
        if get(t_vars, v, 0) < cnt
            t_ge_s = false
            break
        end
    end

    if ws > wt && s_ge_t
        return :GT
    elseif wt > ws && t_ge_s
        return :LT
    elseif ws == wt
        # Equal weight: compare by precedence, then lexicographically
        s_head = _lpo_head(s)
        t_head = _lpo_head(t)
        if s_head !== nothing && t_head !== nothing
            sp = get(prec, s_head, _default_prec(s))
            tp = get(prec, t_head, _default_prec(t))
            if sp > tp && s_ge_t
                return :GT
            elseif tp > sp && t_ge_s
                return :LT
            elseif sp == tp && s_head == t_head
                # Same head: lexicographic comparison of arguments
                cmp = _kbo_lex_compare(prec, weights, _lpo_args(s), _lpo_args(t))
                if cmp == :GT && s_ge_t
                    return :GT
                elseif cmp == :LT && t_ge_s
                    return :LT
                end
            end
        end
    end

    return :INCOMPARABLE
end

"""Lexicographic comparison of argument lists for KBO."""
function _kbo_lex_compare(prec, weights, s_args, t_args)::Symbol
    for i in 1:min(length(s_args), length(t_args))
        cmp = kbo_compare(prec, weights, s_args[i], t_args[i])
        cmp != :EQ && return cmp
    end
    la, lt = length(s_args), length(t_args)
    la > lt ? :GT : la < lt ? :LT : :EQ
end

"""Default precedence based on kind and name."""
function _default_prec(t::CQLTerm)::Int
    base = _kind_rank(t) * 1000
    h = _lpo_head(t)
    h === nothing && return base
    base + (hash(h) % 500)
end

"""Simple occurs check (no substitution)."""
function _occurs_in_simple(v::Symbol, t::CQLTerm)::Bool
    if t isa CQLVar; return t.name == v
    elseif t isa CQLSym
        for a in t.args; _occurs_in_simple(v, a) && return true; end
        return false
    elseif t isa CQLFk; return _occurs_in_simple(v, t.arg)
    elseif t isa CQLAtt; return _occurs_in_simple(v, t.arg)
    else return false
    end
end

# Keep LPO as fallback for cases where KBO fails to orient
"""Compare two terms using Lexicographic Path Ordering (LPO) with memoization."""
function lpo_compare(prec::Dict{Symbol,Int}, s::CQLTerm, t::CQLTerm)::Symbol
    cache = Dict{UInt128, Symbol}()
    sizehint!(cache, 32)
    _lpo_cached(prec, s, t, cache)
end

"""LPO with shared cache (for use within kb_complete to persist cache across calls)."""
function lpo_compare(prec::Dict{Symbol,Int}, s::CQLTerm, t::CQLTerm,
                     cache::Dict{UInt128, Symbol})::Symbol
    _lpo_cached(prec, s, t, cache)
end

@inline function _lpo_cache_key(s::CQLTerm, t::CQLTerm)::UInt128
    UInt128(objectid(s)) << 64 | UInt128(objectid(t))
end

function _lpo_cached(prec::Dict{Symbol,Int}, s::CQLTerm, t::CQLTerm,
                     cache::Dict{UInt128, Symbol})::Symbol
    key = _lpo_cache_key(s, t)
    cached = get(cache, key, nothing)
    cached !== nothing && return cached
    result = _lpo_impl(prec, s, t, cache)
    cache[key] = result
    result
end

function _lpo_impl(prec::Dict{Symbol,Int}, s::CQLTerm, t::CQLTerm,
                   cache::Dict{UInt128, Symbol})::Symbol
    if s isa CQLVar && t isa CQLVar
        return s.name == t.name ? :EQ : :INCOMPARABLE
    end
    s isa CQLVar && return (_occurs_in_simple(s.name, t) ? :LT : :INCOMPARABLE)
    t isa CQLVar && return (_occurs_in_simple(t.name, s) ? :GT : :INCOMPARABLE)
    s === t && return :EQ
    s == t && return :EQ

    s_head = _lpo_head(s)
    t_head = _lpo_head(t)

    # LPO1: s > t if some si >= t (inline args iteration)
    if s isa CQLSym
        for si in s.args
            cmp = _lpo_cached(prec, si, t, cache)
            (cmp == :GT || cmp == :EQ) && return :GT
        end
    elseif s isa CQLFk
        cmp = _lpo_cached(prec, s.arg, t, cache)
        (cmp == :GT || cmp == :EQ) && return :GT
    elseif s isa CQLAtt
        cmp = _lpo_cached(prec, s.arg, t, cache)
        (cmp == :GT || cmp == :EQ) && return :GT
    end

    if s_head !== nothing && t_head !== nothing
        sp = get(prec, s_head, _default_prec(s))
        tp = get(prec, t_head, _default_prec(t))

        if sp > tp
            if _all_gt_lpo(prec, s, t, cache)
                return :GT
            end
        elseif sp == tp && s_head == t_head
            if _all_gt_lpo(prec, s, t, cache)
                cmp = _lex_compare_cached(prec, s, t, cache)
                cmp == :GT && return :GT
            end
        elseif sp < tp
            # Check if some tj >= s
            if t isa CQLSym
                for tj in t.args
                    cmp = _lpo_cached(prec, tj, s, cache)
                    (cmp == :GT || cmp == :EQ) && return :LT
                end
            elseif t isa CQLFk
                cmp = _lpo_cached(prec, t.arg, s, cache)
                (cmp == :GT || cmp == :EQ) && return :LT
            elseif t isa CQLAtt
                cmp = _lpo_cached(prec, t.arg, s, cache)
                (cmp == :GT || cmp == :EQ) && return :LT
            end
            if _all_gt_lpo_rev(prec, t, s, cache)
                return :LT
            end
        end
    end

    # Check if some tj >= s
    if t isa CQLSym
        for tj in t.args
            cmp = _lpo_cached(prec, tj, s, cache)
            (cmp == :GT || cmp == :EQ) && return :LT
        end
    elseif t isa CQLFk
        cmp = _lpo_cached(prec, t.arg, s, cache)
        (cmp == :GT || cmp == :EQ) && return :LT
    elseif t isa CQLAtt
        cmp = _lpo_cached(prec, t.arg, s, cache)
        (cmp == :GT || cmp == :EQ) && return :LT
    end

    return :INCOMPARABLE
end

"""Check: for all tj in t.args, s > tj (inlined, no allocation)."""
@inline function _all_gt_lpo(prec, s, t, cache)::Bool
    if t isa CQLSym
        for tj in t.args
            _lpo_cached(prec, s, tj, cache) != :GT && return false
        end
    elseif t isa CQLFk
        _lpo_cached(prec, s, t.arg, cache) != :GT && return false
    elseif t isa CQLAtt
        _lpo_cached(prec, s, t.arg, cache) != :GT && return false
    end
    true
end

"""Check: for all si in s.args, t > si (inlined, no allocation)."""
@inline function _all_gt_lpo_rev(prec, t, s, cache)::Bool
    if s isa CQLSym
        for si in s.args
            _lpo_cached(prec, t, si, cache) != :GT && return false
        end
    elseif s isa CQLFk
        _lpo_cached(prec, t, s.arg, cache) != :GT && return false
    elseif s isa CQLAtt
        _lpo_cached(prec, t, s.arg, cache) != :GT && return false
    end
    true
end

function _lex_compare_cached(prec, s, t, cache)::Symbol
    # Inline args access for s and t
    s_args = s isa CQLSym ? s.args : s isa CQLFk ? CQLTerm[s.arg] : s isa CQLAtt ? CQLTerm[s.arg] : CQLTerm[]
    t_args = t isa CQLSym ? t.args : t isa CQLFk ? CQLTerm[t.arg] : t isa CQLAtt ? CQLTerm[t.arg] : CQLTerm[]
    for i in 1:min(length(s_args), length(t_args))
        cmp = _lpo_cached(prec, s_args[i], t_args[i], cache)
        if cmp == :GT
            # Check remaining t_args: all must be < s
            for j in i+1:length(t_args)
                _lpo_cached(prec, s, t_args[j], cache) != :GT && return :INCOMPARABLE
            end
            return :GT
        elseif cmp == :LT
            return :LT
        end
    end
    la, lt = length(s_args), length(t_args)
    la > lt ? :GT : la < lt ? :LT : :EQ
end

# ============================================================================
# Critical pair computation
# ============================================================================

# Counter for renaming variables to avoid capture
const _kb_var_counter = Ref(0)

# Pre-generated variable symbol pool for fast lookup
const _KB_VAR_POOL_SIZE = 50000
const _kb_var_pool = Symbol[Symbol("_kbv", i) for i in 1:_KB_VAR_POOL_SIZE]

"""Get a fresh variable symbol (O(1) for pooled range)."""
@inline function _fresh_var_sym()::Symbol
    _kb_var_counter[] += 1
    c = _kb_var_counter[]
    c <= _KB_VAR_POOL_SIZE ? @inbounds(_kb_var_pool[c]) : Symbol("_kbv", c)
end

"""Rename all variables in a term to fresh names."""
function rename_vars(t::CQLTerm)::Tuple{CQLTerm, Dict{Symbol,Symbol}}
    mapping = Dict{Symbol,Symbol}()
    renamed = _rename(t, mapping)
    (renamed, mapping)
end

function _rename(t::CQLTerm, mapping::Dict{Symbol,Symbol})::CQLTerm
    if t isa CQLVar
        if !haskey(mapping, t.name)
            mapping[t.name] = _fresh_var_sym()
        end
        return CQLVar(mapping[t.name])
    elseif t isa CQLSym
        changed = false
        new_args = t.args
        for (i, a) in enumerate(t.args)
            na = _rename(a, mapping)
            if na !== a
                if !changed
                    new_args = copy(t.args)
                    changed = true
                end
                new_args[i] = na
            end
        end
        return changed ? CQLSym(t.sym, new_args) : t
    elseif t isa CQLFk
        na = _rename(t.arg, mapping)
        return na === t.arg ? t : CQLFk(t.fk, na)
    elseif t isa CQLAtt
        na = _rename(t.arg, mapping)
        return na === t.arg ? t : CQLAtt(t.att, na)
    else
        return t
    end
end

"""Rename a rewrite rule with fresh variables."""
function rename_rule(r::RewriteRule)::RewriteRule
    mapping = Dict{Symbol,Symbol}()
    lhs = _rename(r.lhs, mapping)
    rhs = _rename(r.rhs, mapping)
    RewriteRule(lhs, rhs)
end

"""Get all non-variable subterm positions in a term.
Returns a list of (position_path, subterm) pairs."""
function subterm_positions(t::CQLTerm)::Vector{Tuple{Vector{Int}, CQLTerm}}
    result = Tuple{Vector{Int}, CQLTerm}[]
    path_buf = Int[]
    _collect_positions!(t, path_buf, result)
    result
end

function _collect_positions!(t::CQLTerm, path::Vector{Int}, result)
    push!(result, (copy(path), t))
    if t isa CQLSym
        for i in eachindex(t.args)
            push!(path, i)
            _collect_positions!(t.args[i], path, result)
            pop!(path)
        end
    elseif t isa CQLFk
        push!(path, 1)
        _collect_positions!(t.arg, path, result)
        pop!(path)
    elseif t isa CQLAtt
        push!(path, 1)
        _collect_positions!(t.arg, path, result)
        pop!(path)
    end
end

"""Replace a subterm at a given position."""
function replace_at(t::CQLTerm, path::Vector{Int}, replacement::CQLTerm)::CQLTerm
    isempty(path) && return replacement
    return _replace_at_impl(t, path, 1, replacement)
end

function _replace_at_impl(t::CQLTerm, path::Vector{Int}, depth::Int, replacement::CQLTerm)::CQLTerm
    depth > length(path) && return replacement
    idx = path[depth]
    if t isa CQLSym
        new_args = copy(t.args)
        new_args[idx] = _replace_at_impl(t.args[idx], path, depth + 1, replacement)
        return CQLSym(t.sym, new_args)
    elseif t isa CQLFk
        return CQLFk(t.fk, _replace_at_impl(t.arg, path, depth + 1, replacement))
    elseif t isa CQLAtt
        return CQLAtt(t.att, _replace_at_impl(t.arg, path, depth + 1, replacement))
    else
        error("Invalid position path for term: $t")
    end
end

"""Compute all critical pairs between two rules, pushing results into `out`."""
function critical_pairs!(out::Vector{Equation}, r1::RewriteRule, r2::RewriteRule,
                         unify_buf::Dict{Symbol, CQLTerm}, rename_map::Dict{Symbol, Symbol})
    # Rename r2 to avoid variable conflicts (reuse mapping dict)
    empty!(rename_map)
    r2_lhs = _rename(r2.lhs, rename_map)
    r2_rhs = _rename(r2.rhs, rename_map)

    # Inline subterm iteration: try unifying each non-variable subterm of r1.lhs with r2_lhs
    _cp_at_subterms!(out, r1, r2_lhs, r2_rhs, r1.lhs, Int[], unify_buf)
end

"""Recurse through term t collecting critical pairs at each non-variable position."""
function _cp_at_subterms!(out::Vector{Equation}, r1::RewriteRule,
                          r2_lhs::CQLTerm, r2_rhs::CQLTerm,
                          t::CQLTerm, path::Vector{Int},
                          unify_buf::Dict{Symbol, CQLTerm})
    # Skip variables
    t isa CQLVar && return

    # Try unification at this position
    if unify_reuse!(t, r2_lhs, unify_buf)
        cp_lhs = full_apply_subst(replace_at(r1.lhs, path, r2_rhs), unify_buf)
        cp_rhs = full_apply_subst(r1.rhs, unify_buf)
        if cp_lhs != cp_rhs
            push!(out, Equation(cp_lhs, cp_rhs))
        end
    end

    # Recurse into subterms
    if t isa CQLSym
        for i in eachindex(t.args)
            push!(path, i)
            _cp_at_subterms!(out, r1, r2_lhs, r2_rhs, t.args[i], path, unify_buf)
            pop!(path)
        end
    elseif t isa CQLFk
        push!(path, 1)
        _cp_at_subterms!(out, r1, r2_lhs, r2_rhs, t.arg, path, unify_buf)
        pop!(path)
    elseif t isa CQLAtt
        push!(path, 1)
        _cp_at_subterms!(out, r1, r2_lhs, r2_rhs, t.arg, path, unify_buf)
        pop!(path)
    end
end

# Keep backward-compatible API (used in tests)
"""Compute all critical pairs between two rules."""
function critical_pairs(r1::RewriteRule, r2::RewriteRule)::Vector{Tuple{CQLTerm, CQLTerm}}
    eqs = Equation[]
    unify_buf = Dict{Symbol, CQLTerm}()
    sizehint!(unify_buf, 8)
    rename_map = Dict{Symbol, Symbol}()
    critical_pairs!(eqs, r1, r2, unify_buf, rename_map)
    return [(eq.lhs, eq.rhs) for eq in eqs]
end

# ============================================================================
# Completion loop
# ============================================================================

"""Build default precedence from equations.

When `reverse_arity=false` (default): binary > unary > constant.
Good for Peano arithmetic (plus > succ > zero).

When `reverse_arity=true`: unary > binary > constant.
Good for group theory (I > o > e).
"""
function build_default_precedence(eqs::Vector{Equation}; reverse_arity::Bool=false)::Dict{Symbol,Int}
    prec = Dict{Symbol,Int}()
    # Collect all head symbols with their max arity and kind rank
    head_info = Dict{Symbol, Tuple{Int,Int}}()  # symbol -> (max_arity, kind_rank)
    for eq in eqs
        _collect_heads!(eq.lhs, head_info)
        _collect_heads!(eq.rhs, head_info)
    end

    # Constants always get lowest precedence.
    # For non-constants, ordering depends on reverse_arity flag.
    function _prec_class(arity::Int)::Int
        if arity == 0
            0  # constants → lowest
        elseif reverse_arity
            # unary(2) > binary(1) > constants(0) — good for group theory
            arity == 1 ? 2 : 1
        else
            # binary(2) > unary(1) > constants(0) — good for arithmetic
            arity
        end
    end

    sorted = sort(collect(head_info), by = kv -> begin
        (sym, (arity, kind)) = kv
        (_prec_class(arity), kind, string(sym))
    end)

    for (i, (h, _)) in enumerate(sorted)
        prec[h] = i
    end
    prec
end

function _collect_heads!(t::CQLTerm, heads::Dict{Symbol, Tuple{Int,Int}})
    if t isa CQLSym
        arity = length(t.args)
        prev = get(heads, t.sym, (0, 3))
        heads[t.sym] = (max(prev[1], arity), 3)
        for a in t.args; _collect_heads!(a, heads); end
    elseif t isa CQLFk
        heads[t.fk] = (max(get(heads, t.fk, (0, 2))[1], 1), 2)
        _collect_heads!(t.arg, heads)
    elseif t isa CQLAtt
        heads[t.att] = (max(get(heads, t.att, (0, 1))[1], 1), 1)
        _collect_heads!(t.arg, heads)
    elseif t isa CQLGen
        heads[t.gen] = (max(get(heads, t.gen, (0, 5))[1], 0), 5)
    elseif t isa CQLSk
        heads[t.sk] = (max(get(heads, t.sk, (0, 4))[1], 0), 4)
    end
end

"""Run Knuth-Bendix completion to produce a confluent TRS.

Uses head-symbol indexed rule lookup (twee-lib style) for O(1) normalize dispatch.
Returns (rules, passive_eqs, converged) where converged indicates the pending queue was exhausted."""
function kb_complete(eqs::Vector{Equation}, prec::Dict{Symbol,Int};
                     max_rules::Int=500, max_iters::Int=10000,
                     timeout_seconds::Real=30)::Tuple{Vector{RewriteRule}, Vector{Equation}, Bool}
    @debug "kb_complete: $(length(eqs)) eqs, prec=$prec, timeout=$(timeout_seconds)s"
    rules = RewriteRule[]
    passive = Equation[]  # non-orientable equations for unfailing completion

    pending = Equation[eq for eq in eqs]
    start_time = time()

    # Reset var counter to stay within pre-allocated pool
    _kb_var_counter[] = 0

    # Head-symbol indexed rule set — rebuilt when rules change
    rule_idx = RuleIndex(rules)
    rules_changed = false

    # Reusable buffers for critical pair computation
    cp_unify_buf = Dict{Symbol, CQLTerm}()
    sizehint!(cp_unify_buf, 8)
    cp_rename_map = Dict{Symbol, Symbol}()
    cp_path_buf = Int[]

    # Persistent LPO cache (survives across iterations for cached comparisons)
    lpo_cache = Dict{UInt128, Symbol}()
    sizehint!(lpo_cache, 256)

    # Early convergence detection
    stable_count = 0
    last_rule_count = 0

    iter = 0
    while !isempty(pending) && iter < max_iters
        iter += 1
        if time() - start_time > timeout_seconds
            break
        end
        eq = popfirst!(pending)

        # Rebuild index when rules changed
        if rules_changed
            rule_idx = RuleIndex(rules)
            rules_changed = false
        end

        # Normalize both sides using indexed rules (inner-most strategy)
        lhs_nf = normalize_innermost(rule_idx, eq.lhs)
        rhs_nf = normalize_innermost(rule_idx, eq.rhs)

        if lhs_nf == rhs_nf
            stable_count += 1
            if stable_count >= 100 && length(rules) == last_rule_count
                local all_joinable = true
                local checked = 0
                while !isempty(pending) && checked < 500
                    checked += 1
                    eq2 = popfirst!(pending)
                    l2 = normalize_innermost(rule_idx, eq2.lhs)
                    r2 = normalize_innermost(rule_idx, eq2.rhs)
                    if l2 != r2
                        all_joinable = false
                        pushfirst!(pending, eq2)
                        break
                    end
                end
                if all_joinable
                    @debug "kb_complete: early convergence at iter $iter ($(length(rules)) rules, $stable_count+$checked joinable)"
                    return (rules, passive, true)
                end
            end
            continue
        end

        stable_count = 0

        # Orient using LPO (with persistent cache)
        cmp = lpo_compare(prec, lhs_nf, rhs_nf, lpo_cache)

        local new_rule::Union{RewriteRule, Nothing} = nothing
        if cmp == :GT
            new_rule = RewriteRule(lhs_nf, rhs_nf)
        elseif cmp == :LT
            new_rule = RewriteRule(rhs_nf, lhs_nf)
        else
            # Try size-based orientation as fallback
            sl = term_size(lhs_nf); sr = term_size(rhs_nf)
            if sl > sr
                new_rule = RewriteRule(lhs_nf, rhs_nf)
            elseif sr > sl
                new_rule = RewriteRule(rhs_nf, lhs_nf)
            else
                push!(passive, Equation(lhs_nf, rhs_nf))
                continue
            end
        end

        # Inter-reduce using the single new rule (with reusable index)
        new_rule_idx = RuleIndex(RewriteRule[new_rule])
        reduced_rules = RewriteRule[]
        sizehint!(reduced_rules, length(rules))
        for r in rules
            r_lhs_rewrite = rewrite_one_step(new_rule_idx, r.lhs)
            r_rhs_rewrite = normalize_innermost(new_rule_idx, r.rhs)
            if r_lhs_rewrite !== nothing
                push!(pending, Equation(r_lhs_rewrite, r_rhs_rewrite))
            else
                new_rhs = r_rhs_rewrite
                if new_rhs != r.rhs
                    push!(reduced_rules, RewriteRule(r.lhs, new_rhs))
                else
                    push!(reduced_rules, r)
                end
            end
        end
        rules = reduced_rules

        # Compute critical pairs with all existing rules (reusing buffers)
        for r in rules
            critical_pairs!(pending, new_rule, r, cp_unify_buf, cp_rename_map)
            critical_pairs!(pending, r, new_rule, cp_unify_buf, cp_rename_map)
        end
        # Self-critical pairs
        critical_pairs!(pending, new_rule, new_rule, cp_unify_buf, cp_rename_map)

        push!(rules, new_rule)
        last_rule_count = length(rules)
        rules_changed = true

        if length(rules) > max_rules
            break
        end
    end

    converged = isempty(pending)
    @debug "kb_complete: $(length(eqs)) eqs, $(iter) iters → $(length(rules)) rules in $(round(time()-start_time, digits=2))s$(converged ? " (converged)" : "")"
    (rules, passive, converged)
end

"""Collect arities of all head symbols in a term."""
function _collect_arities!(t::CQLTerm, arities::Dict{Symbol, Int})
    if t isa CQLSym
        arities[t.sym] = max(get(arities, t.sym, 0), length(t.args))
        for a in t.args; _collect_arities!(a, arities); end
    elseif t isa CQLFk
        arities[t.fk] = max(get(arities, t.fk, 0), 1)
        _collect_arities!(t.arg, arities)
    elseif t isa CQLAtt
        arities[t.att] = max(get(arities, t.att, 0), 1)
        _collect_arities!(t.arg, arities)
    end
end

# ============================================================================
# Unfailing completion: passive equation checking
# ============================================================================

"""Check if two normalized terms are provably equal using passive equations.

Passive equations can be applied bidirectionally. We do a bounded search:
try substituting passive equations into the terms and re-normalizing."""
function _check_passive(rules::Vector{RewriteRule}, passive::Vector{Equation},
                        t1::CQLTerm, t2::CQLTerm; max_depth::Int=3)::Bool
    t1 == t2 && return true
    max_depth <= 0 && return false

    # Try each passive equation as a rewrite in both directions on t1
    for peq in passive
        for (from, to) in [(peq.lhs, peq.rhs), (peq.rhs, peq.lhs)]
            for new_t1 in _apply_eq_at_all_positions(from, to, t1)
                new_t1_nf = normalize(rules, new_t1)
                if new_t1_nf == t2
                    return true
                end
                if max_depth > 1 && _check_passive(rules, passive, new_t1_nf, t2; max_depth=max_depth-1)
                    return true
                end
            end
        end
    end
    false
end

"""Apply equation lhs→rhs at all matching positions in term t. Returns a vector of new terms."""
function _apply_eq_at_all_positions(from::CQLTerm, to::CQLTerm, t::CQLTerm)::Vector{CQLTerm}
    results = CQLTerm[]
    # Try matching at root
    σ = match_term(from, t)
    if σ !== nothing
        push!(results, apply_subst(to, σ))
    end
    # Try matching in subterms
    if t isa CQLFk
        for new_arg in _apply_eq_at_all_positions(from, to, t.arg)
            push!(results, CQLFk(t.fk, new_arg))
        end
    elseif t isa CQLAtt
        for new_arg in _apply_eq_at_all_positions(from, to, t.arg)
            push!(results, CQLAtt(t.att, new_arg))
        end
    elseif t isa CQLSym
        for i in 1:length(t.args)
            for new_arg in _apply_eq_at_all_positions(from, to, t.args[i])
                new_args = copy(t.args)
                new_args[i] = new_arg
                push!(results, CQLSym(t.sym, new_args))
            end
        end
    end
    results
end

# ============================================================================
# Prover function
# ============================================================================

# Global cache for completed rule sets to avoid re-running KB completion
# when the same equations appear across typeside/schema/instance stages.
const _KB_CACHE = Dict{UInt64, Tuple{Vector{RewriteRule}, Vector{Equation}}}()
const _KB_CACHE_LOCK = ReentrantLock()

# Cache: function symbols → which precedence ordering worked (to avoid retrying wrong orderings)
const _KB_PREC_HINT = Dict{Set{Symbol}, Bool}()  # symbols → reverse_arity flag that worked

function _kb_cache_key(eqs::Vector{Equation}, prec::Dict{Symbol,Int})::UInt64
    h = UInt64(0xdeadbeef)
    for eq in sort(eqs, by=eq -> hash(eq))
        h = hash(eq.lhs, h)
        h = hash(eq.rhs, h)
    end
    for (k, v) in sort(collect(prec), by=first)
        h = hash(k, h)
        h = hash(v, h)
    end
    h
end

function _collect_symbols(eqs::Vector{Equation})::Set{Symbol}
    syms = Set{Symbol}()
    for eq in eqs
        _collect_syms!(eq.lhs, syms)
        _collect_syms!(eq.rhs, syms)
    end
    syms
end
function _collect_syms!(t::CQLTerm, syms::Set{Symbol})
    if t isa CQLSym
        push!(syms, t.sym)
        for a in t.args; _collect_syms!(a, syms); end
    elseif t isa CQLFk
        push!(syms, t.fk)
        _collect_syms!(t.arg, syms)
    elseif t isa CQLAtt
        push!(syms, t.att)
        _collect_syms!(t.arg, syms)
    elseif t isa CQLGen
        push!(syms, t.gen)
    elseif t isa CQLSk
        push!(syms, t.sk)
    end
end

"""Create a KB completion prover."""
function kb_completion_prover(col::Collage, opts::CQLOptions)
    (col_simplified, replacements) = simplify_collage(col)

    eqs = Equation[eq for (_, eq) in col_simplified.ceqs]

    isempty(eqs) && return (ctx::Ctx, eq::Equation) -> begin
        l = replace_repeatedly(replacements, eq.lhs)
        r = replace_repeatedly(replacements, eq.rhs)
        l == r
    end

    # Parse custom precedence from options if provided
    prec_str = get_str(opts, COMPLETION_PRECEDENCE)
    has_custom_prec = !isempty(prec_str)

    # Build candidate precedence orderings to try.
    prec_candidates = Dict{Symbol,Int}[]
    hint_ra = nothing  # track which reverse_arity is tried first
    if has_custom_prec
        prec = build_default_precedence(eqs)
        sep = occursin(",", prec_str) ? "," : r"\s+"
        parts = split(strip(prec_str), Regex(string(sep)))
        for (i, p) in enumerate(parts)
            s = Symbol(strip(String(p)))
            isempty(string(s)) && continue
            prec[s] = i * 10
        end
        push!(prec_candidates, prec)
    else
        # Check if we have a hint for which ordering works for these symbols
        eq_syms = _collect_symbols(eqs)
        for (cached_syms, ra) in _KB_PREC_HINT
            if cached_syms ⊆ eq_syms
                hint_ra = ra
                break
            end
        end
        if hint_ra !== nothing
            push!(prec_candidates, build_default_precedence(eqs; reverse_arity=hint_ra))
            push!(prec_candidates, build_default_precedence(eqs; reverse_arity=!hint_ra))
        else
            push!(prec_candidates, build_default_precedence(eqs; reverse_arity=false))
            push!(prec_candidates, build_default_precedence(eqs; reverse_arity=true))
        end
    end
    # Track which reverse_arity each candidate uses
    ra_flags = if has_custom_prec
        Bool[false]
    elseif hint_ra !== nothing
        Bool[hint_ra, !hint_ra]
    else
        Bool[false, true]
    end

    # Run completion, trying each precedence candidate
    timeout_seconds = get_int(opts, TIMEOUT)
    local rules::Vector{RewriteRule}
    local passive::Vector{Equation}
    last_err = nothing
    cached = false

    # Check global cache first for each candidate
    for prec in prec_candidates
        cache_key = _kb_cache_key(eqs, prec)
        lock(_KB_CACHE_LOCK) do
            if haskey(_KB_CACHE, cache_key)
                (rules, passive) = _KB_CACHE[cache_key]
                cached = true
            end
        end
        cached && break
    end

    if !cached
        # No cache hit — run completion
        last_err = nothing

        for (idx, prec) in enumerate(prec_candidates)
            try
                per_attempt_timeout = if has_custom_prec
                    timeout_seconds
                elseif idx < length(prec_candidates)
                    # Non-last: short timeout — correct ordering converges fast
                    max(timeout_seconds ÷ 10, 3)
                else
                    # Last candidate: full timeout
                    timeout_seconds
                end
                (rules, passive, converged) = kb_complete(eqs, prec;
                    timeout_seconds=per_attempt_timeout)
                # For non-last candidates, require convergence
                if !converged && idx < length(prec_candidates) && !has_custom_prec
                    throw(CQLException("KB completion did not converge with precedence ordering #$idx"))
                end
                last_err = nothing
                # Cache the result
                cache_key = _kb_cache_key(eqs, prec)
                lock(_KB_CACHE_LOCK) do
                    _KB_CACHE[cache_key] = (rules, passive)
                end
                # Save precedence hint for future calls with overlapping symbols
                if !has_custom_prec && converged && idx <= length(ra_flags)
                    _KB_PREC_HINT[_collect_symbols(eqs)] = ra_flags[idx]
                end
                break
            catch e
                last_err = e
                if !(e isa CQLException)
                    rethrow(e)
                end
            end
        end
    end
    if last_err !== nothing
        throw(CQLException("KB Completion failed: $(last_err isa CQLException ? last_err.msg : sprint(showerror, last_err))"))
    end

    # Build indexed rule set for efficient normalization during proving
    rule_idx = RuleIndex(rules)

    function prover(ctx::Ctx, eq::Equation)::Bool
        l = replace_repeatedly(replacements, eq.lhs)
        r = replace_repeatedly(replacements, eq.rhs)
        ln = normalize_innermost(rule_idx, l)
        rn = normalize_innermost(rule_idx, r)
        ln == rn && return true
        # Unfailing: try passive equations bidirectionally
        if !isempty(passive)
            _check_passive(rules, passive, ln, rn)
        else
            false
        end
    end

    prover
end
