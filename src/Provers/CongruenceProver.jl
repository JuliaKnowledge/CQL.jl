"""
Congruence closure prover for ground (variable-free) theories.

Uses a union-find data structure to decide equality of ground terms
modulo a set of ground equations.
"""

# ============================================================================
# Union-Find
# ============================================================================

mutable struct UnionFind
    parent::Vector{Int}
    rank::Vector{Int}
    # class_list: maps representative → list of all members in its class
    class_list::Vector{Vector{Int}}
end

UnionFind() = UnionFind(Int[], Int[], Vector{Int}[])

function uf_ensure!(uf::UnionFind, x::Int)
    while length(uf.parent) < x
        n = length(uf.parent) + 1
        push!(uf.parent, n)
        push!(uf.rank, 0)
        push!(uf.class_list, Int[n])
    end
end

function uf_find!(uf::UnionFind, x::Int)::Int
    uf_ensure!(uf, x)
    if uf.parent[x] != x
        uf.parent[x] = uf_find!(uf, uf.parent[x])  # path compression
    end
    uf.parent[x]
end

function uf_union!(uf::UnionFind, x::Int, y::Int)
    rx = uf_find!(uf, x)
    ry = uf_find!(uf, y)
    rx == ry && return
    # Always merge smaller class into larger; track new representative
    if uf.rank[rx] < uf.rank[ry]
        uf.parent[rx] = ry
        append!(uf.class_list[ry], uf.class_list[rx])
        empty!(uf.class_list[rx])
    elseif uf.rank[rx] > uf.rank[ry]
        uf.parent[ry] = rx
        append!(uf.class_list[rx], uf.class_list[ry])
        empty!(uf.class_list[ry])
    else
        uf.parent[ry] = rx
        uf.rank[rx] += 1
        append!(uf.class_list[rx], uf.class_list[ry])
        empty!(uf.class_list[ry])
    end
end

uf_equiv(uf::UnionFind, x::Int, y::Int) = uf_find!(uf, x) == uf_find!(uf, y)

# ============================================================================
# Term internalization for congruence closure
# ============================================================================

struct CCState
    uf::UnionFind
    term_to_id::Dict{CQLTerm, Int}
    id_to_term::Dict{Int, CQLTerm}
    next_id::Ref{Int}
    # For each id, store its function symbol and argument ids
    sig::Dict{Int, Tuple{Symbol, Vector{Int}}}
    # Reverse lookup: for a given id, which compound term ids use it as an argument
    use_list::Dict{Int, Vector{Int}}
    # Symbol index: maps each symbol to term ids with that symbol (for fast congruence lookup)
    sym_index::Dict{Symbol, Vector{Int}}
end

function CCState()
    CCState(
        UnionFind(),
        Dict{CQLTerm,Int}(),
        Dict{Int,CQLTerm}(),
        Ref(0),
        Dict{Int, Tuple{Symbol, Vector{Int}}}(),
        Dict{Int, Vector{Int}}(),
        Dict{Symbol, Vector{Int}}(),
    )
end

"""Find an existing interned term that is congruent with the given signature."""
function find_congruent(cc::CCState, sym::Symbol, arg_ids::Vector{Int})::Union{Int,Nothing}
    ids = get(cc.sym_index, sym, nothing)
    ids === nothing && return nothing
    for other_id in ids
        other_args = cc.sig[other_id][2]
        length(other_args) == length(arg_ids) || continue
        match = true
        for i in eachindex(arg_ids)
            if !uf_equiv(cc.uf, arg_ids[i], other_args[i])
                match = false
                break
            end
        end
        match && return other_id
    end
    nothing
end

"""Intern a term, returning its id. Recursively interns subterms.
After interning, checks for congruence with existing terms and merges if found."""
function intern!(cc::CCState, t::CQLTerm)::Int
    haskey(cc.term_to_id, t) && return cc.term_to_id[t]

    cc.next_id[] += 1
    id = cc.next_id[]
    cc.term_to_id[t] = id
    cc.id_to_term[id] = t
    uf_ensure!(cc.uf, id)  # initialize in union-find

    if t isa CQLVar
        throw(CQLException("Congruence prover received variable - theory must be ground"))
    elseif t isa CQLGen
        cc.sig[id] = (t.gen, Int[])
        push!(get!(Vector{Int}, cc.sym_index, t.gen), id)
    elseif t isa CQLSk
        cc.sig[id] = (t.sk, Int[])
        push!(get!(Vector{Int}, cc.sym_index, t.sk), id)
    elseif t isa CQLSym
        arg_ids = Int[intern!(cc, a) for a in t.args]
        cong = find_congruent(cc, t.sym, arg_ids)
        cc.sig[id] = (t.sym, arg_ids)
        push!(get!(Vector{Int}, cc.sym_index, t.sym), id)
        for aid in arg_ids
            push!(get!(Vector{Int}, cc.use_list, aid), id)
        end
        if cong !== nothing
            cc_merge!(cc, id, cong)
        end
    elseif t isa CQLFk
        aid = intern!(cc, t.arg)
        arg_ids = Int[aid]
        cong = find_congruent(cc, t.fk, arg_ids)
        cc.sig[id] = (t.fk, arg_ids)
        push!(get!(Vector{Int}, cc.sym_index, t.fk), id)
        push!(get!(Vector{Int}, cc.use_list, aid), id)
        if cong !== nothing
            cc_merge!(cc, id, cong)
        end
    elseif t isa CQLAtt
        aid = intern!(cc, t.arg)
        arg_ids = Int[aid]
        cong = find_congruent(cc, t.att, arg_ids)
        cc.sig[id] = (t.att, arg_ids)
        push!(get!(Vector{Int}, cc.sym_index, t.att), id)
        push!(get!(Vector{Int}, cc.use_list, aid), id)
        if cong !== nothing
            cc_merge!(cc, id, cong)
        end
    end

    id
end

"""Check if two nodes are congruent (same symbol, equivalent arguments)."""
function congruent(cc::CCState, a::Int, b::Int)::Bool
    !haskey(cc.sig, a) && return false
    !haskey(cc.sig, b) && return false
    (sym_a, args_a) = cc.sig[a]
    (sym_b, args_b) = cc.sig[b]
    sym_a == sym_b || return false
    length(args_a) == length(args_b) || return false
    all(uf_equiv(cc.uf, x, y) for (x, y) in zip(args_a, args_b))
end

"""Merge two equivalence classes, propagating congruence."""
function cc_merge!(cc::CCState, a::Int, b::Int)
    ra = uf_find!(cc.uf, a)
    rb = uf_find!(cc.uf, b)
    ra == rb && return

    # Collect predecessors using class membership lists (O(class_size) not O(n))
    preds_a = Int[]
    preds_b = Int[]
    for id in cc.uf.class_list[ra]
        append!(preds_a, get(cc.use_list, id, Int[]))
    end
    for id in cc.uf.class_list[rb]
        append!(preds_b, get(cc.use_list, id, Int[]))
    end

    uf_union!(cc.uf, ra, rb)

    # Check for new congruences
    for pa in preds_a
        for pb in preds_b
            if !uf_equiv(cc.uf, pa, pb) && congruent(cc, pa, pb)
                cc_merge!(cc, pa, pb)
            end
        end
    end
end

"""Build a congruence closure decision procedure from ground equations."""
function congruence_decide(equations::Vector{Tuple{CQLTerm,CQLTerm}})
    cc = CCState()

    # Intern all terms from equations
    for (lhs, rhs) in equations
        intern!(cc, lhs)
        intern!(cc, rhs)
    end

    # Merge equated terms
    for (lhs, rhs) in equations
        id_l = cc.term_to_id[lhs]
        id_r = cc.term_to_id[rhs]
        cc_merge!(cc, id_l, id_r)
    end

    # Return a decision procedure and a canonical ID function
    function decide(lhs::CQLTerm, rhs::CQLTerm)::Bool
        lhs === rhs && return true
        id_l = intern!(cc, lhs)
        id_r = intern!(cc, rhs)
        uf_equiv(cc.uf, id_l, id_r)
    end

    function canonical(t::CQLTerm)::Int
        uf_find!(cc.uf, intern!(cc, t))
    end

    (decide, canonical)
end

"""Create a congruence closure prover. Requires all equations to be ground."""
function congruence_prover(col::Collage)
    (col_simplified, _) = simplify_collage(col)

    eqs_are_ground(col_simplified) || throw(CQLException("Congruence Error: Not ground"))

    # Use original (unsimplified) equations for the congruence closure
    rules = Tuple{CQLTerm,CQLTerm}[
        (eq.lhs, eq.rhs) for (_, eq) in col.ceqs
    ]

    (hidden, canonical) = congruence_decide(rules)

    # Query directly without replacements — the CC handles all reasoning
    function prover(ctx::Ctx, eq::Equation)::Bool
        hidden(eq.lhs, eq.rhs)
    end

    prover, canonical
end
