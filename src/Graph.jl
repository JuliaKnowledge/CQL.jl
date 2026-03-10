"""
Simple graph with topological sort for dependency resolution.
"""

struct SimpleGraph{T}
    vertices::Vector{T}
    edges::Vector{Tuple{T,T}}
end

"""Get outbound edges from a vertex."""
function outbound(v, g::SimpleGraph)
    [(s, t) for (s, t) in g.edges if s == v]
end

"""Get inbound edges to a vertex."""
function inbound(v, g::SimpleGraph)
    [(s, t) for (s, t) in g.edges if t == v]
end

"""Remove an edge from the graph."""
function remove_edge(g::SimpleGraph{T}, e::Tuple{T,T}) where T
    SimpleGraph(g.vertices, filter(!=(e), g.edges))
end

"""Topological sort. Returns sorted vertices or throws on cycle."""
function tsort(g::SimpleGraph{T}) where T
    no_incoming = [v for v in g.vertices if isempty(inbound(v, g))]
    result = T[]
    remaining = SimpleGraph(copy(g.vertices), copy(g.edges))
    queue = copy(no_incoming)

    while !isempty(queue)
        n = popfirst!(queue)
        push!(result, n)
        for (_, m) in outbound(n, remaining)
            remaining = remove_edge(remaining, (n, m))
            if isempty(inbound(m, remaining))
                push!(queue, m)
            end
        end
    end

    if !isempty(remaining.edges)
        throw(CQLException("There is at least one cycle in the graph."))
    end

    result
end
