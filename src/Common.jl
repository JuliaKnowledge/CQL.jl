"""
Common types and utilities for CQL.
"""

"""CQL expression kinds for dependency tracking."""
@enum Kind begin
    TYPESIDE
    SCHEMA
    INSTANCE
    MAPPING
    TRANSFORM
    QUERY
    COMMAND
    GRAPH
    COMMENT
    SCHEMA_COLIMIT
    CONSTRAINTS
end

"""Base exception type for CQL errors."""
struct CQLException <: Exception
    msg::String
end
Base.showerror(io::IO, e::CQLException) = print(io, "CQLError: ", e.msg)

"""Wrap an error message with a prefix context."""
function wrap_error(prefix::String, result)
    if result isa Exception
        CQLException("$prefix: $(result.msg)")
    else
        result
    end
end

"""Convert a list to a Set, erroring on duplicates."""
function to_set_safely(items)
    s = Set{eltype(items)}()
    for k in items
        if k in s
            throw(CQLException("Duplicate binding: $k"))
        end
        push!(s, k)
    end
    s
end

"""Convert a list of pairs to a Dict, erroring on duplicate keys."""
function to_dict_safely(pairs)
    d = Dict{typeof(first(first(pairs))), typeof(last(first(pairs)))}()
    for (k, v) in pairs
        if haskey(d, k)
            throw(CQLException("Duplicate binding: $k"))
        end
        d[k] = v
    end
    d
end

function to_dict_safely(pairs::Vector{Tuple{K,V}}) where {K,V}
    d = Dict{K,V}()
    for (k, v) in pairs
        if haskey(d, k)
            throw(CQLException("Duplicate binding: $k"))
        end
        d[k] = v
    end
    d
end

function to_dict_safely(pairs::Vector{Pair{K,V}}) where {K,V}
    d = Dict{K,V}()
    for (k, v) in pairs
        if haskey(d, k)
            throw(CQLException("Duplicate binding: $k"))
        end
        d[k] = v
    end
    d
end

# Empty case
function to_dict_safely(::Vector{Any})
    Dict{Symbol,Any}()
end

"""Safe dictionary lookup with error message."""
function safe_lookup(d::Dict, key)
    haskey(d, key) || throw(CQLException("Key not found: $key"))
    d[key]
end

"""Accumulate values into sets keyed by their first element."""
function from_list_accum(pairs)
    d = Dict{typeof(first(first(pairs))), Set{typeof(last(first(pairs)))}}()
    for (k, v) in pairs
        if !haskey(d, k)
            d[k] = Set{typeof(v)}()
        end
        push!(d[k], v)
    end
    d
end

"""Merge multiple dictionaries, later values override earlier."""
function merge_dicts(dicts...)
    result = Dict{Any,Any}()
    for d in dicts
        merge!(result, d)
    end
    result
end

"""Format a section with heading and indented body."""
function section_str(heading::String, body::String)
    heading * "\n" * indent_lines(body)
end

"""Indent all lines in a string."""
function indent_lines(s::String)
    join(["    " * line * "\n" for line in split(s, '\n') if !isempty(line)])
end

"""Either type - used for ty+en sort distinction."""
struct Left{T}
    val::T
end

struct Right{T}
    val::T
end

const Either{L,R} = Union{Left{L}, Right{R}}

is_left(::Left) = true
is_left(::Right) = false
is_right(::Left) = false
is_right(::Right) = true

get_left(x::Left) = x.val
get_right(x::Right) = x.val

Base.:(==)(a::Left, b::Left) = a.val == b.val
Base.:(==)(a::Right, b::Right) = a.val == b.val
Base.:(==)(::Left, ::Right) = false
Base.:(==)(::Right, ::Left) = false
Base.hash(x::Left, h::UInt) = hash(x.val, hash(0x4c656674, h))  # "Left" tag
Base.hash(x::Right, h::UInt) = hash(x.val, hash(0x52696768, h))  # "Right" tag
Base.show(io::IO, x::Left) = print(io, "Left(", x.val, ")")
Base.show(io::IO, x::Right) = print(io, "Right(", x.val, ")")
