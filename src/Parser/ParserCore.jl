"""
Core parsing utilities: raw term parsing, option parsing, combinators.
"""

"""Save the current parser position for backtracking."""
function save_pos(ps::ParseState)
    (ps.pos, ps.line, ps.col)
end

"""Restore a previously saved parser position."""
function restore_pos!(ps::ParseState, saved::Tuple{Int,Int,Int})
    ps.pos, ps.line, ps.col = saved
end

"""Try to run a parser; if it fails, backtrack to the saved position."""
function try_parse(ps::ParseState, parser)
    saved = save_pos(ps)
    try
        return parser(ps)
    catch e
        e isa CQLException || rethrow(e)
        restore_pos!(ps, saved)
        return nothing
    end
end

"""Parse zero or more items using the given parser function."""
function parse_many!(ps::ParseState, parser)
    results = []
    while true
        r = try_parse(ps, parser)
        r === nothing && break
        push!(results, r)
    end
    results
end

"""Parse one or more items."""
function parse_some!(ps::ParseState, parser)
    first = parser(ps)
    rest = parse_many!(ps, parser)
    pushfirst!(rest, first)
    rest
end

"""Parse items separated by a delimiter string."""
function parse_sep_by!(ps::ParseState, parser, sep::String)
    results = []
    r = try_parse(ps, parser)
    r === nothing && return results
    push!(results, r)
    while try_expect!(ps, sep)
        push!(results, parser(ps))
    end
    results
end

"""Parse items separated by a delimiter, requiring at least one."""
function parse_sep_by1!(ps::ParseState, parser, sep::String)
    results = parse_sep_by!(ps, parser, sep)
    isempty(results) && parse_error(ps, "Expected at least one item")
    results
end

"""Parse content within braces { ... }."""
function parse_braces!(ps::ParseState, parser)
    expect!(ps, "{")
    result = parser(ps)
    expect!(ps, "}")
    result
end

"""Parse content within parentheses ( ... )."""
function parse_parens!(ps::ParseState, parser)
    expect!(ps, "(")
    result = parser(ps)
    expect!(ps, ")")
    result
end

# ============================================================================
# Raw term parsing
# ============================================================================

"""
Parse a raw CQL term.

Handles:
- Function application: f(a1, a2, ...)
- Dot notation: a.b.c  => b(a) then c(b(a))
- Simple identifiers: x
- Infix in parens: (a f b)
- Type annotations: term@Type
- Literals: true, false
- Decimal numbers: 500.1
"""
function parse_raw_term!(ps::ParseState)::RawTerm
    skip_ws!(ps)
    c = peek_char(ps)
    if c == '('
        r = try_parse(ps, _parse_infix_term!)
        r !== nothing && return _maybe_type_annotation!(ps, r)
    end
    if c !== nothing && (c == '-' || isdigit(c))
        r = try_parse(ps, _parse_decimal_literal!)
        r !== nothing && return _maybe_type_annotation!(ps, r)
    end

    # Read identifier once, then branch on what follows (avoids 2 redundant reads + backtracking)
    id = try_parse(ps, read_identifier!)
    if id !== nothing
        pos_after_id = save_pos(ps)
        skip_ws!(ps)
        nc = at_end(ps) ? nothing : peek_char(ps)
        if nc == '('
            # Might be function application — wrap in try_parse since ( may start next expression
            r = try_parse(ps, function(ps2)
                expect!(ps2, "(")
                args = parse_sep_by!(ps2, parse_raw_term!, ",")
                expect!(ps2, ")")
                RawTerm(id, RawTerm[a for a in args])
            end)
            if r !== nothing
                return _maybe_type_annotation!(ps, r)
            end
            restore_pos!(ps, pos_after_id)
            return _maybe_type_annotation!(ps, RawTerm(id, RawTerm[]))
        elseif nc == '.'
            ids = String[id]
            while try_expect!(ps, ".")
                push!(ids, read_identifier!(ps))
            end
            if length(ids) >= 2
                result = RawTerm(ids[1], RawTerm[])
                for i in 2:length(ids)
                    result = RawTerm(ids[i], RawTerm[result])
                end
                return _maybe_type_annotation!(ps, result)
            end
            restore_pos!(ps, pos_after_id)
            return _maybe_type_annotation!(ps, RawTerm(id, RawTerm[]))
        else
            return _maybe_type_annotation!(ps, RawTerm(id, RawTerm[]))
        end
    end

    for kw in ("true", "false", "import_csv", "import_jdbc",
               "export_csv_instance", "export_jdbc_instance")
        if try_expect!(ps, kw)
            return _maybe_type_annotation!(ps, RawTerm(kw, RawTerm[]))
        end
    end

    parse_error(ps, "Expected term")
end

"""Check for @Type annotation after a term (no whitespace between term and @)."""
function _maybe_type_annotation!(ps::ParseState, term::RawTerm)::RawTerm
    if !at_end(ps) && peek_char(ps) == '@'
        advance!(ps)  # consume @
        type_name = read_word!(ps)  # allow reserved words as type names
        return RawTerm("@" * type_name, RawTerm[term])
    end
    term
end

"""Parse a decimal literal: digits.digits (e.g., 500.1, 3.14)."""
function _parse_decimal_literal!(ps::ParseState)::RawTerm
    skip_ws!(ps)
    start = ps.pos
    c = peek_char(ps)
    # Optional negative sign
    if c == '-'
        advance!(ps)
        c = peek_char(ps)
    end
    (c !== nothing && isdigit(c)) || backtrack_error()
    while !at_end(ps) && isdigit(peek_char(ps))
        advance!(ps)
    end
    # Must have .digit (not just . which could be path separator)
    at_end(ps) && backtrack_error()
    peek_char(ps) == '.' || backtrack_error()
    np = nextind(ps.source, ps.pos)
    (np <= ncodeunits(ps.source) && isdigit(ps.source[np])) || backtrack_error()
    advance!(ps)  # consume .
    while !at_end(ps) && isdigit(peek_char(ps))
        advance!(ps)
    end
    word = ps.source[start:prevind(ps.source, ps.pos)]
    RawTerm(word, RawTerm[])
end

function _parse_func_app!(ps::ParseState)::RawTerm
    skip_ws!(ps)
    id = read_identifier!(ps)
    skip_ws!(ps)
    # Must be followed by '('
    peek_char(ps) == '(' || backtrack_error()
    expect!(ps, "(")
    args = parse_sep_by!(ps, parse_raw_term!, ",")
    expect!(ps, ")")
    RawTerm(id, RawTerm[a for a in args])
end

function _parse_dot_term!(ps::ParseState)::RawTerm
    skip_ws!(ps)
    ids = parse_sep_by1!(ps, ps2 -> read_identifier!(ps2), ".")
    length(ids) < 2 && backtrack_error()
    # a.b.c => c(b(a)) ... but per Haskell: foldl (\y x -> RawApp x [y]) (RawApp (head t) []) (tail t)
    result = RawTerm(ids[1], RawTerm[])
    for i in 2:length(ids)
        result = RawTerm(ids[i], RawTerm[result])
    end
    result
end

function _parse_infix_term!(ps::ParseState)::RawTerm
    expect!(ps, "(")
    a = parse_raw_term!(ps)
    f = read_identifier!(ps)
    b = parse_raw_term!(ps)
    expect!(ps, ")")
    RawTerm(f, RawTerm[a, b])
end

# ============================================================================
# Option parsing
# ============================================================================

"""Parse a key = value option pair. Values can be keywords like true/false."""
function parse_option!(ps::ParseState)::Tuple{String,String}
    k = read_word!(ps)
    expect!(ps, "=")
    v = read_word!(ps)
    (k, v)
end

"""Parse an optional section: if keyword matches, parse body; else return empty."""
function parse_optional_section!(ps::ParseState, keyword::String, parser)
    if try_expect!(ps, keyword)
        return parse_many!(ps, parser)
    end
    return []
end

# ============================================================================
# Common declaration parsers
# ============================================================================

"""Parse a typed declaration: name1 name2 ... : type"""
function parse_typed_decl!(ps::ParseState)::Vector{Tuple{String, String}}
    names = parse_some!(ps, ps2 -> read_identifier!(ps2))
    expect!(ps, ":")
    ty = read_identifier!(ps)
    [(n, ty) for n in names]
end

"""Parse a function declaration: name1 ... : type1, type2, ... -> retType"""
function parse_func_decl!(ps::ParseState)::Vector{Tuple{String, Tuple{Vector{String}, String}}}
    names = parse_some!(ps, ps2 -> read_identifier!(ps2))
    expect!(ps, ":")
    # Could be constant (no args, just : type) or function (args -> ret)
    # Try to detect -> by parsing identifiers separated by commas, then ->
    first_id = read_identifier!(ps)
    if try_expect!(ps, "->")
        # constant form with args: first_id -> retType
        ret = read_identifier!(ps)
        return [(n, ([first_id], ret)) for n in names]
    elseif try_expect!(ps, ",")
        # Multiple argument types
        arg_types = String[first_id]
        push!(arg_types, read_identifier!(ps))
        while try_expect!(ps, ",")
            push!(arg_types, read_identifier!(ps))
        end
        expect!(ps, "->")
        ret = read_identifier!(ps)
        return [(n, (arg_types, ret)) for n in names]
    else
        # Constant: name : type (no args)
        return [(n, (String[], first_id)) for n in names]
    end
end

"""Parse a FK or attribute declaration: name1 name2 ... : src -> tgt"""
function parse_arrow_decl!(ps::ParseState)::Vector{Tuple{String, Tuple{String, String}}}
    names = parse_some!(ps, ps2 -> read_identifier!(ps2))
    expect!(ps, ":")
    src = read_identifier!(ps)
    expect!(ps, "->")
    tgt = read_identifier!(ps)
    [(n, (src, tgt)) for n in names]
end

"""Parse variable bindings for forall: var1 var2 : type, var3, ..."""
function parse_var_bindings!(ps::ParseState)::Vector{Tuple{String, Union{Nothing, String}}}
    result = Tuple{String, Union{Nothing, String}}[]
    vars = parse_some!(ps, ps2 -> read_identifier!(ps2))
    ty = if try_expect!(ps, ":")
        read_identifier!(ps)
    else
        nothing
    end
    for v in vars
        push!(result, (v, ty))
    end
    result
end

"""Parse a typeside equation: [forall var1:type1, var2 . ] term = term"""
function parse_ts_equation!(ps::ParseState)::Tuple{Vector{Tuple{String, Union{Nothing,String}}}, RawTerm, RawTerm}
    ctx = if try_expect!(ps, "forall")
        bindings = parse_sep_by1!(ps, parse_var_bindings!, ",")
        all_bindings = reduce(vcat, bindings)
        expect!(ps, ".")
        all_bindings
    else
        Tuple{String, Union{Nothing,String}}[]
    end
    lhs = parse_raw_term!(ps)
    expect!(ps, "=")
    rhs = parse_raw_term!(ps)
    (ctx, lhs, rhs)
end

"""Parse a simple equation: term = term"""
function parse_equation!(ps::ParseState)::Tuple{RawTerm, RawTerm}
    lhs = parse_raw_term!(ps)
    expect!(ps, "=")
    rhs = parse_raw_term!(ps)
    (lhs, rhs)
end
