"""
Lexer / tokenizer for CQL.
"""

# Pre-allocated backtrack exception (avoids string interpolation overhead in try_parse paths)
const _BACKTRACK_EXCEPTION = CQLException("backtrack")

const RESERVED_WORDS = Set([
    "typeside", "schema", "instance", "mapping", "transform", "query", "command",
    "sigma", "delta", "pi", "lambda", "unit", "counit", "eval",
    "entity", "entities", "foreign_keys", "attributes", "path_equations",
    "observation_equations", "generators", "equations", "multi_equations",
    "options", "imports", "types", "constants", "functions",
    "from", "where", "return", "copivot", "distinct",
    "empty", "literal", "identity", "forall", "exists",
    "rename", "remove", "modify", "match",
    "schema_colimit", "quotient", "entity_equations", "getSchema", "getMapping",
    "coproduct", "constraints", "chase",
    "unique", "check",
    "external_types", "external_functions", "external_parsers",
    "html", "md",
])

"""Parser state: tracks position in source string."""
mutable struct ParseState
    source::String
    pos::Int
    line::Int
    col::Int
end

ParseState(s::String) = ParseState(s, 1, 1, 1)

"""Check if we're at end of input."""
at_end(ps::ParseState) = ps.pos > ncodeunits(ps.source)

"""Peek at current character."""
function peek_char(ps::ParseState)::Union{Char, Nothing}
    at_end(ps) ? nothing : ps.source[ps.pos]
end

"""Advance one character (handles multi-byte UTF-8)."""
function advance!(ps::ParseState)
    if !at_end(ps)
        c = ps.source[ps.pos]
        ps.pos = nextind(ps.source, ps.pos)
        if c == '\n'
            ps.line += 1
            ps.col = 1
        else
            ps.col += 1
        end
        c
    else
        nothing
    end
end

"""Skip whitespace and comments."""
function skip_ws!(ps::ParseState)
    while !at_end(ps)
        c = peek_char(ps)
        np = nextind(ps.source, ps.pos)  # next byte position
        if isspace(c)
            advance!(ps)
        elseif c == '/' && np <= ncodeunits(ps.source) && ps.source[np] == '/'
            # Line comment //
            while !at_end(ps) && peek_char(ps) != '\n'
                advance!(ps)
            end
        elseif c == '/' && np <= ncodeunits(ps.source) && ps.source[np] == '*'
            # Block comment /* */
            advance!(ps); advance!(ps)
            while !at_end(ps)
                nc = nextind(ps.source, ps.pos)
                if peek_char(ps) == '*' && nc <= ncodeunits(ps.source) && ps.source[nc] == '/'
                    advance!(ps); advance!(ps)
                    break
                end
                advance!(ps)
            end
        elseif c == '(' && np <= ncodeunits(ps.source) && ps.source[np] == '*'
            # Block comment (* *)
            advance!(ps); advance!(ps)
            while !at_end(ps)
                nc = nextind(ps.source, ps.pos)
                if peek_char(ps) == '*' && nc <= ncodeunits(ps.source) && ps.source[nc] == ')'
                    advance!(ps); advance!(ps)
                    break
                end
                advance!(ps)
            end
        elseif c == '#'
            # Hash line comment (Java CQL style)
            while !at_end(ps) && peek_char(ps) != '\n'
                advance!(ps)
            end
        else
            break
        end
    end
end

"""Check if character is valid in an identifier."""
is_id_char(c::Char) = isletter(c) || isdigit(c) || c == '_' || c == '$'

"""Read an identifier, rejecting reserved words."""
function read_identifier!(ps::ParseState)::String
    skip_ws!(ps)
    start = ps.pos

    c = peek_char(ps)
    c === nothing && backtrack_error()

    if c == '"'
        # Quoted identifier (always allowed, even if content is a keyword)
        advance!(ps)
        buf = IOBuffer()
        while !at_end(ps) && peek_char(ps) != '"'
            write(buf, advance!(ps))
        end
        at_end(ps) && parse_error(ps, "Unterminated quoted identifier")
        advance!(ps)  # skip closing quote
        return String(take!(buf))
    end

    # Allow identifiers starting with letters, underscores, $, or digits (CQL allows numeric names like "50")
    (isletter(c) || c == '_' || c == '$' || isdigit(c)) || backtrack_error()

    while !at_end(ps) && is_id_char(peek_char(ps))
        advance!(ps)
    end

    word = ps.source[start:prevind(ps.source, ps.pos)]
    if word in RESERVED_WORDS
        # Restore position - this is a keyword, not an identifier
        ps.pos = start
        ps.col -= length(word)
        backtrack_error()
    end
    word
end

"""Read any word (including reserved words). Used for option values."""
function read_word!(ps::ParseState)::String
    skip_ws!(ps)
    start = ps.pos

    c = peek_char(ps)
    c === nothing && backtrack_error()

    if c == '"'
        advance!(ps)
        buf = IOBuffer()
        while !at_end(ps) && peek_char(ps) != '"'
            write(buf, advance!(ps))
        end
        at_end(ps) && parse_error(ps, "Unterminated quoted string")
        advance!(ps)
        return String(take!(buf))
    end

    (isletter(c) || c == '_' || c == '$' || isdigit(c)) || backtrack_error()

    while !at_end(ps) && is_id_char(peek_char(ps))
        advance!(ps)
    end

    ps.source[start:prevind(ps.source, ps.pos)]
end

"""Match a specific constant string (keywords are ASCII, so sizeof == length)."""
function expect!(ps::ParseState, s::String)
    skip_ws!(ps)
    slen = sizeof(s)  # byte length (keywords are ASCII)
    if ps.pos + slen - 1 > ncodeunits(ps.source)
        backtrack_error()
    end
    actual = ps.source[ps.pos:ps.pos+slen-1]
    # Check that the match isn't a prefix of a longer identifier
    if actual == s
        next_pos = ps.pos + slen
        if slen > 0 && is_id_char(s[end]) && next_pos <= ncodeunits(ps.source) && is_id_char(ps.source[next_pos])
            backtrack_error()
        end
        ps.pos += slen
        if slen > 0
            ps.col += length(s)
        end
        skip_ws!(ps)
        return s
    end
    backtrack_error()
end

"""Try to match a constant string; return true if matched."""
function try_expect!(ps::ParseState, s::String)::Bool
    skip_ws!(ps)
    slen = sizeof(s)
    if ps.pos + slen - 1 > ncodeunits(ps.source)
        return false
    end
    actual = ps.source[ps.pos:ps.pos+slen-1]
    if actual == s
        next_pos = ps.pos + slen
        if slen > 0 && is_id_char(s[end]) && next_pos <= ncodeunits(ps.source) && is_id_char(ps.source[next_pos])
            return false
        end
        ps.pos += slen
        ps.col += length(s)
        skip_ws!(ps)
        return true
    end
    false
end

"""Check if the next token matches, without consuming."""
function lookahead(ps::ParseState, s::String)::Bool
    skip_ws!(ps)
    slen = sizeof(s)
    if ps.pos + slen - 1 > ncodeunits(ps.source)
        return false
    end
    actual = ps.source[ps.pos:ps.pos+slen-1]
    if actual == s
        next_pos = ps.pos + slen
        if slen > 0 && is_id_char(s[end]) && next_pos <= ncodeunits(ps.source) && is_id_char(ps.source[next_pos])
            return false
        end
        return true
    end
    false
end

"""Raise a parse error with position info."""
function parse_error(ps::ParseState, msg::String)
    context = if ps.pos <= ncodeunits(ps.source)
        endpos = min(nextind(ps.source, ps.pos, 30), ncodeunits(ps.source) + 1) - 1
        # Clamp to valid index
        endpos = thisind(ps.source, endpos)
        ps.source[ps.pos:endpos]
    else
        "<end of input>"
    end
    throw(CQLException("Parse error at line $(ps.line), col $(ps.col): $msg (near: $context)"))
end

"""Lightweight parse error for backtrackable contexts (avoids string interpolation)."""
@inline function backtrack_error()
    throw(_BACKTRACK_EXCEPTION)
end

"""Parse a quoted string literal."""
function read_string!(ps::ParseState)::String
    skip_ws!(ps)
    expect!(ps, "\"")
    buf = IOBuffer()
    while !at_end(ps) && peek_char(ps) != '"'
        c = advance!(ps)
        if c == '\\'
            nc = advance!(ps)
            if nc == 'n'; write(buf, '\n')
            elseif nc == 't'; write(buf, '\t')
            elseif nc == '"'; write(buf, '"')
            elseif nc == '\\'; write(buf, '\\')
            else write(buf, nc)
            end
        else
            write(buf, c)
        end
    end
    at_end(ps) && parse_error(ps, "Unterminated string")
    advance!(ps)  # closing quote
    String(take!(buf))
end

"""Read an integer."""
function read_int!(ps::ParseState)::Int
    skip_ws!(ps)
    start = ps.pos
    if peek_char(ps) == '-'
        advance!(ps)
    end
    while !at_end(ps) && isdigit(peek_char(ps))
        advance!(ps)
    end
    parse(Int, ps.source[start:prevind(ps.source, ps.pos)])
end
