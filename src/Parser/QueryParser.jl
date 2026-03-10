"""
Parser for query declarations.

Grammar:
  query_exp ::= "literal" ":" schema "->" schema { entity_blocks... }
              | "identity" schema
              | identifier
              | "(" query_exp ")"

  entity_block ::= "entity" name "->" "{" from? where? attributes? foreign_keys? "}"
"""

"""Parse a query expression."""
function parse_query_exp!(ps::ParseState)::QueryExp
    skip_ws!(ps)

    # Query composition: [ q1 ; q2 ]
    if lookahead(ps, "[")
        return _parse_query_comp!(ps)
    end

    if lookahead(ps, "literal")
        return QueryRawExp(_parse_query_raw!(ps))
    end

    # simple query shorthand: simple : srcSchema [-> tgtSchema] { ... }
    if lookahead(ps, "simple") && !_is_followed_by_eq_query(ps, "simple")
        expect!(ps, "simple")
        expect!(ps, ":")
        src_ref = parse_schema_exp!(ps)
        # Optional -> tgtSchema
        dst_ref = if try_expect!(ps, "->")
            parse_schema_exp!(ps)
        else
            src_ref  # single-schema form: src = dst
        end
        # Parse simple query body
        raw = parse_braces!(ps, function(ps2)
            _parse_simple_query_body!(ps2, src_ref, dst_ref)
        end)
        return QueryRawExp(raw)
    end

    if try_expect!(ps, "identity")
        sch = parse_schema_exp!(ps)
        return QueryId(sch)
    end

    # toQuery mapping [{ options }] → convert mapping to query
    if lookahead(ps, "toQuery") && !_is_followed_by_eq_query(ps, "toQuery")
        expect!(ps, "toQuery")
        m = parse_mapping_exp!(ps)
        _parse_optional_options_block!(ps)  # consume optional { options ... }
        return QueryToQuery(m)
    end

    # toCoQuery mapping [{ options }] → convert mapping to co-query
    if lookahead(ps, "toCoQuery") && !_is_followed_by_eq_query(ps, "toCoQuery")
        expect!(ps, "toCoQuery")
        m = parse_mapping_exp!(ps)
        _parse_optional_options_block!(ps)  # consume optional { options ... }
        return QueryToCoQuery(m)
    end

    # front constraints index → query
    if lookahead(ps, "front") && !_is_followed_by_eq_query(ps, "front")
        expect!(ps, "front")
        cname = read_identifier!(ps)
        idx = read_int!(ps)
        return QueryFront(cname, idx)
    end

    # back constraints index → query
    if lookahead(ps, "back") && !_is_followed_by_eq_query(ps, "back")
        expect!(ps, "back")
        cname = read_identifier!(ps)
        idx = read_int!(ps)
        return QueryBack(cname, idx)
    end

    # rext q1 q2 → right extension query
    if lookahead(ps, "rext") && !_is_followed_by_eq_query(ps, "rext")
        expect!(ps, "rext")
        q1 = parse_query_exp!(ps)
        q2 = parse_query_exp!(ps)
        return QueryRext(q1, q2)
    end

    # spanify schema → query
    if lookahead(ps, "spanify") && !_is_followed_by_eq_query(ps, "spanify")
        expect!(ps, "spanify")
        sch = parse_schema_exp!(ps)
        return QuerySpanify(sch)
    end

    # spanify_mapping mapping → query
    if lookahead(ps, "spanify_mapping") && !_is_followed_by_eq_query(ps, "spanify_mapping")
        expect!(ps, "spanify_mapping")
        m = parse_mapping_exp!(ps)
        return QuerySpanifyMapping(m)
    end

    # chase constraints query
    if lookahead(ps, "chase") && !_is_followed_by_eq_query(ps, "chase")
        expect!(ps, "chase")
        cname = read_identifier!(ps)
        q = parse_query_exp!(ps)
        return QueryChase(cname, q)
    end

    # reformulate constraints query schema N
    if lookahead(ps, "reformulate") && !_is_followed_by_eq_query(ps, "reformulate")
        expect!(ps, "reformulate")
        cname = read_identifier!(ps)
        q = parse_query_exp!(ps)
        sch = parse_schema_exp!(ps)
        idx = read_int!(ps)
        return QueryReformulate(cname, q, sch, idx)
    end

    # include src_schema tgt_schema → inclusion query
    if lookahead(ps, "include") && !_is_followed_by_eq_query(ps, "include")
        expect!(ps, "include")
        src = parse_schema_exp!(ps)
        tgt = parse_schema_exp!(ps)
        return QueryInclude(src, tgt)
    end

    # fromCoSpan mapping1 mapping2 → query from co-span
    if lookahead(ps, "fromCoSpan") && !_is_followed_by_eq_query(ps, "fromCoSpan")
        expect!(ps, "fromCoSpan")
        m1 = parse_mapping_exp!(ps)
        m2 = parse_mapping_exp!(ps)
        return QueryFromCoSpan(m1, m2)
    end

    # fromConstraints index constraints → query
    if lookahead(ps, "fromConstraints") && !_is_followed_by_eq_query(ps, "fromConstraints")
        expect!(ps, "fromConstraints")
        idx = read_int!(ps)
        cname = read_identifier!(ps)
        return QueryFromConstraints(idx, cname)
    end

    if lookahead(ps, "(")
        return parse_parens!(ps, parse_query_exp!)
    end

    # Variable reference
    name = read_identifier!(ps)
    QueryVar(name)
end

"""Skip arguments for unsupported query operations."""
function _skip_query_args!(ps::ParseState)
    # Read tokens (identifiers, parens, numbers) until we hit something that looks like
    # a new declaration keyword or end of input
    decl_keywords = Set(["typeside", "schema", "instance", "mapping", "transform",
                         "query", "schema_colimit", "constraints", "command"])
    while !at_end(ps)
        skip_ws!(ps)
        at_end(ps) && break
        c = peek_char(ps)
        if c == '('
            # Skip balanced parens
            advance!(ps)
            depth = 1
            while !at_end(ps) && depth > 0
                c2 = peek_char(ps)
                if c2 == '('; depth += 1; end
                if c2 == ')'; depth -= 1; end
                advance!(ps)
            end
        elseif c == '{' || c == '}'
            break
        elseif isdigit(c)
            while !at_end(ps) && isdigit(peek_char(ps))
                advance!(ps)
            end
        else
            # Try to read an identifier; stop if it looks like a declaration
            saved = save_pos(ps)
            r = try_parse(ps, ps2 -> read_identifier!(ps2))
            if r === nothing
                break
            end
            if r in decl_keywords
                restore_pos!(ps, saved)
                break
            end
        end
    end
end

"""Parse query composition: [ q1 ; q2 ]"""
function _parse_query_comp!(ps::ParseState)::QueryComp
    expect!(ps, "[")
    f = parse_query_exp!(ps)
    expect!(ps, ";")
    g = parse_query_exp!(ps)
    expect!(ps, "]")
    QueryComp(f, g)
end

"""Check if a word is followed by '=' (variable assignment, not keyword)."""
function _is_followed_by_eq_query(ps::ParseState, word::String)::Bool
    saved = save_pos(ps)
    try
        expect!(ps, word)
        skip_ws!(ps)
        result = !at_end(ps) && peek_char(ps) == '='
        restore_pos!(ps, saved)
        return result
    catch
        restore_pos!(ps, saved)
        return false
    end
end

"""Parse a simple query body — either entity blocks or flat from/where/attributes."""
function _parse_simple_query_body!(ps::ParseState, src_ref, dst_ref)::QueryExpRaw
    ens = Tuple{String, Tuple{
        Vector{Tuple{String,String}},
        Vector{Tuple{RawTerm,RawTerm}},
        Vector{Tuple{String,RawTerm}},
        Vector{Tuple{String,Vector{Tuple{String,RawTerm}}}}
    }}[]

    # Check if this is a flat form (from/where/attributes without entity blocks)
    if lookahead(ps, "from") || lookahead(ps, "where") || lookahead(ps, "attributes")
        # Flat form: single implicit entity
        en_block = _parse_query_entity_body!(ps)
        push!(ens, ("__simple__", en_block))
    else
        # Entity block form
        while try_expect!(ps, "entity")
            en_name = read_identifier!(ps)
            expect!(ps, "->")
            en_block = parse_braces!(ps, _parse_query_entity_body!)
            push!(ens, (en_name, en_block))
        end
    end

    options = parse_optional_section!(ps, "options", parse_option!)

    QueryExpRaw(src_ref, dst_ref, ens, Tuple{String,String}[o for o in options], Any[])
end

"""Parse the body of a query entity block: from, where, attributes, foreign_keys."""
function _parse_query_entity_body!(ps::ParseState)
    from_bindings = Tuple{String,String}[]
    if try_expect!(ps, "from")
        while true
            r = try_parse(ps, function(ps4)
                _parse_gen_decl!(ps4)
            end)
            r === nothing && break
            append!(from_bindings, r)
        end
    end

    where_eqs = Tuple{RawTerm,RawTerm}[]
    if try_expect!(ps, "where")
        while true
            r = try_parse(ps, parse_equation!)
            r === nothing && break
            push!(where_eqs, r)
        end
    end

    att_mappings = Tuple{String,RawTerm}[]
    if try_expect!(ps, "attributes") || try_expect!(ps, "return")
        # Handle optional '*' wildcard (include all default attributes)
        skip_ws!(ps)
        if !at_end(ps) && peek_char(ps) == '*'
            advance!(ps)  # consume '*'
        end
        while true
            r = try_parse(ps, function(ps4)
                _parse_query_att_mapping!(ps4)
            end)
            r === nothing && break
            push!(att_mappings, r)
        end
    end

    fk_mappings = Tuple{String,Vector{Tuple{String,RawTerm}}}[]
    if try_expect!(ps, "foreign_keys")
        while true
            r = try_parse(ps, function(ps4)
                fk_name = read_identifier!(ps4)
                expect!(ps4, "->")
                fk_body = parse_braces!(ps4, function(ps5)
                    mappings = Tuple{String,RawTerm}[]
                    while true
                        m = try_parse(ps5, _parse_gen_mapping!)
                        m === nothing && break
                        push!(mappings, m)
                    end
                    parse_optional_section!(ps5, "options", parse_option!)
                    mappings
                end)
                (fk_name, fk_body)
            end)
            r === nothing && break
            push!(fk_mappings, r)
        end
    end

    (from_bindings, where_eqs, att_mappings, fk_mappings)
end

"""Parse a raw query: literal : srcSchema -> tgtSchema { entity blocks... }"""
function _parse_query_raw!(ps::ParseState)::QueryExpRaw
    expect!(ps, "literal")
    expect!(ps, ":")
    src_ref = parse_schema_exp!(ps)
    expect!(ps, "->")
    dst_ref = parse_schema_exp!(ps)

    parse_braces!(ps, function(ps2)
        imports = parse_optional_section!(ps2, "imports", parse_query_exp!)

        ens = Tuple{String, Tuple{
            Vector{Tuple{String,String}},
            Vector{Tuple{RawTerm,RawTerm}},
            Vector{Tuple{String,RawTerm}},
            Vector{Tuple{String,Vector{Tuple{String,RawTerm}}}}
        }}[]

        while try_expect!(ps2, "entity")
            en_name = read_identifier!(ps2)
            expect!(ps2, "->")

            en_block = parse_braces!(ps2, function(ps3)
                # from clause
                from_bindings = Tuple{String,String}[]
                if try_expect!(ps3, "from")
                    while true
                        r = try_parse(ps3, function(ps4)
                            _parse_gen_decl!(ps4)
                        end)
                        r === nothing && break
                        append!(from_bindings, r)
                    end
                end

                # where clause
                where_eqs = Tuple{RawTerm,RawTerm}[]
                if try_expect!(ps3, "where")
                    while true
                        r = try_parse(ps3, parse_equation!)
                        r === nothing && break
                        push!(where_eqs, r)
                    end
                end

                # attributes inside entity block
                att_mappings = Tuple{String,RawTerm}[]
                if try_expect!(ps3, "attributes")
                    # Handle optional '*' wildcard
                    skip_ws!(ps3)
                    if !at_end(ps3) && peek_char(ps3) == '*'
                        advance!(ps3)
                    end
                    while true
                        r = try_parse(ps3, _parse_query_att_mapping!)
                        r === nothing && break
                        push!(att_mappings, r)
                    end
                end

                # foreign_keys inside entity block
                fk_mappings = Tuple{String,Vector{Tuple{String,RawTerm}}}[]
                if try_expect!(ps3, "foreign_keys")
                    while true
                        r = try_parse(ps3, function(ps4)
                            fk_name = read_identifier!(ps4)
                            expect!(ps4, "->")
                            fk_body = parse_braces!(ps4, function(ps5)
                                mappings = Tuple{String,RawTerm}[]
                                while true
                                    m = try_parse(ps5, _parse_gen_mapping!)
                                    m === nothing && break
                                    push!(mappings, m)
                                end
                                # consume optional "options" section (ignored)
                                parse_optional_section!(ps5, "options", parse_option!)
                                mappings
                            end)
                            (fk_name, fk_body)
                        end)
                        r === nothing && break
                        push!(fk_mappings, r)
                    end
                end

                (from_bindings, where_eqs, att_mappings, fk_mappings)
            end)

            push!(ens, (en_name, en_block))
        end

        options = parse_optional_section!(ps2, "options", parse_option!)

        QueryExpRaw(
            src_ref,
            dst_ref,
            ens,
            Tuple{String,String}[o for o in options],
            imports,
        )
    end)
end

"""Parse a query attribute mapping: name -> term  OR  name -> from ... where ... return ... [aggregate ...]"""
function _parse_query_att_mapping!(ps::ParseState)::Tuple{String,RawTerm}
    name = read_identifier!(ps)
    expect!(ps, "->")
    skip_ws!(ps)

    # Check for sub-query attribute (from ... where ... return ... aggregate ...)
    if lookahead(ps, "from")
        expect!(ps, "from")
        # Parse from bindings and encode as RawTerm list
        from_parts = RawTerm[]
        while true
            r = try_parse(ps, _parse_gen_decl!)
            r === nothing && break
            for (v, e) in r
                push!(from_parts, RawTerm(v * ":" * e, RawTerm[]))
            end
        end
        # Parse where clause and encode as pairs of RawTerms
        where_parts = RawTerm[]
        if try_expect!(ps, "where")
            while true
                r = try_parse(ps, parse_equation!)
                r === nothing && break
                (lhs, rhs) = r
                push!(where_parts, lhs)
                push!(where_parts, rhs)
            end
        end
        # Parse return term
        local ret_term = RawTerm("__unit__", RawTerm[])
        if try_expect!(ps, "return")
            ret_term = parse_raw_term!(ps)
        end
        # Parse aggregate clause (optional)
        if try_expect!(ps, "aggregate")
            zero_term = parse_raw_term!(ps)
            if try_expect!(ps, "lambda")
                arg1 = read_identifier!(ps)
                arg2 = read_identifier!(ps)
                expect!(ps, ".")
                body_term = parse_raw_term!(ps)
                # Encode full aggregation as a structured RawTerm
                agg_term = RawTerm("__agg__", [
                    RawTerm("__from__", from_parts),
                    RawTerm("__where__", where_parts),
                    ret_term,
                    zero_term,
                    RawTerm("__lambda__", [RawTerm(arg1, []), RawTerm(arg2, [])]),
                    body_term
                ])
                return (name, agg_term)
            end
        end
        return (name, ret_term)
    end

    # Simple form: name -> term
    term = parse_raw_term!(ps)
    (name, term)
end
