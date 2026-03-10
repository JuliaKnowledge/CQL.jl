"""
Parser for transform declarations.

Grammar:
  transform_exp ::= "literal" ":" instance "->" instance { generators ... }
                   | "identity" instance
                   | "sigma" mapping transform [{ options }]
                   | "delta" mapping transform [{ options }]
                   | "[" transform ";" transform "]"
                   | identifier
                   | "(" transform_exp ")"
"""

"""Parse a transform expression."""
function parse_transform_exp!(ps::ParseState)::TransformExp
    skip_ws!(ps)

    # Composition: [ t1 ; t2 ]
    if lookahead(ps, "[")
        return _parse_transform_comp!(ps)
    end

    if lookahead(ps, "literal")
        return _parse_transform_raw!(ps)
    end

    if try_expect!(ps, "identity")
        inst = parse_instance_exp!(ps)
        return TransformId(inst)
    end

    if try_expect!(ps, "sigma")
        m = parse_mapping_exp!(ps)
        t = parse_transform_exp!(ps)
        opts = _parse_optional_options_block!(ps)
        _parse_optional_options_block!(ps)  # consume optional second { options ... }
        return TransformSigmaExp(m, t, opts)
    end

    if try_expect!(ps, "delta")
        m = parse_mapping_exp!(ps)
        t = parse_transform_exp!(ps)
        opts = _parse_optional_options_block!(ps)
        return TransformDeltaExp(m, t, opts)
    end

    if try_expect!(ps, "unit")
        m = parse_mapping_exp!(ps)
        i = parse_instance_exp!(ps)
        opts = _parse_optional_options_block!(ps)
        return TransformUnit(m, i, opts)
    end

    if try_expect!(ps, "counit")
        m = parse_mapping_exp!(ps)
        i = parse_instance_exp!(ps)
        opts = _parse_optional_options_block!(ps)
        return TransformCounit(m, i, opts)
    end

    if try_expect!(ps, "eval")
        q = parse_query_exp!(ps)
        t = parse_transform_exp!(ps)
        _parse_optional_options_block!(ps)  # consume optional { options ... }
        return TransformEval(q, t)
    end

    # coeval (not reserved, use lookahead) — can have TWO optional { options } blocks
    if lookahead(ps, "coeval") && !_is_followed_by_eq_transform(ps, "coeval")
        expect!(ps, "coeval")
        q = parse_query_exp!(ps)
        t = parse_transform_exp!(ps)
        _parse_optional_options_block!(ps)  # consume optional first { options ... }
        _parse_optional_options_block!(ps)  # consume optional second { options ... }
        return TransformCoeval(q, t)
    end

    # counit_query Q I [{ options }]
    if lookahead(ps, "counit_query") && !_is_followed_by_eq_transform(ps, "counit_query")
        expect!(ps, "counit_query")
        q = parse_query_exp!(ps)
        i = parse_instance_exp!(ps)
        opts = _parse_optional_options_block!(ps)
        return TransformCounitQuery(q, i, opts)
    end

    # unit_query Q I [{ options }]
    if lookahead(ps, "unit_query") && !_is_followed_by_eq_transform(ps, "unit_query")
        expect!(ps, "unit_query")
        q = parse_query_exp!(ps)
        i = parse_instance_exp!(ps)
        opts = _parse_optional_options_block!(ps)
        return TransformUnitQuery(q, i, opts)
    end

    # frozen Q lambda var:type. body : rettype  (transform form)
    if lookahead(ps, "frozen") && !_is_followed_by_eq_transform(ps, "frozen")
        expect!(ps, "frozen")
        q = parse_query_exp!(ps)
        expect!(ps, "lambda")
        var_name = read_identifier!(ps)
        expect!(ps, ":")
        var_type = read_identifier!(ps)
        expect!(ps, ".")
        body = parse_raw_term!(ps)
        expect!(ps, ":")
        ret_type = read_identifier!(ps)
        return TransformFrozen(q, var_name, var_type, body, ret_type)
    end

    # except transform instance
    if lookahead(ps, "except") && !_is_followed_by_eq_transform(ps, "except")
        expect!(ps, "except")
        t = parse_transform_exp!(ps)
        i = parse_instance_exp!(ps)
        return TransformExcept(t, i)
    end

    # except_return inst1 inst2
    if lookahead(ps, "except_return") && !_is_followed_by_eq_transform(ps, "except_return")
        expect!(ps, "except_return")
        i1 = parse_instance_exp!(ps)
        i2 = parse_instance_exp!(ps)
        return TransformExceptReturn(i1, i2)
    end

    # include inst1 inst2 (transform form)
    if lookahead(ps, "include") && !_is_followed_by_eq_transform(ps, "include")
        expect!(ps, "include")
        i1 = parse_instance_exp!(ps)
        i2 = parse_instance_exp!(ps)
        return TransformInclude(i1, i2)
    end

    # distinct_return instance
    if lookahead(ps, "distinct_return") && !_is_followed_by_eq_transform(ps, "distinct_return")
        expect!(ps, "distinct_return")
        i = parse_instance_exp!(ps)
        return TransformDistinctReturn(i)
    end

    # distinct transform (transform form — must come after distinct_return)
    if lookahead(ps, "distinct") && !_is_followed_by_eq_transform(ps, "distinct")
        expect!(ps, "distinct")
        t = parse_transform_exp!(ps)
        return TransformDistinctTransform(t)
    end

    # pi mapping transform [{ options }] [{ options }] — can have TWO optional options blocks
    if lookahead(ps, "pi") && !_is_followed_by_eq_transform(ps, "pi")
        expect!(ps, "pi")
        m = parse_mapping_exp!(ps)
        t = parse_transform_exp!(ps)
        opts = _parse_optional_options_block!(ps)
        _parse_optional_options_block!(ps)  # consume optional second { options ... }
        return TransformPi(m, t, opts)
    end

    if lookahead(ps, "(")
        return parse_parens!(ps, parse_transform_exp!)
    end

    # Variable reference
    name = read_identifier!(ps)
    TransformVar(name)
end

"""Parse transform composition: [ t1 ; t2 ]"""
function _parse_transform_comp!(ps::ParseState)::TransformComp
    expect!(ps, "[")
    f = parse_transform_exp!(ps)
    expect!(ps, ";")
    g = parse_transform_exp!(ps)
    expect!(ps, "]")
    TransformComp(f, g)
end

"""Parse a raw transform: literal : src_inst -> dst_inst { generators ... options ... }"""
function _parse_transform_raw!(ps::ParseState)
    expect!(ps, "literal")
    expect!(ps, ":")
    src_ref = parse_instance_exp!(ps)
    expect!(ps, "->")
    dst_ref = parse_instance_exp!(ps)

    parse_braces!(ps, function(ps2)
        imports = parse_optional_section!(ps2, "imports", parse_transform_exp!)

        gens = parse_optional_section!(ps2, "generators", _parse_gen_mapping!)

        options = parse_optional_section!(ps2, "options", parse_option!)

        TransformRawExp(
            src_ref,
            dst_ref,
            Tuple{String,RawTerm}[g for g in gens],
            Tuple{String,String}[o for o in options],
            imports,
        )
    end)
end

"""Check if a word is followed by '=' (variable assignment, not keyword)."""
function _is_followed_by_eq_transform(ps::ParseState, word::String)::Bool
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

"""Parse a generator mapping: gen -> term"""
function _parse_gen_mapping!(ps::ParseState)::Tuple{String,RawTerm}
    name = read_identifier!(ps)
    expect!(ps, "->")
    term = parse_raw_term!(ps)
    (name, term)
end
