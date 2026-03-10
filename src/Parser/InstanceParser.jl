"""
Parser for instance declarations.

Grammar:
  instance_exp ::= "literal" ":" schema { ... }
                 | "empty" ":" schema
                 | "sigma" mapping instance [{ options }]
                 | "delta" mapping instance [{ options }]
                 | "eval" query instance
                 | "pivot" instance
                 | identifier
                 | "(" instance_exp ")"
"""

"""Parse an instance expression."""
function parse_instance_exp!(ps::ParseState)::InstanceExp
    skip_ws!(ps)

    if lookahead(ps, "literal")
        return InstanceRawExp(_parse_instance_raw!(ps))
    end

    if try_expect!(ps, "empty")
        expect!(ps, ":")
        sch = parse_schema_exp!(ps)
        return InstanceInitial(sch)
    end

    if try_expect!(ps, "sigma_chase")
        m = parse_mapping_exp!(ps)
        i = parse_instance_exp!(ps)
        opts = _parse_optional_options_block!(ps)
        return InstanceSigma(m, i, opts)  # treat sigma_chase as sigma
    end

    if try_expect!(ps, "sigma")
        m = parse_mapping_exp!(ps)
        i = parse_instance_exp!(ps)
        opts = _parse_optional_options_block!(ps)
        return InstanceSigma(m, i, opts)
    end

    if try_expect!(ps, "delta")
        m = parse_mapping_exp!(ps)
        i = parse_instance_exp!(ps)
        opts = _parse_optional_options_block!(ps)
        return InstanceDelta(m, i, opts)
    end

    if try_expect!(ps, "eval")
        q = parse_query_exp!(ps)
        i = parse_instance_exp!(ps)
        _parse_optional_options_block!(ps)  # consume optional { options ... }
        return InstanceEval(q, i)
    end

    if try_expect!(ps, "coproduct")
        instances = InstanceExp[]
        push!(instances, parse_instance_exp!(ps))
        while try_expect!(ps, "+")
            push!(instances, parse_instance_exp!(ps))
        end
        expect!(ps, ":")
        sch = parse_schema_exp!(ps)
        _parse_optional_options_block!(ps)  # consume optional { options ... }
        return InstanceCoproduct(instances, sch)
    end

    if try_expect!(ps, "chase")
        # Try inline constraints expression first (literal : schema { ... })
        c = try_parse(ps, parse_constraints_exp!)
        if c !== nothing
            i = parse_instance_exp!(ps)
            opts = _parse_optional_options_block!(ps)
            return InstanceChase(c, i, opts)
        end
        # Fall back to reading a constraints name reference
        cname = read_identifier!(ps)
        i = parse_instance_exp!(ps)
        opts = _parse_optional_options_block!(ps)
        return InstanceChase(cname, i, opts)
    end

    # coeval Q I [{ options }] — co-evaluation of a query (not reserved)
    if lookahead(ps, "coeval") && !_is_followed_by_eq(ps, "coeval")
        expect!(ps, "coeval")
        q = parse_query_exp!(ps)
        i = parse_instance_exp!(ps)
        _parse_optional_options_block!(ps)  # consume optional { options ... }
        return InstanceCoeval(q, i)
    end

    # pivot instance (not reserved, use lookahead for non-reserved keywords)
    if lookahead(ps, "pivot") && !_is_followed_by_eq(ps, "pivot")
        expect!(ps, "pivot")
        i = parse_instance_exp!(ps)
        return InstancePivot(i)
    end

    # import_csv "path" : schema (not reserved)
    if lookahead(ps, "import_csv") && !_is_followed_by_eq(ps, "import_csv")
        expect!(ps, "import_csv")
        path = read_word!(ps)
        expect!(ps, ":")
        sch = parse_schema_exp!(ps)
        return InstanceImportCsv(path, sch)
    end

    # import_jdbc "conn" : schema [{ entity -> "SQL" ... options ... }]
    if lookahead(ps, "import_jdbc") && !_is_followed_by_eq(ps, "import_jdbc")
        expect!(ps, "import_jdbc")
        conn = read_word!(ps)
        expect!(ps, ":")
        sch = parse_schema_exp!(ps)
        entity_sql = Tuple{String,String}[]
        import_opts = Tuple{String,String}[]
        skip_ws!(ps)
        if !at_end(ps) && peek_char(ps) == '{'
            parse_braces!(ps, function(ps2)
                while !at_end(ps2)
                    skip_ws!(ps2)
                    at_end(ps2) && break
                    c = peek_char(ps2)
                    c == '}' && break
                    if c == '"'
                        read_string!(ps2)
                    else
                        r = try_parse(ps2, function(ps3)
                            if try_expect!(ps3, "options")
                                append!(import_opts, parse_many!(ps3, parse_option!))
                                return true
                            end
                            n = read_identifier!(ps3)
                            if try_expect!(ps3, "->")
                                sql = read_string!(ps3)
                                push!(entity_sql, (n, sql))
                            end
                            true
                        end)
                        r === nothing && break
                    end
                end
            end)
        end
        return InstanceImportJdbc(conn, sch, entity_sql, import_opts)
    end

    # random : schema { generators entity -> count ... }
    if lookahead(ps, "random") && !_is_followed_by_eq(ps, "random")
        expect!(ps, "random")
        expect!(ps, ":")
        sch = parse_schema_exp!(ps)
        gen_counts = Tuple{String,Int}[]
        opts = Tuple{String,String}[]
        if lookahead(ps, "{")
            parse_braces!(ps, function(ps2)
                gen_entries = parse_optional_section!(ps2, "generators", _parse_gen_count!)
                append!(gen_counts, gen_entries)
                append!(opts, parse_optional_section!(ps2, "options", parse_option!))
            end)
        end
        return InstanceRandom(sch, gen_counts, opts)
    end

    # sigma_chase (non-reserved keyword)
    if lookahead(ps, "sigma_chase") && !_is_followed_by_eq(ps, "sigma_chase")
        expect!(ps, "sigma_chase")
        m = parse_mapping_exp!(ps)
        i = parse_instance_exp!(ps)
        opts = _parse_optional_options_block!(ps)
        return InstanceSigma(m, i, opts)
    end

    # distinct instance
    if try_expect!(ps, "distinct")
        i = parse_instance_exp!(ps)
        return InstanceDistinct(i)
    end

    # coequalize t1 t2 [{ options }]
    if lookahead(ps, "coequalize") && !_is_followed_by_eq(ps, "coequalize")
        expect!(ps, "coequalize")
        t1 = parse_transform_exp!(ps)
        t2 = parse_transform_exp!(ps)
        _parse_optional_options_block!(ps)  # consume optional { options ... }
        return InstanceCoequalize(t1, t2)
    end

    # colimit graph_name schema { nodes ... edges ... }
    if lookahead(ps, "colimit") && !_is_followed_by_eq(ps, "colimit")
        expect!(ps, "colimit")
        graph_name = read_identifier!(ps)
        sch = parse_schema_exp!(ps)
        node_map = Tuple{String,Any}[]
        edge_map = Tuple{String,Any}[]
        opts = Tuple{String,String}[]
        parse_braces!(ps, function(ps2)
            if try_expect!(ps2, "nodes")
                while true
                    r = try_parse(ps2, function(ps3)
                        node_name = read_identifier!(ps3)
                        expect!(ps3, "->")
                        inst_exp = parse_instance_exp!(ps3)
                        (node_name, inst_exp)
                    end)
                    r === nothing && break
                    push!(node_map, r)
                end
            end
            if try_expect!(ps2, "edges")
                while true
                    r = try_parse(ps2, function(ps3)
                        edge_name = read_identifier!(ps3)
                        expect!(ps3, "->")
                        tr_exp = parse_transform_exp!(ps3)
                        (edge_name, tr_exp)
                    end)
                    r === nothing && break
                    push!(edge_map, r)
                end
            end
            opts_section = parse_optional_section!(ps2, "options", parse_option!)
            append!(opts, opts_section)
        end)
        return InstanceColimit(graph_name, sch, node_map, edge_map, opts)
    end

    # import_jdbc_direct conn rowid : schema
    if lookahead(ps, "import_jdbc_direct") && !_is_followed_by_eq(ps, "import_jdbc_direct")
        expect!(ps, "import_jdbc_direct")
        conn = read_word!(ps)
        rowid = read_word!(ps)
        expect!(ps, ":")
        sch = parse_schema_exp!(ps)
        return InstanceImportJdbcDirect(conn, rowid, sch)
    end

    # import_odbc "conn" : schema [{ entity -> "SQL" ... options ... }]
    if lookahead(ps, "import_odbc") && !_is_followed_by_eq(ps, "import_odbc")
        expect!(ps, "import_odbc")
        conn = read_word!(ps)
        expect!(ps, ":")
        sch = parse_schema_exp!(ps)
        entity_sql = Tuple{String,String}[]
        import_opts = Tuple{String,String}[]
        skip_ws!(ps)
        if !at_end(ps) && peek_char(ps) == '{'
            parse_braces!(ps, function(ps2)
                while !at_end(ps2)
                    skip_ws!(ps2)
                    at_end(ps2) && break
                    c = peek_char(ps2)
                    c == '}' && break
                    if c == '"'
                        read_string!(ps2)
                    else
                        r = try_parse(ps2, function(ps3)
                            if try_expect!(ps3, "options")
                                append!(import_opts, parse_many!(ps3, parse_option!))
                                return true
                            end
                            n = read_identifier!(ps3)
                            if try_expect!(ps3, "->")
                                sql = read_string!(ps3)
                                push!(entity_sql, (n, sql))
                            end
                            true
                        end)
                        r === nothing && break
                    end
                end
            end)
        end
        return InstanceImportOdbc(conn, sch, entity_sql, import_opts)
    end

    # import_odbc_direct conn rowid : schema
    if lookahead(ps, "import_odbc_direct") && !_is_followed_by_eq(ps, "import_odbc_direct")
        expect!(ps, "import_odbc_direct")
        conn = read_word!(ps)
        rowid = read_word!(ps)
        expect!(ps, ":")
        sch = parse_schema_exp!(ps)
        return InstanceImportOdbcDirect(conn, rowid, sch)
    end

    # import_json_ld_all "path"
    if lookahead(ps, "import_json_ld_all") && !_is_followed_by_eq(ps, "import_json_ld_all")
        expect!(ps, "import_json_ld_all")
        path = read_word!(ps)
        return InstanceImportJsonLd(path)
    end

    # import_rdf_all "path"
    if lookahead(ps, "import_rdf_all") && !_is_followed_by_eq(ps, "import_rdf_all")
        expect!(ps, "import_rdf_all")
        path = read_word!(ps)
        return InstanceImportRdf(path)
    end

    # import_xml_all "path"
    if lookahead(ps, "import_xml_all") && !_is_followed_by_eq(ps, "import_xml_all")
        expect!(ps, "import_xml_all")
        path = read_word!(ps)
        return InstanceImportXml(path)
    end

    # spanify instance
    if lookahead(ps, "spanify") && !_is_followed_by_eq(ps, "spanify")
        expect!(ps, "spanify")
        i = parse_instance_exp!(ps)
        return InstanceSpanify(i)
    end

    # frozen query entity (instance form — not "frozen Q lambda ..." which is transform form)
    if lookahead(ps, "frozen") && !_is_followed_by_eq(ps, "frozen")
        r = try_parse(ps, function(ps2)
            expect!(ps2, "frozen")
            q = parse_query_exp!(ps2)
            skip_ws!(ps2)
            # If next token is "lambda", this is actually a transform form — fail the try_parse
            if lookahead(ps2, "lambda")
                parse_error(ps2, "transform form, not instance form")
            end
            entity = read_identifier!(ps2)
            InstanceFrozen(q, entity)
        end)
        if r !== nothing
            return r
        end
    end

    # except inst1 inst2
    if lookahead(ps, "except") && !_is_followed_by_eq(ps, "except")
        expect!(ps, "except")
        i1 = parse_instance_exp!(ps)
        i2 = parse_instance_exp!(ps)
        return InstanceExcept(i1, i2)
    end

    # anonymize instance
    if lookahead(ps, "anonymize") && !_is_followed_by_eq(ps, "anonymize")
        expect!(ps, "anonymize")
        i = parse_instance_exp!(ps)
        return InstanceAnonymize(i)
    end

    # pi mapping instance [{ options }]
    if lookahead(ps, "pi") && !_is_followed_by_eq(ps, "pi")
        expect!(ps, "pi")
        m = parse_mapping_exp!(ps)
        i = parse_instance_exp!(ps)
        opts = _parse_optional_options_block!(ps)
        return InstancePi(m, i, opts)
    end

    # cascade_delete instance : schema
    if lookahead(ps, "cascade_delete") && !_is_followed_by_eq(ps, "cascade_delete")
        expect!(ps, "cascade_delete")
        i = parse_instance_exp!(ps)
        expect!(ps, ":")
        sch = parse_schema_exp!(ps)
        return InstanceCascadeDelete(i, sch)
    end

    # dom_t transform → domain instance of transform
    if lookahead(ps, "dom_t") && !_is_followed_by_eq(ps, "dom_t")
        expect!(ps, "dom_t")
        t = parse_transform_exp!(ps)
        return InstanceDomT(t)
    end

    # cod_t transform → codomain instance of transform
    if lookahead(ps, "cod_t") && !_is_followed_by_eq(ps, "cod_t")
        expect!(ps, "cod_t")
        t = parse_transform_exp!(ps)
        return InstanceCodT(t)
    end

    # quotient_query instance { query-like body }
    if lookahead(ps, "quotient_query") && !_is_followed_by_eq(ps, "quotient_query")
        expect!(ps, "quotient_query")
        i = parse_instance_exp!(ps)
        # Parse the query-like body in braces
        body = if lookahead(ps, "{")
            parse_braces!(ps, function(ps2)
                ens = Any[]
                while try_expect!(ps2, "entity")
                    en_name = read_identifier!(ps2)
                    expect!(ps2, "->")
                    en_block = parse_braces!(ps2, _parse_query_entity_body!)
                    push!(ens, (en_name, en_block))
                end
                parse_optional_section!(ps2, "options", parse_option!)
                ens
            end)
        else
            nothing
        end
        return InstanceQuotientQuery(i, body)
    end

    if lookahead(ps, "(")
        return parse_parens!(ps, parse_instance_exp!)
    end

    # Variable reference
    name = read_identifier!(ps)
    InstanceVar(name)
end

"""Check if a word at current position is followed by '=' (indicating it's a variable assignment, not a keyword)."""
function _is_followed_by_eq(ps::ParseState, word::String)::Bool
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

"""Parse generator count: entity -> count"""
function _parse_gen_count!(ps::ParseState)::Tuple{String,Int}
    name = read_identifier!(ps)
    expect!(ps, "->")
    count = read_int!(ps)
    (name, count)
end

"""Parse optional { options ... } block."""
function _parse_optional_options_block!(ps::ParseState)::Vector{Tuple{String,String}}
    skip_ws!(ps)
    if lookahead(ps, "{")
        return parse_braces!(ps, function(ps2)
            parse_optional_section!(ps2, "options", parse_option!)
        end)
    end
    Tuple{String,String}[]
end

"""Parse a raw instance: literal : schema { generators ... equations ... options ... }"""
function _parse_instance_raw!(ps::ParseState)::InstExpRaw
    expect!(ps, "literal")
    expect!(ps, ":")
    sch_ref = parse_schema_exp!(ps)

    parse_braces!(ps, function(ps2)
        imports = parse_optional_section!(ps2, "imports", parse_instance_exp!)

        gen_groups = parse_optional_section!(ps2, "generators", _parse_gen_decl!)
        gens = reduce(vcat, gen_groups; init=Tuple{String,String}[])

        eqs = parse_optional_section!(ps2, "equations", parse_equation!)

        multi_eqs = parse_optional_section!(ps2, "multi_equations", _parse_multi_eq!)
        all_eqs = vcat(
            Tuple{RawTerm,RawTerm}[eq for eq in eqs],
            reduce(vcat, multi_eqs; init=Tuple{RawTerm,RawTerm}[])
        )

        options = parse_optional_section!(ps2, "options", parse_option!)

        InstExpRaw(
            sch_ref,
            gens,
            all_eqs,
            Tuple{String,String}[o for o in options],
            imports,
        )
    end)
end

"""Parse generator declaration: gen1 gen2 ... : entity"""
function _parse_gen_decl!(ps::ParseState)::Vector{Tuple{String,String}}
    names = parse_some!(ps, ps2 -> read_identifier!(ps2))
    expect!(ps, ":")
    en = read_identifier!(ps)
    [(n, en) for n in names]
end

"""Parse a single multi-equation: id -> { term term, term term, ... }"""
function _parse_multi_eq!(ps::ParseState)::Vector{Tuple{RawTerm,RawTerm}}
    label = read_identifier!(ps)
    expect!(ps, "->")
    expect!(ps, "{")
    pairs = parse_sep_by!(ps, function(ps3)
        t1 = parse_raw_term!(ps3)
        t2 = parse_raw_term!(ps3)
        (RawTerm(label, RawTerm[t1]), t2)
    end, ",")
    expect!(ps, "}")
    pairs
end
