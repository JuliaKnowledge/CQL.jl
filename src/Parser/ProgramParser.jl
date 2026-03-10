"""
Top-level CQL program parser.

Grammar:
  program ::= [options ...] declaration*
  declaration ::= "typeside" name "=" typeside_exp
                | "schema" name "=" schema_exp
                | "instance" name "=" instance_exp
                | "mapping" name "=" mapping_exp
                | "transform" name "=" transform_exp
                | "query" name "=" query_exp
"""

"""An expression in the CQL program."""
struct Exp
    kind::Kind
    name::String
    body::Any  # TypesideExp | SchemaExp | InstanceExp | MappingExp | TransformExp | QueryExp
end

"""A parsed CQL program before evaluation."""
struct Program
    options::Vector{Tuple{String,String}}
    exps::Vector{Exp}
end

"""Parse a complete CQL program from source text."""
function parse_program(source::String)::Program
    ps = ParseState(source)
    skip_ws!(ps)

    # Optional global options
    global_opts = Tuple{String,String}[]
    if try_expect!(ps, "options")
        global_opts = parse_many!(ps, parse_option!)
    end

    # Parse declarations
    exps = Exp[]
    while !at_end(ps)
        skip_ws!(ps)
        at_end(ps) && break

        exp = _parse_declaration!(ps)
        push!(exps, exp)
    end

    # Check for duplicates
    names = [e.name for e in exps]
    seen = Set{String}()
    for n in names
        if n in seen
            throw(CQLException("Duplicate definition: $n"))
        end
        push!(seen, n)
    end

    Program(global_opts, exps)
end

"""Parse a single declaration: kind name = body"""
function _parse_declaration!(ps::ParseState)::Exp
    skip_ws!(ps)

    if try_expect!(ps, "typeside")
        name = read_identifier!(ps)
        expect!(ps, "=")
        body = parse_typeside_exp!(ps)
        return Exp(TYPESIDE, name, body)
    end

    if try_expect!(ps, "schema")
        name = read_identifier!(ps)
        expect!(ps, "=")
        body = parse_schema_exp!(ps)
        return Exp(SCHEMA, name, body)
    end

    if try_expect!(ps, "instance")
        name = read_identifier!(ps)
        expect!(ps, "=")
        body = parse_instance_exp!(ps)
        return Exp(INSTANCE, name, body)
    end

    if try_expect!(ps, "mapping")
        name = read_identifier!(ps)
        expect!(ps, "=")
        body = parse_mapping_exp!(ps)
        return Exp(MAPPING, name, body)
    end

    if try_expect!(ps, "transform")
        name = read_identifier!(ps)
        expect!(ps, "=")
        body = parse_transform_exp!(ps)
        return Exp(TRANSFORM, name, body)
    end

    if try_expect!(ps, "query")
        name = read_identifier!(ps)
        expect!(ps, "=")
        body = parse_query_exp!(ps)
        return Exp(QUERY, name, body)
    end

    if try_expect!(ps, "schema_colimit")
        name = read_identifier!(ps)
        expect!(ps, "=")
        body = parse_schema_colimit_exp!(ps)
        return Exp(SCHEMA_COLIMIT, name, body)
    end

    if try_expect!(ps, "constraints")
        name = read_identifier!(ps)
        expect!(ps, "=")
        body = parse_constraints_exp!(ps)
        return Exp(CONSTRAINTS, name, body)
    end

    # Command declarations: command name = exec_jdbc/export_jdbc_instance/...
    if try_expect!(ps, "command")
        name = read_identifier!(ps)
        expect!(ps, "=")
        cmd = _parse_command_body!(ps)
        return Exp(COMMAND, name, cmd)
    end

    # Graph declarations: graph name = literal { nodes ... edges ... }
    if try_expect!(ps, "graph")
        name = read_identifier!(ps)
        expect!(ps, "=")
        body = _parse_graph_body!(ps)
        return Exp(GRAPH, name, body)
    end

    # html/md blocks (comments with HTML/markdown content) - skip entirely
    if lookahead(ps, "html") || lookahead(ps, "md")
        _skip_unknown_declaration!(ps)
        skip_ws!(ps)
        if at_end(ps)
            return Exp(COMMAND, "__html_skip__", nothing)
        end
        return _parse_declaration!(ps)  # recursively parse next declaration
    end

    # Unsupported declarations that we skip: apg_typeside, apg_schema, apg_instance,
    # apg_morphism, apg_mapping, span, colimit, etc.
    unsupported_keywords = ["apg_typeside", "apg_schema", "apg_instance",
                            "apg_morphism", "apg_mapping", "span", "colimit",
                            "sql_type_side", "pragma"]
    for kw in unsupported_keywords
        if lookahead(ps, kw)
            expect!(ps, kw)
            name = try_parse(ps, function(ps2)
                n = read_identifier!(ps2)
                expect!(ps2, "=")
                n
            end)
            if name === nothing
                name = "__skip_$(kw)_$(ps.pos)"
            end
            _skip_to_end_of_decl!(ps)
            return Exp(COMMAND, string(name), nothing)  # reuse COMMAND kind for skipping
        end
    end

    parse_error(ps, "Expected declaration (typeside, schema, instance, mapping, transform, query, schema_colimit, or constraints)")
end

"""Parse a graph body: literal { nodes n1 n2 ... edges e1 : n1 -> n2 ... }"""
function _parse_graph_body!(ps::ParseState)
    expect!(ps, "literal")
    parse_braces!(ps, function(ps2)
        nodes = String[]
        edges = Tuple{String, Tuple{String, String}}[]

        while true
            skip_ws!(ps2)
            if try_expect!(ps2, "nodes")
                # Read node names, but stop before section keywords like "edges"
                append!(nodes, parse_many!(ps2, function(ps3)
                    skip_ws!(ps3)
                    if lookahead(ps3, "edges") || lookahead(ps3, "nodes") || (!at_end(ps3) && peek_char(ps3) == '}')
                        parse_error(ps3, "end of nodes section")
                    end
                    read_identifier!(ps3)
                end))
            elseif try_expect!(ps2, "edges")
                for group in parse_many!(ps2, ps3 -> parse_arrow_decl!(ps3))
                    append!(edges, group)
                end
            else
                break
            end
        end

        (nodes, edges)
    end)
end

"""Skip a command body: reads tokens until the next top-level declaration keyword or EOF."""
function _skip_command_body!(ps::ParseState)
    _skip_to_end_of_decl!(ps)
end

# ============================================================================
# Command expression types
# ============================================================================

"""exec_jdbc "conn" { "sql1" "sql2" ... }"""
struct CommandExecJdbc
    conn::String
    sqls::Vector{String}
end

"""export_jdbc_instance inst_name "conn" "prefix" [{ options }]"""
struct CommandExportJdbc
    instance_name::String
    conn::String
    prefix::String
    options::Vector{Tuple{String,String}}
end

"""exec_odbc "conn" { "sql1" "sql2" ... }"""
struct CommandExecOdbc
    conn::String
    sqls::Vector{String}
end

"""export_odbc_instance inst_name "conn" "prefix" [{ options }]"""
struct CommandExportOdbc
    instance_name::String
    conn::String
    prefix::String
    options::Vector{Tuple{String,String}}
end

"""export_rdf_instance_xml inst_name "filepath" { external_types ... }"""
struct CommandExportRdfInstanceXml
    instance_name::String
    filepath::String
    external_types::Dict{String,String}
end

"""Unrecognized command (check, etc.) — skip."""
struct CommandSkip end

"""Parse a command body after 'command name ='."""
function _parse_command_body!(ps::ParseState)
    skip_ws!(ps)

    # exec_jdbc "conn" { "sql1" "sql2" ... }
    if lookahead(ps, "exec_jdbc")
        expect!(ps, "exec_jdbc")
        skip_ws!(ps)
        conn = read_string!(ps)
        skip_ws!(ps)
        sqls = String[]
        if !at_end(ps) && peek_char(ps) == '{'
            parse_braces!(ps, function(ps2)
                while !at_end(ps2)
                    skip_ws!(ps2)
                    at_end(ps2) && break
                    peek_char(ps2) == '}' && break
                    if peek_char(ps2) == '"'
                        push!(sqls, read_string!(ps2))
                    else
                        # skip options or other tokens
                        r = try_parse(ps2, function(ps3)
                            if try_expect!(ps3, "options")
                                parse_many!(ps3, parse_option!)
                                return true
                            end
                            read_identifier!(ps3)
                            true
                        end)
                        r === nothing && break
                    end
                end
            end)
        end
        return CommandExecJdbc(conn, sqls)
    end

    # export_jdbc_instance inst_name "conn" "prefix" [{ options }]
    if lookahead(ps, "export_jdbc_instance")
        expect!(ps, "export_jdbc_instance")
        skip_ws!(ps)
        inst_name = read_identifier!(ps)
        skip_ws!(ps)
        conn = read_string!(ps)
        skip_ws!(ps)
        prefix = read_string!(ps)
        skip_ws!(ps)
        cmd_opts = Tuple{String,String}[]
        if !at_end(ps) && peek_char(ps) == '{'
            parse_braces!(ps, function(ps2)
                while !at_end(ps2)
                    skip_ws!(ps2)
                    at_end(ps2) && break
                    peek_char(ps2) == '}' && break
                    if try_expect!(ps2, "options")
                        append!(cmd_opts, parse_many!(ps2, parse_option!))
                    else
                        r = try_parse(ps2, function(ps3)
                            read_identifier!(ps3)
                            true
                        end)
                        r === nothing && break
                    end
                end
            end)
        end
        return CommandExportJdbc(inst_name, conn, prefix, cmd_opts)
    end

    # exec_odbc "conn" { "sql1" "sql2" ... }
    if lookahead(ps, "exec_odbc")
        expect!(ps, "exec_odbc")
        skip_ws!(ps)
        conn = read_string!(ps)
        skip_ws!(ps)
        sqls = String[]
        if !at_end(ps) && peek_char(ps) == '{'
            parse_braces!(ps, function(ps2)
                while !at_end(ps2)
                    skip_ws!(ps2)
                    at_end(ps2) && break
                    peek_char(ps2) == '}' && break
                    if peek_char(ps2) == '"'
                        push!(sqls, read_string!(ps2))
                    else
                        r = try_parse(ps2, function(ps3)
                            if try_expect!(ps3, "options")
                                parse_many!(ps3, parse_option!)
                                return true
                            end
                            read_identifier!(ps3)
                            true
                        end)
                        r === nothing && break
                    end
                end
            end)
        end
        return CommandExecOdbc(conn, sqls)
    end

    # export_odbc_instance inst_name "conn" "prefix" [{ options }]
    if lookahead(ps, "export_odbc_instance")
        expect!(ps, "export_odbc_instance")
        skip_ws!(ps)
        inst_name = read_identifier!(ps)
        skip_ws!(ps)
        conn = read_string!(ps)
        skip_ws!(ps)
        prefix = read_string!(ps)
        skip_ws!(ps)
        cmd_opts = Tuple{String,String}[]
        if !at_end(ps) && peek_char(ps) == '{'
            parse_braces!(ps, function(ps2)
                while !at_end(ps2)
                    skip_ws!(ps2)
                    at_end(ps2) && break
                    peek_char(ps2) == '}' && break
                    if try_expect!(ps2, "options")
                        append!(cmd_opts, parse_many!(ps2, parse_option!))
                    else
                        r = try_parse(ps2, function(ps3)
                            read_identifier!(ps3)
                            true
                        end)
                        r === nothing && break
                    end
                end
            end)
        end
        return CommandExportOdbc(inst_name, conn, prefix, cmd_opts)
    end

    # export_rdf_instance_xml inst_name "filepath" { external_types ... }
    if lookahead(ps, "export_rdf_instance_xml")
        expect!(ps, "export_rdf_instance_xml")
        skip_ws!(ps)
        inst_name = read_identifier!(ps)
        skip_ws!(ps)
        filepath = read_string!(ps)
        skip_ws!(ps)
        ext_types = Dict{String,String}()
        if !at_end(ps) && peek_char(ps) == '{'
            parse_braces!(ps, function(ps2)
                while !at_end(ps2)
                    skip_ws!(ps2)
                    at_end(ps2) && break
                    peek_char(ps2) == '}' && break
                    if try_expect!(ps2, "external_types")
                        # Parse: TypeName -> "xsd_uri" "converter_expr"
                        while !at_end(ps2)
                            skip_ws!(ps2)
                            at_end(ps2) && break
                            c = peek_char(ps2)
                            (c == '}' || c == 'o') && break  # end or 'options'
                            ty_name = read_identifier!(ps2)
                            skip_ws!(ps2)
                            expect!(ps2, "->")
                            skip_ws!(ps2)
                            xsd_uri = read_string!(ps2)
                            skip_ws!(ps2)
                            # Skip the converter expression (e.g., "x => x.toString()")
                            if !at_end(ps2) && peek_char(ps2) == '"'
                                read_string!(ps2)
                            end
                            ext_types[ty_name] = xsd_uri
                        end
                    elseif try_expect!(ps2, "options")
                        parse_many!(ps2, parse_option!)
                    else
                        r = try_parse(ps2, function(ps3)
                            read_identifier!(ps3)
                            true
                        end)
                        r === nothing && break
                    end
                end
            end)
        end
        return CommandExportRdfInstanceXml(inst_name, filepath, ext_types)
    end

    # Unknown command: skip
    _skip_to_end_of_decl!(ps)
    return CommandSkip()
end

"""Skip tokens until the next top-level declaration keyword or EOF.
Handles balanced braces and quoted strings."""
function _skip_to_end_of_decl!(ps::ParseState)
    decl_keywords = ["typeside", "schema", "instance", "mapping", "transform",
                     "query", "schema_colimit", "constraints", "command", "graph", "html", "md",
                     "apg_typeside", "apg_schema", "apg_instance", "apg_morphism",
                     "apg_mapping", "span", "colimit", "pragma", "sql_type_side"]
    depth = 0
    while !at_end(ps)
        skip_ws!(ps)
        at_end(ps) && break

        c = peek_char(ps)
        if c == '{'
            advance!(ps)
            depth += 1
        elseif c == '}'
            if depth > 0
                advance!(ps)
                depth -= 1
                if depth == 0
                    break  # matched the outermost brace block
                end
            else
                break  # don't consume unmatched '}'
            end
        elseif c == '"'
            # Skip quoted string
            advance!(ps)  # opening quote
            while !at_end(ps) && peek_char(ps) != '"'
                if peek_char(ps) == '\\'
                    advance!(ps)  # skip escape char
                end
                advance!(ps)
            end
            !at_end(ps) && advance!(ps)  # closing quote
        elseif depth == 0
            # Check if we've hit a declaration keyword at a word boundary
            is_at_decl = false
            for kw in decl_keywords
                if lookahead(ps, kw)
                    is_at_decl = true
                    break
                end
            end
            if is_at_decl
                break
            end
            # Skip the entire word/token at once to avoid matching keywords
            # in the middle of identifiers (e.g., "export_csv_instance")
            if is_id_char(c)
                while !at_end(ps) && is_id_char(peek_char(ps))
                    advance!(ps)
                end
            else
                advance!(ps)
            end
        else
            # Inside braces: skip entire words at once too
            if is_id_char(c)
                while !at_end(ps) && is_id_char(peek_char(ps))
                    advance!(ps)
                end
            else
                advance!(ps)
            end
        end
    end
end

"""Skip an unknown declaration (like 'html { ... }')."""
function _skip_unknown_declaration!(ps::ParseState)
    # Skip everything until we've passed any brace blocks
    while !at_end(ps)
        c = peek_char(ps)
        if c == '{'
            advance!(ps)
            _skip_brace_block!(ps)
            break
        elseif c == '\n'
            advance!(ps)
            break
        else
            advance!(ps)
        end
    end
end

"""Skip contents of a brace block (assumes opening '{' already consumed)."""
function _skip_brace_block!(ps::ParseState)
    depth = 1
    while !at_end(ps) && depth > 0
        c = peek_char(ps)
        if c == '{'
            depth += 1
        elseif c == '}'
            depth -= 1
        elseif c == '"'
            advance!(ps)
            while !at_end(ps) && peek_char(ps) != '"'
                if peek_char(ps) == '\\'
                    advance!(ps)
                end
                advance!(ps)
            end
        end
        advance!(ps)
    end
end
