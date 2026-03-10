"""
Parser for typeside declarations.

Grammar:
  typeside_exp ::= "sql" | "empty" | "literal" { ... } | identifier | "(" typeside_exp ")"
"""

"""Parse a typeside expression."""
function parse_typeside_exp!(ps::ParseState)::TypesideExp
    skip_ws!(ps)

    if try_expect!(ps, "sql")
        return TypesideSql()
    end

    if try_expect!(ps, "rdf")
        return TypesideRdf()
    end

    if try_expect!(ps, "empty")
        return TypesideInitial()
    end

    if lookahead(ps, "literal")
        return TypesideRawExp(_parse_typeside_raw!(ps))
    end

    # typesideOf schema
    if lookahead(ps, "typesideOf")
        expect!(ps, "typesideOf")
        sch = parse_schema_exp!(ps)
        return TypesideOf(sch)
    end

    if lookahead(ps, "(")
        return parse_parens!(ps, parse_typeside_exp!)
    end

    # Variable reference
    name = read_identifier!(ps)
    TypesideVar(name)
end

"""Parse a raw typeside: literal { types ... constants ... functions ... equations ... options ... }

Sections can appear in any order."""
function _parse_typeside_raw!(ps::ParseState)::TypesideRaw
    expect!(ps, "literal")
    parse_braces!(ps, function(ps2)
        imports = Any[]
        tys = String[]
        constants = Vector{Tuple{String,Tuple{Vector{String},String}}}[]
        functions = Vector{Tuple{String,Tuple{Vector{String},String}}}[]
        eqs = Any[]
        options = Tuple{String,String}[]
        ext_fns = Tuple{String, Tuple{Vector{String}, String}, String}[]
        ext_parsers = Tuple{String, String}[]

        while true
            skip_ws!(ps2)
            if try_expect!(ps2, "imports")
                append!(imports, parse_many!(ps2, parse_typeside_exp!))
            elseif try_expect!(ps2, "types")
                append!(tys, parse_many!(ps2, ps3 -> read_identifier!(ps3)))
            elseif try_expect!(ps2, "constants")
                append!(constants, parse_many!(ps2, _parse_ts_constant!))
            elseif try_expect!(ps2, "functions")
                append!(functions, parse_many!(ps2, _parse_ts_function!))
            elseif try_expect!(ps2, "external_types")
                for et in parse_many!(ps2, _parse_external_type!)
                    push!(tys, et)
                end
            elseif try_expect!(ps2, "external_parsers")
                append!(ext_parsers, parse_many!(ps2, _parse_external_parser_with_code!))
            elseif try_expect!(ps2, "external_functions")
                for entry in parse_many!(ps2, _parse_external_function_with_code!)
                    push!(ext_fns, entry)
                    # Also add as regular function signature
                    push!(functions, [(entry[1], entry[2])])
                end
            elseif try_expect!(ps2, "equations")
                append!(eqs, parse_many!(ps2, parse_ts_equation!))
            elseif try_expect!(ps2, "options")
                append!(options, parse_many!(ps2, parse_option!))
            else
                break
            end
        end

        syms = vcat(reduce(vcat, constants; init=Tuple{String,Tuple{Vector{String},String}}[]),
                    reduce(vcat, functions; init=Tuple{String,Tuple{Vector{String},String}}[]))

        TypesideRaw(
            String[t for t in tys],
            syms,
            eqs,
            Tuple{String,String}[o for o in options],
            imports,
            ext_fns,
            ext_parsers,
        )
    end)
end

"""Parse a typeside constant declaration: name1 name2 ... : type"""
function _parse_ts_constant!(ps::ParseState)::Vector{Tuple{String, Tuple{Vector{String}, String}}}
    names = parse_some!(ps, ps2 -> read_identifier!(ps2))
    expect!(ps, ":")
    ty = read_identifier!(ps)
    [(n, (String[], ty)) for n in names]
end

"""Parse a typeside function declaration: name1 ... : type1, type2, ... -> retType
Also handles zero-arg functions: name : -> retType"""
function _parse_ts_function!(ps::ParseState)::Vector{Tuple{String, Tuple{Vector{String}, String}}}
    names = parse_some!(ps, ps2 -> read_identifier!(ps2))
    expect!(ps, ":")
    # Zero-arg function: name : -> retType
    if try_expect!(ps, "->")
        ret = read_identifier!(ps)
        return [(n, (String[], ret)) for n in names]
    end
    arg_types = parse_sep_by1!(ps, ps2 -> read_identifier!(ps2), ",")
    expect!(ps, "->")
    ret = read_identifier!(ps)
    [(n, (String[a for a in arg_types], ret)) for n in names]
end

"""Parse an external_type declaration: TypeName -> \"java.class.Name\" """
function _parse_external_type!(ps::ParseState)::String
    name = read_identifier!(ps)
    expect!(ps, "->")
    _read_string_value!(ps)  # skip the Java class name
    name
end

"""Parse an external_parser entry: TypeName -> \"parser code\".
Returns (type_name, code) tuple."""
function _parse_external_parser_with_code!(ps::ParseState)::Tuple{String, String}
    name = read_identifier!(ps)
    expect!(ps, "->")
    code = _read_string_value!(ps)
    (name, code)
end

"""Parse an external_function declaration with code:
name : ArgType, ... -> RetType = \"js code\"
Returns a single (name, (arg_types, ret_type), code) tuple."""
function _parse_external_function_with_code!(ps::ParseState)::Tuple{String, Tuple{Vector{String}, String}, String}
    name = read_identifier!(ps)
    expect!(ps, ":")
    if try_expect!(ps, "->")
        ret = read_identifier!(ps)
        expect!(ps, "=")
        code = _read_string_value!(ps)
        return (name, (String[], ret), code)
    end
    arg_types = parse_sep_by1!(ps, ps2 -> read_identifier!(ps2), ",")
    expect!(ps, "->")
    ret = read_identifier!(ps)
    expect!(ps, "=")
    code = _read_string_value!(ps)
    (name, (String[a for a in arg_types], ret), code)
end

"""Parse an external_function declaration: name : ArgType, ... -> RetType = \"java code\"
Also handles multi-arg: name : ArgType, ArgType -> RetType = \"(x, y) => ...\" """
function _parse_external_function!(ps::ParseState)::Vector{Tuple{String, Tuple{Vector{String}, String}}}
    names = parse_some!(ps, ps2 -> read_identifier!(ps2))
    expect!(ps, ":")
    # Zero-arg: name : -> retType = "code"
    if try_expect!(ps, "->")
        ret = read_identifier!(ps)
        expect!(ps, "=")
        _read_string_value!(ps)
        return [(n, (String[], ret)) for n in names]
    end
    arg_types = parse_sep_by1!(ps, ps2 -> read_identifier!(ps2), ",")
    expect!(ps, "->")
    ret = read_identifier!(ps)
    expect!(ps, "=")
    _read_string_value!(ps)  # skip the Java code string
    [(n, (String[a for a in arg_types], ret)) for n in names]
end

"""Read a quoted string value, consuming the quotes. Used for external Java code."""
function _read_string_value!(ps::ParseState)::String
    skip_ws!(ps)
    c = peek_char(ps)
    c == '"' || parse_error(ps, "Expected quoted string, got '$c'")
    read_string!(ps)
end
