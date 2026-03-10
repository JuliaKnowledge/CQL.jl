"""
Parser for schema declarations.

Grammar:
  schema_exp ::= "literal" ":" typeside { ... } | "empty" ":" typeside | identifier | "(" schema_exp ")"
"""

"""Parse a schema expression."""
function parse_schema_exp!(ps::ParseState)::SchemaExp
    skip_ws!(ps)

    if lookahead(ps, "literal")
        return SchemaRawExp(_parse_schema_raw!(ps))
    end

    if try_expect!(ps, "empty")
        expect!(ps, ":")
        ts = parse_typeside_exp!(ps)
        return SchemaInitial(ts)
    end

    if try_expect!(ps, "getSchema")
        colimit_name = read_identifier!(ps)
        return SchemaGetSchema(colimit_name)
    end

    # schemaOf instance → extract schema from an instance
    if lookahead(ps, "schemaOf") && !_is_followed_by_eq_schema(ps, "schemaOf")
        expect!(ps, "schemaOf")
        inst = parse_instance_exp!(ps)
        return SchemaOf(inst)
    end

    # pivot instance → schema
    if lookahead(ps, "pivot") && !_is_followed_by_eq_schema(ps, "pivot")
        expect!(ps, "pivot")
        i = parse_instance_exp!(ps)
        return SchemaPivot(i)
    end

    # import_jdbc_all "conn" { options ... } → schema (not supported but parse it)
    if lookahead(ps, "import_jdbc_all") && !_is_followed_by_eq_schema(ps, "import_jdbc_all")
        expect!(ps, "import_jdbc_all")
        conn = read_word!(ps)
        # Parse optional brace block with options
        opts = Tuple{String,String}[]
        skip_ws!(ps)
        if !at_end(ps) && peek_char(ps) == '{'
            parse_braces!(ps, function(ps2)
                parse_optional_section!(ps2, "options", function(ps3)
                    k, v = parse_option!(ps3)
                    push!(opts, (k, v))
                end)
            end)
        end
        return SchemaImportJdbcAll(conn, opts)
    end

    # import_odbc_all "conn" { options ... } → schema
    if lookahead(ps, "import_odbc_all") && !_is_followed_by_eq_schema(ps, "import_odbc_all")
        expect!(ps, "import_odbc_all")
        conn = read_word!(ps)
        opts = Tuple{String,String}[]
        skip_ws!(ps)
        if !at_end(ps) && peek_char(ps) == '{'
            parse_braces!(ps, function(ps2)
                parse_optional_section!(ps2, "options", function(ps3)
                    k, v = parse_option!(ps3)
                    push!(opts, (k, v))
                end)
            end)
        end
        return SchemaImportOdbcAll(conn, opts)
    end

    # front constraints index → schema
    if lookahead(ps, "front") && !_is_followed_by_eq_schema(ps, "front")
        expect!(ps, "front")
        cname = read_identifier!(ps)
        idx = read_int!(ps)
        return SchemaFront(cname, idx)
    end

    # spanify schema → schema
    if lookahead(ps, "spanify") && !_is_followed_by_eq_schema(ps, "spanify")
        expect!(ps, "spanify")
        sch = parse_schema_exp!(ps)
        return SchemaSpanify(sch)
    end

    # prefix schema "str" → schema
    if lookahead(ps, "prefix") && !_is_followed_by_eq_schema(ps, "prefix")
        expect!(ps, "prefix")
        sch = parse_schema_exp!(ps)
        prefix_str = read_string!(ps)
        return SchemaPrefix(sch, prefix_str)
    end

    # dom_q query → source schema of query
    if lookahead(ps, "dom_q") && !_is_followed_by_eq_schema(ps, "dom_q")
        expect!(ps, "dom_q")
        q = parse_query_exp!(ps)
        return SchemaDomQ(q)
    end

    # cod_q query → target schema of query
    if lookahead(ps, "cod_q") && !_is_followed_by_eq_schema(ps, "cod_q")
        expect!(ps, "cod_q")
        q = parse_query_exp!(ps)
        return SchemaCodQ(q)
    end

    # dom_m mapping → source schema of mapping
    if lookahead(ps, "dom_m") && !_is_followed_by_eq_schema(ps, "dom_m")
        expect!(ps, "dom_m")
        m = parse_mapping_exp!(ps)
        return SchemaDomM(m)
    end

    # cod_m mapping → target schema of mapping
    if lookahead(ps, "cod_m") && !_is_followed_by_eq_schema(ps, "cod_m")
        expect!(ps, "cod_m")
        m = parse_mapping_exp!(ps)
        return SchemaCodM(m)
    end

    if lookahead(ps, "(")
        return parse_parens!(ps, parse_schema_exp!)
    end

    # Variable reference
    name = read_identifier!(ps)
    SchemaVar(name)
end

"""Check if a word is followed by '=' (variable assignment, not keyword)."""
function _is_followed_by_eq_schema(ps::ParseState, word::String)::Bool
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

"""Parse a raw schema: literal : typeside { entities ... foreign_keys ... attributes ... }

Sections can appear in any order (matching Haskell CQL behavior)."""
function _parse_schema_raw!(ps::ParseState)::SchemaRaw
    expect!(ps, "literal")
    expect!(ps, ":")
    ts_ref = parse_typeside_exp!(ps)

    parse_braces!(ps, function(ps2)
        imports = Any[]
        ens = String[]
        fks = Tuple{String,Tuple{String,String}}[]
        atts = Tuple{String,Tuple{String,String}}[]
        path_eqs = Any[]
        obs_eqs = Any[]
        options = Tuple{String,String}[]

        while true
            skip_ws!(ps2)
            if try_expect!(ps2, "imports")
                append!(imports, parse_many!(ps2, parse_schema_exp!))
            elseif try_expect!(ps2, "entities")
                append!(ens, parse_many!(ps2, ps3 -> read_identifier!(ps3)))
            elseif try_expect!(ps2, "entity")
                # Per-entity block: entity E [foreign_keys ...] [attributes ...]
                en = read_identifier!(ps2)
                push!(ens, en)
                # Parse optional FK and attribute sections with implicit source entity
                en_fks = parse_optional_section!(ps2, "foreign_keys", ps3 -> _parse_schema_per_entity_fk!(ps3, en))
                for group in en_fks
                    append!(fks, group)
                end
                en_atts = parse_optional_section!(ps2, "attributes", ps3 -> _parse_schema_per_entity_att!(ps3, en))
                for group in en_atts
                    append!(atts, group)
                end
            elseif try_expect!(ps2, "foreign_keys")
                for group in parse_many!(ps2, _parse_schema_fk!)
                    append!(fks, group)
                end
            elseif try_expect!(ps2, "attributes")
                for group in parse_many!(ps2, _parse_schema_att!)
                    append!(atts, group)
                end
            elseif try_expect!(ps2, "path_equations")
                append!(path_eqs, parse_many!(ps2, _parse_path_eq!))
            elseif try_expect!(ps2, "observation_equations")
                append!(obs_eqs, parse_many!(ps2, _parse_obs_eq!))
            elseif try_expect!(ps2, "options")
                append!(options, parse_many!(ps2, parse_option!))
            else
                break
            end
        end

        SchemaRaw(
            ts_ref,
            ens,
            fks,
            atts,
            path_eqs,
            Tuple{String,Union{Nothing,String},RawTerm,RawTerm}[eq for eq in obs_eqs],
            options,
            imports,
        )
    end)
end

"""Parse FK declaration: fk1 fk2 ... : entity1 -> entity2"""
function _parse_schema_fk!(ps::ParseState)::Vector{Tuple{String, Tuple{String, String}}}
    parse_arrow_decl!(ps)
end

"""Parse attribute declaration: att1 att2 ... : entity -> type"""
function _parse_schema_att!(ps::ParseState)::Vector{Tuple{String, Tuple{String, String}}}
    parse_arrow_decl!(ps)
end

"""Parse per-entity FK: fk1 fk2 ... : target (source entity implicit)
Also supports full form fk : src -> tgt within per-entity blocks."""
function _parse_schema_per_entity_fk!(ps::ParseState, src_entity::String)::Vector{Tuple{String, Tuple{String, String}}}
    # Try full arrow form first: name : src -> tgt
    r = try_parse(ps, ps2 -> parse_arrow_decl!(ps2))
    if r !== nothing
        return r
    end
    # Per-entity shorthand: name1 name2 ... : target
    names = parse_some!(ps, ps2 -> read_identifier!(ps2))
    expect!(ps, ":")
    tgt = read_identifier!(ps)
    [(n, (src_entity, tgt)) for n in names]
end

"""Parse per-entity attribute: att1 att2 ... : type (source entity implicit)
Also supports full form att : src -> type within per-entity blocks."""
function _parse_schema_per_entity_att!(ps::ParseState, src_entity::String)::Vector{Tuple{String, Tuple{String, String}}}
    # Try full arrow form first: name : src -> tgt
    r = try_parse(ps, ps2 -> parse_arrow_decl!(ps2))
    if r !== nothing
        return r
    end
    # Per-entity shorthand: name1 name2 ... : type
    names = parse_some!(ps, ps2 -> read_identifier!(ps2))
    expect!(ps, ":")
    tgt = read_identifier!(ps)
    [(n, (src_entity, tgt)) for n in names]
end

"""Parse a path equation: a.b.c = d.e.f"""
function _parse_path_eq!(ps::ParseState)::Tuple{Vector{String}, Vector{String}}
    lhs = parse_sep_by1!(ps, ps2 -> read_identifier!(ps2), ".")
    expect!(ps, "=")
    rhs = parse_sep_by1!(ps, ps2 -> read_identifier!(ps2), ".")
    (String[s for s in lhs], String[s for s in rhs])
end

"""Parse an observation equation: forall var[:type] . term = term
OR shorthand: att = path (implicit forall variable)"""
function _parse_obs_eq!(ps::ParseState)::Tuple{String, Union{Nothing,String}, RawTerm, RawTerm}
    # Try the forall form first
    r = try_parse(ps, function(ps2)
        expect!(ps2, "forall")
        var = read_identifier!(ps2)
        ty = if try_expect!(ps2, ":")
            read_identifier!(ps2)
        else
            nothing
        end
        expect!(ps2, ".")
        lhs = parse_raw_term!(ps2)
        expect!(ps2, "=")
        rhs = parse_raw_term!(ps2)
        (var, ty, lhs, rhs)
    end)
    r !== nothing && return r

    # Shorthand form: att = path.att2 (no forall)
    # Means: forall _x . att(_x) = att2(path(_x))
    lhs = parse_raw_term!(ps)
    expect!(ps, "=")
    rhs = parse_raw_term!(ps)
    # Append implicit variable _x at the deepest position
    lhs_wrapped = _append_implicit_var(lhs, "_x")
    rhs_wrapped = _append_implicit_var(rhs, "_x")
    ("_x", nothing, lhs_wrapped, rhs_wrapped)
end

"""Append an implicit variable at the deepest position of a term chain."""
function _append_implicit_var(t::RawTerm, var_name::String)::RawTerm
    if isempty(t.args)
        RawTerm(t.head, [RawTerm(var_name, RawTerm[])])
    else
        RawTerm(t.head, [_append_implicit_var(t.args[1], var_name)])
    end
end
