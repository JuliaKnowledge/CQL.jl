"""
Parser for schema_colimit declarations.

Grammar:
  schema_colimit_exp ::= "quotient" schema1 "+" schema2 ... ":" typeside { entity_equations ... observation_equations ... path_equations ... options ... }
                       | "coproduct" schema1 "+" schema2 ... ":" typeside [{ ... }]
                       | "modify" base_colimit { rename ... remove ... }
                       | "pseudo_quotient" schema1 "+" schema2 ... ":" typeside { ... }
"""

"""Parse a schema_colimit expression."""
function parse_schema_colimit_exp!(ps::ParseState)
    # Handle modify
    if try_expect!(ps, "modify")
        return _parse_modify_colimit!(ps)
    end

    # Handle simplify: simplify ColimitName → return the same colimit (no-op simplification)
    if lookahead(ps, "simplify") && !_is_followed_by_eq_colimit(ps, "simplify")
        expect!(ps, "simplify")
        base_name = read_identifier!(ps)
        return SchemaColimitModify(base_name,
            Tuple{String,String}[], Tuple{String,String}[], Tuple{String,String}[],
            Tuple{String,String}[], Tuple{String,String}[])
    end

    # literal graphName : typeside { nodes ... edges ... }
    if try_expect!(ps, "literal")
        graph_name = read_identifier!(ps)
        expect!(ps, ":")
        ts_ref = parse_typeside_exp!(ps)
        node_map = Tuple{String,Any}[]
        edge_map = Tuple{String,Any}[]
        opts = Tuple{String,String}[]
        parse_braces!(ps, function(ps2)
            if try_expect!(ps2, "nodes")
                while true
                    r = try_parse(ps2, function(ps3)
                        node_name = read_identifier!(ps3)
                        expect!(ps3, "->")
                        sch_ref = parse_schema_exp!(ps3)
                        (node_name, sch_ref)
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
                        mapping_ref = parse_mapping_exp!(ps3)
                        (edge_name, mapping_ref)
                    end)
                    r === nothing && break
                    push!(edge_map, r)
                end
            end
            append!(opts, parse_optional_section!(ps2, "options", parse_option!))
        end)
        return SchemaColimitLiteralExp(graph_name, ts_ref, node_map, edge_map, opts)
    end

    # Accept 'quotient', 'coproduct', or 'pseudo_quotient'
    is_pseudo = false
    if try_expect!(ps, "quotient")
        # ok
    elseif try_expect!(ps, "coproduct")
        # ok
    elseif lookahead(ps, "pseudo_quotient") && !_is_followed_by_eq_colimit(ps, "pseudo_quotient")
        expect!(ps, "pseudo_quotient")
        is_pseudo = true
    else
        parse_error(ps, "Expected 'quotient', 'coproduct', 'modify', or 'pseudo_quotient'")
    end

    # Parse schema1 + schema2 + ...
    schema_refs = Tuple{String, SchemaExp}[]
    first_name = read_identifier!(ps)
    push!(schema_refs, (first_name, SchemaVar(first_name)))
    while try_expect!(ps, "+")
        name = read_identifier!(ps)
        push!(schema_refs, (name, SchemaVar(name)))
    end

    expect!(ps, ":")
    ts_ref = parse_typeside_exp!(ps)

    # May have no brace block (empty body)
    if !lookahead(ps, "{")
        return SchemaColimitExp(
            ts_ref,
            schema_refs,
            Tuple{String,String}[],
            Tuple{RawTerm,RawTerm}[],
            Tuple{String,Union{Nothing,String},RawTerm,RawTerm}[],
            Tuple{String,String}[],
        )
    end

    parse_braces!(ps, function(ps2)
        entity_eqs = Tuple{String,String}[]
        entity_isos = Tuple{String,String,String}[]
        path_eqs = Tuple{RawTerm,RawTerm}[]
        obs_eqs = Tuple{String,Union{Nothing,String},RawTerm,RawTerm}[]
        options = Tuple{String,String}[]

        while true
            skip_ws!(ps2)
            if try_expect!(ps2, "entity_equations")
                append!(entity_eqs, parse_many!(ps2, _parse_entity_eq!))
            elseif try_expect!(ps2, "entity_isomorphisms")
                # entity_isomorphisms: name : S1.E1 -> S2.E2
                isos = parse_many!(ps2, _parse_entity_iso!)
                for (name, lhs, rhs) in isos
                    if !is_pseudo
                        # For quotient: isomorphisms also merge entities
                        push!(entity_eqs, (lhs, rhs))
                    end
                    push!(entity_isos, (name, lhs, rhs))
                end
            elseif try_expect!(ps2, "observation_equations")
                append!(obs_eqs, parse_many!(ps2, _parse_colimit_obs_eq!))
            elseif try_expect!(ps2, "path_equations")
                append!(path_eqs, parse_many!(ps2, _parse_colimit_path_eq!))
            elseif try_expect!(ps2, "equations")
                # 'equations' section — same as observation_equations
                append!(obs_eqs, parse_many!(ps2, _parse_colimit_obs_eq!))
            elseif try_expect!(ps2, "options")
                append!(options, parse_many!(ps2, parse_option!))
            else
                break
            end
        end

        SchemaColimitExp(
            ts_ref,
            schema_refs,
            entity_eqs,
            path_eqs,
            obs_eqs,
            options,
            entity_isos,
        )
    end)
end

"""Check if a word is followed by '=' (variable assignment, not keyword)."""
function _is_followed_by_eq_colimit(ps::ParseState, word::String)::Bool
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

"""Parse a modify colimit: modify base_colimit { rename ... remove ... }"""
function _parse_modify_colimit!(ps::ParseState)
    base_name = read_identifier!(ps)

    rename_ens = Tuple{String,String}[]
    rename_fks = Tuple{String,String}[]
    rename_atts = Tuple{String,String}[]
    remove_fks = Tuple{String,String}[]
    remove_atts = Tuple{String,String}[]

    if lookahead(ps, "{")
        parse_braces!(ps, function(ps2)
            while true
                skip_ws!(ps2)
                if try_expect!(ps2, "rename")
                    if try_expect!(ps2, "entities")
                        append!(rename_ens, parse_many!(ps2, _parse_rename!))
                    elseif try_expect!(ps2, "foreign_keys")
                        append!(rename_fks, parse_many!(ps2, _parse_rename!))
                    elseif try_expect!(ps2, "attributes")
                        append!(rename_atts, parse_many!(ps2, _parse_rename!))
                    end
                elseif try_expect!(ps2, "remove")
                    if try_expect!(ps2, "foreign_keys")
                        append!(remove_fks, parse_many!(ps2, _parse_remove!))
                    elseif try_expect!(ps2, "attributes")
                        append!(remove_atts, parse_many!(ps2, _parse_remove!))
                    end
                elseif try_expect!(ps2, "options")
                    parse_many!(ps2, parse_option!)  # consume but ignore
                else
                    break
                end
            end
        end)
    end

    SchemaColimitModify(base_name, rename_ens, rename_fks, rename_atts, remove_fks, remove_atts)
end

"""Parse a rename: old_name -> new_name"""
function _parse_rename!(ps::ParseState)::Tuple{String,String}
    old = _parse_dotted_name!(ps)
    expect!(ps, "->")
    new_name = read_identifier!(ps)
    (old, new_name)
end

"""Parse a remove: name -> replacement_path"""
function _parse_remove!(ps::ParseState)::Tuple{String,String}
    name = _parse_dotted_name!(ps)
    expect!(ps, "->")
    # Read the replacement as dotted path
    replacement = _parse_dotted_name!(ps)
    (name, replacement)
end

"""Parse an entity equation: S1.Entity1 = S2.Entity2"""
function _parse_entity_eq!(ps::ParseState)::Tuple{String, String}
    lhs = _parse_dotted_name!(ps)
    expect!(ps, "=")
    rhs = _parse_dotted_name!(ps)
    (lhs, rhs)
end

"""Parse an entity isomorphism: name : S1.E1 -> S2.E2 (treated as entity equation)"""
function _parse_entity_iso!(ps::ParseState)::Tuple{String,String,String}
    name = read_identifier!(ps)
    expect!(ps, ":")
    lhs = _parse_dotted_name!(ps)
    expect!(ps, "->")
    rhs = _parse_dotted_name!(ps)
    (name, lhs, rhs)
end

"""Parse a dotted name: Schema.Entity"""
function _parse_dotted_name!(ps::ParseState)::String
    parts = parse_sep_by1!(ps, ps2 -> read_identifier!(ps2), ".")
    join(parts, ".")
end

"""Parse a colimit observation equation: forall var[:type][,|.] term = term
Type can be dotted (e.g., SchemaName.EntityName). Separator can be '.' or ','."""
function _parse_colimit_obs_eq!(ps::ParseState)::Tuple{String,Union{Nothing,String},RawTerm,RawTerm}
    expect!(ps, "forall")
    var = read_identifier!(ps)
    ty = if try_expect!(ps, ":")
        # Read dotted type name (e.g., Olog1Schema.Patient)
        _parse_dotted_name!(ps)
    else
        nothing
    end
    # Accept either '.' or ',' as separator
    if !try_expect!(ps, ".") && !try_expect!(ps, ",")
        parse_error(ps, "Expected '.' or ',' after forall variable declaration")
    end
    lhs = parse_raw_term!(ps)
    expect!(ps, "=")
    rhs = parse_raw_term!(ps)
    (var, ty, lhs, rhs)
end

"""Parse a colimit path equation: Entity.fk1 = Entity.fk2"""
function _parse_colimit_path_eq!(ps::ParseState)::Tuple{RawTerm, RawTerm}
    lhs = parse_raw_term!(ps)
    expect!(ps, "=")
    rhs = parse_raw_term!(ps)
    (lhs, rhs)
end
