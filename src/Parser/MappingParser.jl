"""
Parser for mapping declarations.

Grammar:
  mapping_exp ::= "literal" ":" schema "->" schema { entity_mappings... }
                | "identity" schema
                | "[" mapping ";" mapping "]"
                | identifier
                | "(" mapping_exp ")"
"""

"""Parse a mapping expression."""
function parse_mapping_exp!(ps::ParseState)::MappingExp
    skip_ws!(ps)

    # Composition: [ m1 ; m2 ]
    if lookahead(ps, "[")
        return _parse_mapping_comp!(ps)
    end

    if lookahead(ps, "literal")
        return MappingRawExp(_parse_mapping_raw!(ps))
    end

    if try_expect!(ps, "identity")
        sch = parse_schema_exp!(ps)
        return MappingId(sch)
    end

    if try_expect!(ps, "getMapping")
        colimit_name = read_identifier!(ps)
        schema_name = read_identifier!(ps)
        return MappingGetMapping(colimit_name, schema_name)
    end

    # getPseudo colimit_name → mapping from pseudo-quotient schema to result schema
    if try_expect!(ps, "getPseudo")
        colimit_name = read_identifier!(ps)
        return MappingGetPseudo(colimit_name)
    end

    # pivot instance → mapping (projection from pivot schema to original)
    if lookahead(ps, "pivot") && !_is_followed_by_eq_mapping(ps, "pivot")
        expect!(ps, "pivot")
        i = parse_instance_exp!(ps)
        return MappingPivot(i)
    end

    # include src_schema tgt_schema → inclusion mapping
    if lookahead(ps, "include") && !_is_followed_by_eq_mapping(ps, "include")
        expect!(ps, "include")
        src = parse_schema_exp!(ps)
        tgt = parse_schema_exp!(ps)
        return MappingInclude(src, tgt)
    end

    # to_prefix schema "prefix" → mapping to prefixed schema
    if lookahead(ps, "to_prefix") && !_is_followed_by_eq_mapping(ps, "to_prefix")
        expect!(ps, "to_prefix")
        sch = parse_schema_exp!(ps)
        prefix_str = read_string!(ps)
        return MappingToPrefix(sch, prefix_str)
    end

    # from_prefix schema "prefix" → mapping from prefixed schema
    if lookahead(ps, "from_prefix") && !_is_followed_by_eq_mapping(ps, "from_prefix")
        expect!(ps, "from_prefix")
        sch = parse_schema_exp!(ps)
        prefix_str = read_string!(ps)
        return MappingFromPrefix(sch, prefix_str)
    end

    if lookahead(ps, "(")
        return parse_parens!(ps, parse_mapping_exp!)
    end

    # Variable reference
    name = read_identifier!(ps)
    MappingVar(name)
end

"""Check if a word is followed by '=' (variable assignment, not keyword)."""
function _is_followed_by_eq_mapping(ps::ParseState, word::String)::Bool
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

"""Parse mapping composition: [ m1 ; m2 ]"""
function _parse_mapping_comp!(ps::ParseState)::MappingComp
    expect!(ps, "[")
    f = parse_mapping_exp!(ps)
    expect!(ps, ";")
    g = parse_mapping_exp!(ps)
    expect!(ps, "]")
    MappingComp(f, g)
end

"""Parse a raw mapping: literal : srcSchema -> tgtSchema { entity_mappings... }"""
function _parse_mapping_raw!(ps::ParseState)::MappingExpRaw
    expect!(ps, "literal")
    expect!(ps, ":")
    src_ref = parse_schema_exp!(ps)
    expect!(ps, "->")
    dst_ref = parse_schema_exp!(ps)

    parse_braces!(ps, function(ps2)
        imports = parse_optional_section!(ps2, "imports", parse_mapping_exp!)

        # Parse entity mappings: each is "entity src -> tgt [foreign_keys ...] [attributes ...]"
        ens = Tuple{String,String}[]
        fks = Tuple{String,Vector{String}}[]
        atts = Tuple{String,Any}[]

        while try_expect!(ps2, "entity")
            src_en = read_identifier!(ps2)
            expect!(ps2, "->")
            dst_en = read_identifier!(ps2)
            push!(ens, (src_en, dst_en))

            # Optional FK mappings within this entity
            en_fks = parse_optional_section!(ps2, "foreign_keys", _parse_mapping_fk!)
            append!(fks, en_fks)

            # Optional attribute mappings within this entity — tag with source entity
            en_atts = parse_optional_section!(ps2, "attributes", _parse_mapping_att!)
            for (an, av) in en_atts
                push!(atts, (an, (src_en, av)))
            end
        end

        options = parse_optional_section!(ps2, "options", parse_option!)

        MappingExpRaw(
            src_ref,
            dst_ref,
            ens,
            fks,
            atts,
            Tuple{String,String}[o for o in options],
            imports,
        )
    end)
end

"""Parse a FK mapping: fk -> path.to.target  or  fk -> identity"""
function _parse_mapping_fk!(ps::ParseState)::Tuple{String,Vector{String}}
    name = read_identifier!(ps)
    expect!(ps, "->")
    # Handle identity mapping: FK collapses to identity path
    if try_expect!(ps, "identity")
        return (name, String[])
    end
    path = parse_sep_by1!(ps, ps2 -> read_identifier!(ps2), ".")
    (name, String[s for s in path])
end

"""
Parse an attribute mapping.
Two forms:
  att -> lambda var[:type] . term    => (att, (var, type_hint, RawTerm))
  att -> path.to.att                  => (att, [String])
"""
function _parse_mapping_att!(ps::ParseState)::Tuple{String,Any}
    name = read_identifier!(ps)
    expect!(ps, "->")

    # Try lambda form
    if try_expect!(ps, "lambda")
        var = read_identifier!(ps)
        ty_hint = if try_expect!(ps, ":")
            read_identifier!(ps)
        else
            nothing
        end
        expect!(ps, ".")
        term = parse_raw_term!(ps)
        return (name, (var, ty_hint, term))
    end

    # Path form: a.b.c
    path = parse_sep_by1!(ps, ps2 -> read_identifier!(ps2), ".")
    (name, String[s for s in path])
end
