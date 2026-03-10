"""
Parser for constraints declarations.

Grammar:
  constraints_exp ::= "literal" ":" schema {
      forall x:Entity1 y:Entity2
      where term = term  term = term ...
      -> where term = term  term = term ...

      // TGD form:
      forall x:Entity1 y:Entity2
      where term = term ...
      -> exists [unique] z:Entity3
      where term = term  term = term ...
  }
"""

"""Parse a constraints expression."""
function parse_constraints_exp!(ps::ParseState)
    # Handle 'all' constraints: all InstanceName TypesideName
    if lookahead(ps, "all") && !_is_followed_by_eq_constraints(ps, "all")
        expect!(ps, "all")
        _inst_name = read_identifier!(ps)
        _ts_name = read_identifier!(ps)
        # 'all' generates trivial constraints — return empty constraints referencing instance's schema
        return ConstraintsRawExp(
            SchemaVar("__all_dummy__"),
            Any[],
            Tuple{String,String}[],
            Any[_inst_name],
        )
    end

    # Handle sigma/delta constraints: sigma mapping constraints
    if lookahead(ps, "sigma") && !_is_followed_by_eq_constraints(ps, "sigma")
        expect!(ps, "sigma")
        mapping_ref = parse_mapping_exp!(ps)
        constraints_name = read_identifier!(ps)
        return ConstraintsRawExp(
            SchemaVar("__sigma_dummy__"),
            Any[],
            Tuple{String,String}[],
            Any[constraints_name],
            mapping_ref,
        )
    end

    # empty : schema
    if lookahead(ps, "empty") && !_is_followed_by_eq_constraints(ps, "empty")
        expect!(ps, "empty")
        expect!(ps, ":")
        sch_ref = parse_schema_exp!(ps)
        return ConstraintsEmpty(sch_ref)
    end

    # include schema old new [{ options }]
    if lookahead(ps, "include") && !_is_followed_by_eq_constraints(ps, "include")
        expect!(ps, "include")
        sch_ref = parse_schema_exp!(ps)
        old_name = read_string!(ps)
        new_name = read_string!(ps)
        opts = Tuple{String,String}[]
        skip_ws!(ps)
        if !at_end(ps) && peek_char(ps) == '{'
            opts = parse_braces!(ps, function(ps2)
                parse_optional_section!(ps2, "options", parse_option!)
            end)
        end
        return ConstraintsInclude(sch_ref, old_name, new_name, opts)
    end

    # fromSchema schema → constraints derived from schema
    if lookahead(ps, "fromSchema") && !_is_followed_by_eq_constraints(ps, "fromSchema")
        expect!(ps, "fromSchema")
        sch_ref = parse_schema_exp!(ps)
        return ConstraintsFromSchema(sch_ref)
    end

    expect!(ps, "literal")
    expect!(ps, ":")
    sch_ref = parse_schema_exp!(ps)

    parse_braces!(ps, function(ps2)
        imports = parse_optional_section!(ps2, "imports", parse_constraints_exp_ref!)
        egds = parse_many!(ps2, _parse_egd!)
        options = parse_optional_section!(ps2, "options", parse_option!)

        ConstraintsRawExp(
            sch_ref,
            egds,
            Tuple{String,String}[o for o in options],
            imports,
        )
    end)
end

"""Parse a constraints import reference."""
function parse_constraints_exp_ref!(ps::ParseState)
    name = read_identifier!(ps)
    name  # Return as a string reference to be resolved later
end

"""Check if a word is followed by '=' (variable assignment, not keyword)."""
function _is_followed_by_eq_constraints(ps::ParseState, word::String)::Bool
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

"""Parse constraint variable bindings: x:E1 y z:E2 ...
Supports both individual (x:E1 y:E2) and multi-var (x y z:E) bindings."""
function _parse_constraint_vars!(ps::ParseState)::Vector{Tuple{String, String}}
    result = Tuple{String, String}[]
    while true
        # Try to parse a group: name+ : type
        r = try_parse(ps, function(ps2)
            first_name = read_identifier!(ps2)
            names = [first_name]
            # Read more names until we see ':'
            while !lookahead(ps2, ":")
                n = read_identifier!(ps2)
                push!(names, n)
            end
            expect!(ps2, ":")
            ty = read_identifier!(ps2)
            [(n, ty) for n in names]
        end)
        if r === nothing
            break
        end
        append!(result, r)
    end
    result
end

"""Parse a single EGD/TGD block: forall vars where premises -> [exists [unique] vars] where conclusions"""
function _parse_egd!(ps::ParseState)
    expect!(ps, "forall")

    # Parse variable bindings: x:Entity1 y z:Entity2 ...
    vars = _parse_constraint_vars!(ps)

    # Parse premise where-clause
    premises = Tuple{RawTerm, RawTerm}[]
    if try_expect!(ps, "where")
        while true
            r = try_parse(ps, function(ps2)
                # Check we haven't hit the arrow
                if lookahead(ps2, "->")
                    parse_error(ps2, "end of premises")
                end
                lhs = parse_raw_term!(ps2)
                expect!(ps2, "=")
                rhs = parse_raw_term!(ps2)
                (lhs, rhs)
            end)
            r === nothing && break
            push!(premises, r)
        end
    end

    # Parse conclusion
    expect!(ps, "->")

    # Check for exists clause (TGD)
    exists_vars = Tuple{String, String}[]
    is_unique = false
    if try_expect!(ps, "exists")
        # Optional 'unique' modifier (semantically = exists + all equalities must hold)
        is_unique = try_expect!(ps, "unique")

        exists_vars = _parse_constraint_vars!(ps)
    end

    conclusions = Tuple{RawTerm, RawTerm}[]
    if try_expect!(ps, "where")
        while true
            r = try_parse(ps, function(ps2)
                # Check we haven't hit another 'forall', 'options', or closing brace
                if lookahead(ps2, "forall") || lookahead(ps2, "}") || lookahead(ps2, "options")
                    parse_error(ps2, "end of conclusions")
                end
                lhs = parse_raw_term!(ps2)
                expect!(ps2, "=")
                rhs = parse_raw_term!(ps2)
                (lhs, rhs)
            end)
            r === nothing && break
            push!(conclusions, r)
        end
    end

    (vars, premises, exists_vars, conclusions, is_unique)
end
