"""
CSV import/export for CQL instances.

Provides functions to read CQL instances from CSV files and write them back.
Each entity in a schema corresponds to a CSV file named `EntityName.csv`.
"""

# ============================================================================
# CSV Import
# ============================================================================

"""
    import_csv_instance(dir::String, schema::CQLSchema) -> CQLInstance

Import CSV files from a directory into a CQL instance.

Each entity in the schema should have a corresponding CSV file named
`EntityName.csv` in `dir`. The CSV must have:
- An `id` column containing a unique identifier for each row
- Columns matching foreign key names, containing IDs of target entity rows
- Columns matching attribute names, containing attribute values

Foreign key values reference IDs in the target entity's CSV file.
Missing attribute values become Skolem terms (nulls). Missing FK values
cause an error.

The resulting instance is a saturated algebra (equivalent to
`interpret_as_algebra = true` in CQL).

# Example
```julia
schema = cql"schema S = literal : sql { entities A }"
inst = import_csv_instance("data/mydb", schema.S)
```
"""
function import_csv_instance(dir::AbstractString, schema::CQLSchema)
    gens = Dict{Symbol, Symbol}()
    id_to_gen = Dict{Symbol, Dict{String, Symbol}}()
    eqs = Set{Equation}()

    for en in schema.ens
        id_to_gen[en] = Dict{String, Symbol}()
    end

    # First pass: read all CSV files and create generators
    for en in schema.ens
        filepath = joinpath(dir, string(en) * ".csv")
        isfile(filepath) || continue
        for row in CSV.File(filepath)
            raw_id = _csv_cell(row, :id)
            raw_id === nothing && continue
            gen_sym = Symbol(string(en, "_", raw_id))
            gens[gen_sym] = en
            id_to_gen[en][raw_id] = gen_sym
        end
    end

    # Second pass: build FK and attribute equations
    for en in schema.ens
        filepath = joinpath(dir, string(en) * ".csv")
        isfile(filepath) || continue
        csvfile = CSV.File(filepath)
        colnames = Set(propertynames(csvfile))

        for row in csvfile
            raw_id = _csv_cell(row, :id)
            raw_id === nothing && continue
            gen_sym = id_to_gen[en][raw_id]

            # Foreign key equations
            for (fk, (src, tgt)) in schema.fks
                src == en || continue
                fk in colnames || continue
                fk_id = _csv_cell(row, fk)
                fk_id === nothing && throw(CQLException(
                    "Missing foreign key value for $fk in row id=$raw_id of $en"))
                haskey(id_to_gen[tgt], fk_id) || throw(CQLException(
                    "Foreign key $fk=$fk_id references unknown id in entity $tgt"))
                push!(eqs, Equation(
                    CQLFk(fk, CQLGen(gen_sym)),
                    CQLGen(id_to_gen[tgt][fk_id])))
            end

            # Attribute equations
            for (att, (src, _)) in schema.atts
                src == en || continue
                att in colnames || continue
                val = _csv_cell(row, att)
                val === nothing && continue
                push!(eqs, Equation(
                    CQLAtt(att, CQLGen(gen_sym)),
                    CQLSym(Symbol(val), CQLTerm[])))
            end
        end
    end

    pres = Presentation(gens, Dict{Symbol, Symbol}(), eqs)
    saturated_instance(schema, pres)
end

# ============================================================================
# CSV Export
# ============================================================================

"""
    export_csv_instance(inst::CQLInstance, dir::String)

Export a CQL instance to CSV files in a directory.

Creates one CSV file per entity named `EntityName.csv`. Each file contains:
- An `id` column with globally unique integer identifiers
- Columns for each foreign key (containing target row IDs)
- Columns for each attribute (containing values)

The directory is created if it does not exist.

# Example
```julia
export_csv_instance(my_instance, "output/mydb")
```
"""
function export_csv_instance(inst::CQLInstance, dir::String)
    mkpath(dir)
    alg = inst.algebra
    sch = inst.schema

    # Build globally unique ID mapping (sorted for deterministic output)
    carrier_ids = Dict{Any, String}()
    id_counter = 0
    for en in sort(collect(sch.ens))
        for x in sort(collect(carrier(alg, en)); by=string)
            carrier_ids[x] = string(id_counter)
            id_counter += 1
        end
    end

    for en in sch.ens
        filepath = joinpath(dir, string(en) * ".csv")
        fks_list = sort(schema_fks_from(sch, en); by=x -> string(x[1]))
        atts_list = sort(schema_atts_from(sch, en); by=x -> string(x[1]))

        headers = vcat(["id"],
                       [string(fk) for (fk, _) in fks_list],
                       [string(att) for (att, _) in atts_list])

        open(filepath, "w") do io
            println(io, join(_csv_quote.(headers), ","))
            for x in sort(collect(carrier(alg, en)); by=string)
                vals = String[carrier_ids[x]]
                for (fk, _) in fks_list
                    push!(vals, carrier_ids[eval_fk(alg, fk, x)])
                end
                for (att, _) in atts_list
                    push!(vals, _term_to_csv(eval_att(alg, att, x)))
                end
                println(io, join(_csv_quote.(vals), ","))
            end
        end
    end
end

# ============================================================================
# Helpers
# ============================================================================

"""Read a cell from a CSV row, returning nothing for missing/empty values."""
function _csv_cell(row, col::Symbol)::Union{String, Nothing}
    val = getproperty(row, col)
    val === missing && return nothing
    s = strip(string(val))
    isempty(s) && return nothing
    return s
end

"""Quote a string value for CSV output."""
function _csv_quote(s::String)
    "\"" * replace(s, "\"" => "\"\"") * "\""
end

"""Convert a CQL term to a CSV-safe string value."""
function _term_to_csv(t::CQLTerm)::String
    t isa CQLSym && isempty(t.args) ? string(t.sym) : string(t)
end
