"""
Bridge between CQL.jl and Catlab.jl.

Provides conversions:
- CQLSchema -> Catlab BasicSchema
- CQLInstance -> DynamicACSet
"""

"""
Convert a CQL schema to a Catlab BasicSchema.

Returns a NamedTuple with:
- `schema`: the Catlab BasicSchema
- `type_assignment`: Dict mapping type symbols to Julia types
"""
const _CATLAB_INT_TYPES = Set([
    "bigint", "int", "integer", "smallint", "tinyint",
])

const _CATLAB_FLOAT_TYPES = Set([
    "decimal", "double", "doubleprecision", "float", "numeric", "real",
])

const _CATLAB_BOOL_TYPES = Set([
    "bit", "bool", "boolean",
])

function _catlab_julia_type(ty::Symbol)::Type
    normalized = lowercase(String(ty))
    if normalized in _CATLAB_INT_TYPES
        Int
    elseif normalized in _CATLAB_FLOAT_TYPES
        Float64
    elseif normalized in _CATLAB_BOOL_TYPES
        Bool
    else
        String
    end
end

function _coerce_catlab_value(term::CQLTerm, ty::Symbol, ts::Typeside)
    target = _catlab_julia_type(ty)
    target === String && return string(term)

    concrete = _extract_concrete_value(eval_typeside_term(ts, term), ts)
    concrete === nothing && throw(CQLException(
        "Cannot convert symbolic attribute value $term of type $ty to Catlab type $target"))

    if target === Int
        concrete isa Integer && return Int(concrete)
        concrete isa AbstractFloat && isinteger(concrete) && return Int(round(concrete))
    elseif target === Float64
        concrete isa Number && return Float64(concrete)
    elseif target === Bool
        concrete isa Bool && return concrete
    end

    throw(CQLException(
        "Cannot convert attribute value $term of type $ty to Catlab type $target"))
end

function cql_schema_to_catlab(sch::CQLSchema)
    ob_names = Symbol[en for en in sch.ens]

    homs = Tuple{Symbol,Symbol,Symbol}[]
    for (fk, (src, tgt)) in sch.fks
        push!(homs, (fk, src, tgt))
    end

    unique_types = Symbol[ty for ty in sch.typeside.tys]

    attrs = Tuple{Symbol,Symbol,Symbol}[]
    for (att, (src, ty)) in sch.atts
        push!(attrs, (att, src, ty))
    end

    schema_desc = BasicSchema(ob_names, homs, unique_types, attrs)

    type_assignment = Dict{Symbol,Type}(ty => _catlab_julia_type(ty) for ty in unique_types)

    (schema=schema_desc, type_assignment=type_assignment)
end

"""
Convert a CQL instance to a Catlab DynamicACSet.

Populates the ACSet with:
- One row per carrier element per entity
- FK values from the algebra
 - Attribute values converted to matching Julia scalars where possible
"""
function cql_instance_to_acset(inst::CQLInstance)
    catlab_info = cql_schema_to_catlab(inst.schema)
    sch_desc = catlab_info.schema

    acs = DynamicACSet("CQLInstance", sch_desc;
                       type_assignment=catlab_info.type_assignment)

    alg = inst.algebra
    elem_to_id = Dict{Any, Int}()

    # Add rows for each entity
    for en in inst.schema.ens
        for x in carrier(alg, en)
            id = add_part!(acs, en)
            elem_to_id[(en, x)] = id
        end
    end

    # Set FK values
    for (fk, (src, tgt)) in inst.schema.fks
        for x in carrier(alg, src)
            y = eval_fk(alg, fk, x)
            src_id = elem_to_id[(src, x)]
            tgt_id = elem_to_id[(tgt, y)]
            set_subpart!(acs, src_id, fk, tgt_id)
        end
    end

    # Set attribute values
    for (att, (src, ty)) in inst.schema.atts
        for x in carrier(alg, src)
            val = eval_att(alg, att, x)
            src_id = elem_to_id[(src, x)]
            set_subpart!(acs, src_id, att, _coerce_catlab_value(val, ty, inst.schema.typeside))
        end
    end

    acs
end
