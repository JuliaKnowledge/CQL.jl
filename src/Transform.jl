"""
Transforms: morphisms between instances of the same schema.

A transform h: I -> J consists of:
- Generator mapping: gen_I -> entity-side term in J
- Skolem mapping: sk_I -> type-side term in J
"""

"""A CQL transform between instances."""
struct CQLTransform
    src::CQLInstance
    dst::CQLInstance
    gens::Dict{Symbol, CQLTerm}   # src gen -> dst entity-side term
    sks::Dict{Symbol, CQLTerm}    # src sk -> dst type-side term
end

function Base.show(io::IO, tr::CQLTransform)
    println(io, "transform {")
    println(io, "  generators")
    for (s, t) in tr.gens
        println(io, "    ", s, " -> ", t)
    end
    println(io, "  skolems")
    for (s, t) in tr.sks
        println(io, "    ", s, " -> ", t)
    end
    println(io, "}")
end

"""Convert a transform to a morphism for type-checking."""
function transform_to_morphism(tr::CQLTransform)::Morphism
    sch = tr.src.schema
    ens0 = Dict(en => en for en in sch.ens)
    fks0 = Dict(fk => CQLFk(fk, CQLVar(Symbol("_unit"))) for fk in keys(sch.fks))
    atts0 = Dict(att => CQLAtt(att, CQLVar(Symbol("_unit"))) for att in keys(sch.atts))
    Morphism(
        presentation_to_collage(sch, tr.src.pres),
        presentation_to_collage(sch, tr.dst.pres),
        ens0, fks0, atts0, tr.gens, tr.sks,
    )
end

"""Typecheck a transform."""
function typecheck_transform(tr::CQLTransform)
    typecheck_morphism(transform_to_morphism(tr))
end

"""Validate that a transform preserves instance equations."""
function validate_transform(tr::CQLTransform)
    mor = transform_to_morphism(tr)
    for eq in tr.src.pres.eqs
        l = translate_term(mor, eq.lhs)
        r = translate_term(mor, eq.rhs)
        tr.dst.dp(Equation(l, r)) || throw(CQLException(
            "$eq translates to $(Equation(l, r)) which is not provable in target"))
    end
end

"""Compose two transforms."""
function compose_transform(f::CQLTransform, g::CQLTransform)
    g_mor = transform_to_morphism(g)
    new_gens = Dict(k => translate_entity_term(g_mor, v) for (k, v) in f.gens)
    new_sks = Dict(k => translate_term(g_mor, v) for (k, v) in f.sks)
    CQLTransform(f.src, g.dst, new_gens, new_sks)
end

"""Create an identity transform on an instance."""
function identity_transform(inst::CQLInstance)
    gens = Dict(g => CQLGen(g) for g in keys(inst.pres.gens))
    sks = Dict(s => CQLSk(s) for s in keys(inst.pres.sks))
    CQLTransform(inst, inst, gens, sks)
end

# ============================================================================
# Expression types
# ============================================================================

abstract type TransformExp end

struct TransformVar <: TransformExp
    name::String
end

struct TransformId <: TransformExp
    instance::InstanceExp
end

struct TransformComp <: TransformExp
    first::TransformExp
    second::TransformExp
end

struct TransformRawExp <: TransformExp
    src_ref::InstanceExp
    dst_ref::InstanceExp
    gens::Vector{Tuple{String, RawTerm}}
    options::Vector{Tuple{String, String}}
    imports::Vector{Any}
end

struct TransformDeltaExp <: TransformExp
    mapping::MappingExp
    transform::TransformExp
    options::Vector{Tuple{String,String}}
end

struct TransformSigmaExp <: TransformExp
    mapping::MappingExp
    transform::TransformExp
    options::Vector{Tuple{String,String}}
end

struct TransformUnit <: TransformExp
    mapping::MappingExp
    instance::InstanceExp
    options::Vector{Tuple{String,String}}
end

struct TransformCounit <: TransformExp
    mapping::MappingExp
    instance::InstanceExp
    options::Vector{Tuple{String,String}}
end

struct TransformEval <: TransformExp
    query::Any  # QueryExp (defined later)
    transform::TransformExp
end

struct TransformCoeval <: TransformExp
    query::Any  # QueryExp (defined later)
    transform::TransformExp
end

"""Counit of query adjunction: counit_query Q I [{ options }]"""
struct TransformCounitQuery <: TransformExp
    query::Any  # QueryExp
    instance::InstanceExp
    options::Vector{Tuple{String,String}}
end

"""Unit of query adjunction: unit_query Q I [{ options }]"""
struct TransformUnitQuery <: TransformExp
    query::Any  # QueryExp
    instance::InstanceExp
    options::Vector{Tuple{String,String}}
end

"""Frozen transform: frozen Q lambda var:type. body : rettype"""
struct TransformFrozen <: TransformExp
    query::Any  # QueryExp
    lambda_var::String
    lambda_type::String
    lambda_body::Any  # RawTerm
    ret_type::String
end

"""Except transform: except T I"""
struct TransformExcept <: TransformExp
    transform::TransformExp
    instance::InstanceExp
end

"""Except return: except_return I1 I2"""
struct TransformExceptReturn <: TransformExp
    inst1::InstanceExp
    inst2::InstanceExp
end

"""Include transform: include I1 I2"""
struct TransformInclude <: TransformExp
    inst1::InstanceExp
    inst2::InstanceExp
end

"""Distinct transform: distinct T"""
struct TransformDistinctTransform <: TransformExp
    transform::TransformExp
end

"""Distinct return: distinct_return I"""
struct TransformDistinctReturn <: TransformExp
    instance::InstanceExp
end

"""Pi transform: pi mapping transform [{ options }]"""
struct TransformPi <: TransformExp
    mapping::Any  # MappingExp
    transform::TransformExp
    options::Vector{Tuple{String,String}}
end

function deps(e::TransformExp)::Vector{Tuple{String,Kind}}
    if e isa TransformVar
        [(e.name, TRANSFORM)]
    elseif e isa TransformId
        deps(e.instance)
    elseif e isa TransformComp
        vcat(deps(e.first), deps(e.second))
    elseif e isa TransformRawExp
        vcat(deps(e.src_ref), deps(e.dst_ref), vcat([deps(i) for i in e.imports]...))
    elseif e isa TransformDeltaExp
        vcat(deps(e.mapping), deps(e.transform))
    elseif e isa TransformSigmaExp
        vcat(deps(e.mapping), deps(e.transform))
    elseif e isa TransformUnit
        vcat(deps(e.mapping), deps(e.instance))
    elseif e isa TransformCounit
        vcat(deps(e.mapping), deps(e.instance))
    elseif e isa TransformEval
        vcat(deps(e.query), deps(e.transform))
    elseif e isa TransformCoeval
        vcat(deps(e.query), deps(e.transform))
    elseif e isa TransformCounitQuery
        vcat(deps(e.query), deps(e.instance))
    elseif e isa TransformUnitQuery
        vcat(deps(e.query), deps(e.instance))
    elseif e isa TransformFrozen
        deps(e.query)
    elseif e isa TransformExcept
        vcat(deps(e.transform), deps(e.instance))
    elseif e isa TransformExceptReturn
        vcat(deps(e.inst1), deps(e.inst2))
    elseif e isa TransformInclude
        vcat(deps(e.inst1), deps(e.inst2))
    elseif e isa TransformDistinctTransform
        deps(e.transform)
    elseif e isa TransformDistinctReturn
        deps(e.instance)
    elseif e isa TransformPi
        vcat(deps(e.mapping), deps(e.transform))
    else
        Tuple{String,Kind}[]
    end
end
