"""
Collage: a unified theory for typechecking CQL expressions.

A Collage combines types, entities, function symbols, foreign keys, attributes,
generators, and Skolem constants into a single structure used for typechecking
and theorem proving.
"""

"""A Collage (unified theory representation)."""
struct Collage
    ceqs::Set{Tuple{Ctx, Equation}}   # equations with contexts
    ctys::Set{Symbol}                  # types
    cens::Set{Symbol}                  # entities
    csyms::Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}  # sym -> ([arg types], ret type)
    cfks::Dict{Symbol, Tuple{Symbol, Symbol}}            # fk -> (src entity, tgt entity)
    catts::Dict{Symbol, Tuple{Symbol, Symbol}}           # att -> (src entity, tgt type)
    cgens::Dict{Symbol, Symbol}                          # gen -> entity
    csks::Dict{Symbol, Symbol}                           # sk -> type
end

"""Create an empty collage."""
function empty_collage()
    Collage(
        Set{Tuple{Ctx, Equation}}(),
        Set{Symbol}(),
        Set{Symbol}(),
        Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}(),
        Dict{Symbol, Tuple{Symbol, Symbol}}(),
        Dict{Symbol, Tuple{Symbol, Symbol}}(),
        Dict{Symbol, Symbol}(),
        Dict{Symbol, Symbol}(),
    )
end

"""Count head symbol occurrences across all equations in a collage."""
function collage_occs(col::Collage)::Dict{Head,Int}
    result = Dict{Head,Int}()
    for (_, eq) in col.ceqs
        for t in (eq.lhs, eq.rhs)
            for (h, c) in occs_term(t)
                result[h] = get(result, h, 0) + c
            end
        end
    end
    result
end

"""Check if all equations in the collage are ground (no variables in context)."""
function eqs_are_ground(col::Collage)::Bool
    all(isempty(ctx) for (ctx, _) in col.ceqs)
end

"""Get foreign keys originating from a given entity."""
function fks_from(col::Collage, en::Symbol)
    [(fk, tgt) for (fk, (src, tgt)) in col.cfks if src == en]
end

"""Get attributes originating from a given entity."""
function atts_from(col::Collage, en::Symbol)
    [(att, ty) for (att, (src, ty)) in col.catts if src == en]
end

# ============================================================================
# Type checking
# ============================================================================

"""Get the sort (type or entity) of a term in context."""
function type_of_term(col::Collage, ctx::Ctx, t::CQLTerm)::Either{Symbol,Symbol}
    if t isa CQLVar
        haskey(ctx, t.name) || throw(CQLException("Unbound variable: $(t.name)"))
        return ctx[t.name]
    elseif t isa CQLGen
        haskey(col.cgens, t.gen) || throw(CQLException("Unknown generator: $(t.gen)"))
        return Right(col.cgens[t.gen])
    elseif t isa CQLSk
        haskey(col.csks, t.sk) || throw(CQLException("Unknown labelled null: $(t.sk)"))
        return Left(col.csks[t.sk])
    elseif t isa CQLFk
        haskey(col.cfks, t.fk) || throw(CQLException("Unknown foreign key: $(t.fk)"))
        (src, tgt) = col.cfks[t.fk]
        s = type_of_term(col, ctx, t.arg)
        s == Right(src) || throw(CQLException("Expected argument to have entity $src but given $s in $t"))
        return Right(tgt)
    elseif t isa CQLAtt
        haskey(col.catts, t.att) || throw(CQLException("Unknown attribute: $(t.att)"))
        (src, tgt) = col.catts[t.att]
        s = type_of_term(col, ctx, t.arg)
        s == Right(src) || throw(CQLException("Expected argument to have entity $src but given $s in $t"))
        return Left(tgt)
    elseif t isa CQLSym
        haskey(col.csyms, t.sym) || throw(CQLException("Unknown function symbol: $(t.sym)"))
        (arg_tys, ret_ty) = col.csyms[t.sym]
        length(t.args) == length(arg_tys) || throw(CQLException(
            "Expected arity $(length(arg_tys)) but given $(length(t.args)) in $t"))
        for (a, expected_ty) in zip(t.args, arg_tys)
            actual = type_of_term(col, ctx, a)
            actual == Left(expected_ty) || throw(CQLException(
                "Expected argument type $expected_ty but given $actual in $t"))
        end
        return Left(ret_ty)
    else
        error("Unknown term type in type_of_term")
    end
end

"""Get the entity type of a ground entity-side term (no variables, no type-side constructors)."""
function type_of_entity_term(col::Collage, t::CQLTerm)::Symbol
    result = type_of_term(col, Ctx(), t)
    is_right(result) || error("Expected entity-sort term but got type-sort in type_of_entity_term")
    get_right(result)
end

"""Type-check an equation in context."""
function type_of_eq(col::Collage, ctx::Ctx, eq::Equation)
    lhs_ty = type_of_term(col, ctx, eq.lhs)
    rhs_ty = type_of_term(col, ctx, eq.rhs)
    lhs_ty == rhs_ty || throw(CQLException(
        "Equation lhs has type $lhs_ty but rhs has type $rhs_ty"))
    lhs_ty
end

"""Check that all domain references in a collage are valid."""
function check_doms(col::Collage)
    for (_, (arg_tys, ret_ty)) in col.csyms
        for ty in arg_tys
            ty in col.ctys || throw(CQLException("Not a type: $ty"))
        end
        ret_ty in col.ctys || throw(CQLException("Not a type: $ret_ty"))
    end
    for (_, (s, t)) in col.cfks
        s in col.cens || throw(CQLException("Not an entity: $s"))
        t in col.cens || throw(CQLException("Not an entity: $t"))
    end
    for (_, (e, t)) in col.catts
        e in col.cens || throw(CQLException("Not an entity: $e"))
        t in col.ctys || throw(CQLException("Not a type: $t"))
    end
    for (_, en) in col.cgens
        en in col.cens || throw(CQLException("Not an entity: $en"))
    end
    for (_, ty) in col.csks
        ty in col.ctys || throw(CQLException("Not a type: $ty"))
    end
end

"""Typecheck an entire collage: check domains and all equations."""
function typecheck_collage(col::Collage)
    check_doms(col)
    for (ctx, eq) in col.ceqs
        type_of_eq(col, ctx, eq)
    end
end

# ============================================================================
# Simplification
# ============================================================================

"""Simplify a collage by eliminating equations of the form gen/sk = term.
Returns (simplified_collage, list_of_replacements)."""
function simplify_collage(col::Collage)
    (new_eqs, replacements) = simplify_theory(col.ceqs)
    removed_gens = Set{Symbol}()
    removed_sks = Set{Symbol}()
    for (h, _) in replacements
        if h.kind == H_GEN
            push!(removed_gens, h.name)
        elseif h.kind == H_SK
            push!(removed_sks, h.name)
        end
    end
    new_cgens = Dict(k => v for (k, v) in col.cgens if !(k in removed_gens))
    new_csks = Dict(k => v for (k, v) in col.csks if !(k in removed_sks))
    (Collage(new_eqs, col.ctys, col.cens, col.csyms, col.cfks, col.catts, new_cgens, new_csks),
     replacements)
end

# ============================================================================
# Carrier assembly (for initial algebra construction)
# ============================================================================

"""Assemble generator terms by entity, building carrier sets."""
function assemble_gens(col::Collage, carriers::Vector{CQLTerm})::Dict{Symbol, Set{CQLTerm}}
    result = Dict{Symbol, Set{CQLTerm}}(en => Set{CQLTerm}() for en in col.cens)
    for c in carriers
        en = type_of_entity_term(col, c)
        push!(result[en], c)
    end
    result
end

# ============================================================================
# Sort inhabitation check
# ============================================================================

"""Check if all sorts (entities and types) in a collage are inhabited."""
function all_sorts_inhabited(col::Collage)::Bool
    # Initialize: entities/types inhabited if they have direct generators/skolems
    en_inhabited = Dict(en => false for en in col.cens)
    ty_inhabited = Dict(ty => false for ty in col.ctys)

    for (_, en) in col.cgens
        en_inhabited[en] = true
    end
    for (_, ty) in col.csks
        ty_inhabited[ty] = true
    end

    # Fixed point: close under fks, atts, syms
    changed = true
    while changed
        changed = false
        for (_, (src, _tgt)) in col.cfks
            if get(en_inhabited, src, false)
                # FK can produce tgt, but doesn't inhabit new entity per se
                # Actually FK from inhabited entity means entity is reachable but carrier is entity
            end
        end
        for (_, (en, ty)) in col.catts
            if get(en_inhabited, en, false) && !get(ty_inhabited, ty, false)
                ty_inhabited[ty] = true
                changed = true
            end
        end
        for (_, (arg_tys, ret_ty)) in col.csyms
            if all(get(ty_inhabited, ty, false) for ty in arg_tys) && !get(ty_inhabited, ret_ty, false)
                ty_inhabited[ret_ty] = true
                changed = true
            end
        end
    end

    all(values(en_inhabited)) && all(values(ty_inhabited))
end
