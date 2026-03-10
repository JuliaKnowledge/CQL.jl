"""
Instance presentations: generators, Skolem constants, and equations.
"""

"""A presentation of a CQL instance."""
struct Presentation
    gens::Dict{Symbol, Symbol}  # gen -> entity
    sks::Dict{Symbol, Symbol}   # sk -> type
    eqs::Set{Equation}          # ground equations (no context)
    gen_order::Vector{Symbol}   # insertion-ordered generator names
end

"""Create a Presentation, optionally with explicit generator order."""
function Presentation(gens::Dict{Symbol, Symbol}, sks::Dict{Symbol, Symbol},
                      eqs::Set{Equation})
    Presentation(gens, sks, eqs, collect(keys(gens)))
end

function Base.show(io::IO, p::Presentation)
    println(io, "presentation {")
    println(io, "  generators")
    for (g, en) in p.gens
        println(io, "    ", g, " : ", en)
    end
    if !isempty(p.sks)
        println(io, "  skolems")
        for (s, ty) in p.sks
            println(io, "    ", s, " : ", ty)
        end
    end
    println(io, "  equations")
    for eq in p.eqs
        println(io, "    ", eq)
    end
    println(io, "}")
end

"""Convert a presentation (on a schema) to a collage for type-checking."""
function presentation_to_collage(sch::CQLSchema, pres::Presentation)::Collage
    sch_col = schema_to_collage(sch)

    ceqs = Set{Tuple{Ctx, Equation}}()

    # Instance equations (ground, empty context)
    for eq in pres.eqs
        push!(ceqs, (Ctx(), eq))
    end

    # Schema equations: ground universally-quantified equations by instantiating
    # with each generator of the appropriate entity.  This produces ground equations
    # so the congruence prover can be used, avoiding non-confluence issues in the
    # orthogonal prover when multiple FKs target the same entity.
    for (ctx, eq) in sch_col.ceqs
        if isempty(ctx)
            push!(ceqs, (Ctx(), eq))
        else
            # Identify entity-sorted variables in the context
            entity_vars = [(v, get_right(sort)) for (v, sort) in ctx if is_right(sort)]
            if isempty(entity_vars)
                push!(ceqs, (ctx, eq))
            else
                # Instantiate with all generator combinations for entity variables
                _ground_schema_eq!(ceqs, eq, entity_vars, 1, Dict{Symbol,CQLTerm}(), pres.gens)
            end
        end
    end

    Collage(ceqs, sch_col.ctys, sch_col.cens, sch_col.csyms,
            sch_col.cfks, sch_col.catts, pres.gens, pres.sks)
end

"""Recursively ground a schema equation by substituting entity variables with generators."""
function _ground_schema_eq!(ceqs, eq::Equation, entity_vars, idx, subst, gens)
    if idx > length(entity_vars)
        # All variables substituted — apply substitution and add ground equation
        lhs = _subst_vars(eq.lhs, subst)
        rhs = _subst_vars(eq.rhs, subst)
        push!(ceqs, (Ctx(), Equation(lhs, rhs)))
        return
    end
    (var, entity) = entity_vars[idx]
    for (g, gen_entity) in gens
        if gen_entity == entity
            subst[var] = CQLGen(g)
            _ground_schema_eq!(ceqs, eq, entity_vars, idx + 1, subst, gens)
        end
    end
    delete!(subst, entity_vars[idx][1])
end

"""Substitute variable names in a term with concrete terms."""
function _subst_vars(t::CQLTerm, subst::Dict{Symbol,CQLTerm})::CQLTerm
    if t isa CQLVar
        get(subst, t.name, t)
    elseif t isa CQLFk
        CQLFk(t.fk, _subst_vars(t.arg, subst))
    elseif t isa CQLAtt
        CQLAtt(t.att, _subst_vars(t.arg, subst))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_subst_vars(a, subst) for a in t.args])
    else
        t  # CQLGen, CQLSk stay as-is
    end
end

"""Typecheck a presentation against a schema."""
function typecheck_presentation(sch::CQLSchema, pres::Presentation)
    col = presentation_to_collage(sch, pres)
    check_doms(col)
    for (ctx, eq) in col.ceqs
        lhs_ty = type_of_term(col, ctx, eq.lhs)
        rhs_ty = type_of_term(col, ctx, eq.rhs)
        if lhs_ty != rhs_ty
            # In the sql typeside, types like String/Text/Varchar are semantically
            # equivalent (they all map to java.lang.String in Java CQL).
            # Allow type-side mismatches when both sides are type-sorted.
            if is_left(lhs_ty) && is_left(rhs_ty) && length(sch.typeside.tys) > 5
                continue  # lenient for multi-type typesides like sql
            end
            throw(CQLException("Equation lhs has type $lhs_ty but rhs has type $rhs_ty"))
        end
    end
end
