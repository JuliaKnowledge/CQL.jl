"""
Constraints and the chase algorithm.

An ED (Equality/Tuple Generating Dependency) has the form:
    forall x:E1, y:E2 where <premises> -> where <conclusions>         (EGD)
    forall x:E1 where <premises> -> exists z:E3 where <conclusions>   (TGD)

The chase repeatedly finds ED violations and adds the implied equations
(or fresh Skolem generators for TGDs) until a fixed point is reached.
"""

# ============================================================================
# Data structures
# ============================================================================

"""A single equality or tuple generating dependency."""
struct EGD
    vars::Vector{Tuple{Symbol, Symbol}}           # (var_name, entity) universal pairs
    premises::Vector{Equation}                     # where-clause equations (using CQLVar for vars)
    exists_vars::Vector{Tuple{Symbol, Symbol}}     # (var_name, entity) existential pairs (empty for EGDs)
    conclusions::Vector{Equation}                  # conclusion equations
end

"""Check if an ED is a TGD (has existential variables)."""
is_tgd(egd::EGD) = !isempty(egd.exists_vars)

"""A set of constraints on a schema."""
struct CQLConstraints
    schema::CQLSchema
    egds::Vector{EGD}
end

# ============================================================================
# Expression types
# ============================================================================

struct ConstraintsRawExp
    schema_ref::SchemaExp
    raw_egds::Vector{Any}
    options::Vector{Tuple{String,String}}
    imports::Vector{Any}  # Constraint name references
    sigma_mapping::Any    # MappingExp or nothing — for sigma constraints
end

# Backward-compatible constructors
function ConstraintsRawExp(schema_ref, raw_egds, options)
    ConstraintsRawExp(schema_ref, raw_egds, options, Any[], nothing)
end
function ConstraintsRawExp(schema_ref, raw_egds, options, imports)
    ConstraintsRawExp(schema_ref, raw_egds, options, imports, nothing)
end

struct InstanceChase <: InstanceExp
    constraints::Any  # String (name ref) or constraints expression
    instance::InstanceExp
    options::Vector{Tuple{String,String}}
end

"""Empty constraints: empty : schema"""
struct ConstraintsEmpty
    schema_ref::SchemaExp
end

"""Include constraints: include schema old new [{ options }]"""
struct ConstraintsInclude
    schema_ref::SchemaExp
    old_name::String
    new_name::String
    options::Vector{Tuple{String,String}}
end

"""Constraints from schema: fromSchema schema"""
struct ConstraintsFromSchema
    schema_ref::SchemaExp
end

function deps(e::ConstraintsFromSchema)::Vector{Tuple{String,Kind}}
    deps(e.schema_ref)
end

function deps(e::ConstraintsRawExp)::Vector{Tuple{String,Kind}}
    d = deps(e.schema_ref)
    # For 'all' constraints, imports reference instances, not constraints
    sch_name = e.schema_ref isa SchemaVar ? e.schema_ref.name : ""
    if sch_name == "__all_dummy__"
        for imp in e.imports
            push!(d, (imp, INSTANCE))
        end
    else
        for imp in e.imports
            push!(d, (imp, CONSTRAINTS))
        end
    end
    # For sigma constraints, add mapping dependencies
    if e.sigma_mapping !== nothing && e.sigma_mapping isa MappingExp
        append!(d, deps(e.sigma_mapping))
    end
    d
end

function deps(e::InstanceChase)::Vector{Tuple{String,Kind}}
    d = deps(e.instance)
    if e.constraints isa String
        push!(d, (e.constraints, CONSTRAINTS))
    elseif e.constraints isa ConstraintsRawExp || e.constraints isa ConstraintsEmpty || e.constraints isa ConstraintsInclude || e.constraints isa ConstraintsFromSchema
        append!(d, deps(e.constraints))
    end
    d
end

function deps(e::ConstraintsEmpty)::Vector{Tuple{String,Kind}}
    deps(e.schema_ref)
end

function deps(e::ConstraintsInclude)::Vector{Tuple{String,Kind}}
    deps(e.schema_ref)
end

# ============================================================================
# Constraint evaluation
# ============================================================================

"""Evaluate raw constraints into CQLConstraints."""
function eval_constraints_raw(sch::CQLSchema, raw::ConstraintsRawExp,
                               imported_constraints::Vector{CQLConstraints}=CQLConstraints[])::CQLConstraints
    fk_names = collect(keys(sch.fks))
    att_names = collect(keys(sch.atts))
    syms = sch.typeside.syms

    egds = EGD[]
    # Add imported constraints
    for imp in imported_constraints
        append!(egds, imp.egds)
    end
    for raw_egd in raw.raw_egds
        # Parser returns 5-tuple: (vars, premises, exists_vars, conclusions, is_unique)
        is_unique = false
        if length(raw_egd) == 3
            # Backward compat: old 3-tuple format (no exists)
            (vars_raw, premise_eqs_raw, conclusion_eqs_raw) = raw_egd
            exists_vars_raw = Tuple{String,String}[]
        elseif length(raw_egd) == 4
            (vars_raw, premise_eqs_raw, exists_vars_raw, conclusion_eqs_raw) = raw_egd
        else
            (vars_raw, premise_eqs_raw, exists_vars_raw, conclusion_eqs_raw, is_unique) = raw_egd
        end

        # Parse universal variable bindings
        vars = Tuple{Symbol, Symbol}[(Symbol(v), Symbol(e)) for (v, e) in vars_raw]
        var_names = Set{String}(v for (v, _) in vars_raw)

        # Parse existential variable bindings
        exists_vars = Tuple{Symbol, Symbol}[(Symbol(v), Symbol(e)) for (v, e) in exists_vars_raw]
        all_var_names = union(var_names, Set{String}(v for (v, _) in exists_vars_raw))

        # Build var -> entity mapping for FK resolution
        var_entities = Dict{Symbol, Symbol}()
        for (v, e) in vars
            var_entities[v] = e
        end
        for (v, e) in exists_vars
            var_entities[v] = e
        end

        # Parse premise equations
        premises = Equation[]
        for (lhs_raw, rhs_raw) in premise_eqs_raw
            lhs = _trans_constraint_term(sch, var_names, fk_names, att_names, syms, lhs_raw; var_entities=var_entities)
            rhs = _trans_constraint_term(sch, var_names, fk_names, att_names, syms, rhs_raw; var_entities=var_entities)
            push!(premises, Equation(lhs, rhs))
        end

        # Parse conclusion equations (may reference both universal and existential vars)
        conclusions = Equation[]
        for (lhs_raw, rhs_raw) in conclusion_eqs_raw
            lhs = _trans_constraint_term(sch, all_var_names, fk_names, att_names, syms, lhs_raw; var_entities=var_entities)
            rhs = _trans_constraint_term(sch, all_var_names, fk_names, att_names, syms, rhs_raw; var_entities=var_entities)
            push!(conclusions, Equation(lhs, rhs))
        end

        push!(egds, EGD(vars, premises, exists_vars, conclusions))

        # For "exists unique", generate a uniqueness EGD:
        # forall <vars>, <exists_var1>, <exists_var2>
        #   where <premises> AND <conclusions>[v->v1] AND <conclusions>[v->v2]
        #   -> v1 = v2
        if is_unique && !isempty(exists_vars)
            for (ev, een) in exists_vars
                ev1 = Symbol(string(ev, "1"))
                ev2 = Symbol(string(ev, "2"))
                uniq_vars = copy(vars)
                push!(uniq_vars, (ev1, een))
                push!(uniq_vars, (ev2, een))
                uniq_premises = copy(premises)
                # Add conclusion equations for both copies
                for ceq in conclusions
                    push!(uniq_premises, _subst_var_eq(ceq, ev, ev1))
                    push!(uniq_premises, _subst_var_eq(ceq, ev, ev2))
                end
                uniq_conclusions = Equation[Equation(CQLVar(ev1), CQLVar(ev2))]
                push!(egds, EGD(uniq_vars, uniq_premises, Tuple{Symbol,Symbol}[], uniq_conclusions))
            end
        end
    end

    CQLConstraints(sch, egds)
end

"""Substitute a variable name in an equation."""
function _subst_var_eq(eq::Equation, old_var::Symbol, new_var::Symbol)::Equation
    Equation(_subst_var_term(eq.lhs, old_var, new_var),
             _subst_var_term(eq.rhs, old_var, new_var))
end
function _subst_var_term(t::CQLTerm, old_var::Symbol, new_var::Symbol)::CQLTerm
    if t isa CQLVar
        t.name == old_var ? CQLVar(new_var) : t
    elseif t isa CQLFk
        CQLFk(t.fk, _subst_var_term(t.arg, old_var, new_var))
    elseif t isa CQLAtt
        CQLAtt(t.att, _subst_var_term(t.arg, old_var, new_var))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_subst_var_term(a, old_var, new_var) for a in t.args])
    else
        t
    end
end

"""Translate a raw term in constraint context (variables are entities, not generators)."""
function _trans_constraint_term(sch, var_names, fk_names, att_names, syms, raw::RawTerm;
                                 var_entities::Union{Dict,Nothing}=nothing)::CQLTerm
    s = Symbol(raw.head)
    if isempty(raw.args) && raw.head in var_names
        return CQLVar(s)
    elseif length(raw.args) == 1 && s in fk_names
        return CQLFk(s, _trans_constraint_term(sch, var_names, fk_names, att_names, syms, raw.args[1]; var_entities=var_entities))
    elseif length(raw.args) == 1 && s in att_names
        return CQLAtt(s, _trans_constraint_term(sch, var_names, fk_names, att_names, syms, raw.args[1]; var_entities=var_entities))
    elseif length(raw.args) == 1 && has_fk(sch, s)
        # Handle qualified FK names
        inner = _trans_constraint_term(sch, var_names, fk_names, att_names, syms, raw.args[1]; var_entities=var_entities)
        # Try to determine entity from inner term
        inner_en = _entity_of_constraint_term(sch, inner, var_entities)
        if inner_en !== nothing
            qname = resolve_fk(sch, s, inner_en)
            return CQLFk(qname, inner)
        end
        # Fallback: try first candidate
        candidates = fk_candidates(sch, s)
        !isempty(candidates) && return CQLFk(candidates[1], inner)
        throw(CQLException("Cannot resolve FK: $(raw.head)"))
    elseif length(raw.args) == 1 && has_att(sch, s)
        inner = _trans_constraint_term(sch, var_names, fk_names, att_names, syms, raw.args[1]; var_entities=var_entities)
        inner_en = _entity_of_constraint_term(sch, inner, var_entities)
        if inner_en !== nothing
            qname = resolve_att(sch, s, inner_en)
            return CQLAtt(qname, inner)
        end
        candidates = att_candidates(sch, s)
        !isempty(candidates) && return CQLAtt(candidates[1], inner)
        throw(CQLException("Cannot resolve attribute: $(raw.head)"))
    elseif haskey(syms, s)
        return CQLSym(s, CQLTerm[_trans_constraint_term(sch, var_names, fk_names, att_names, syms, a; var_entities=var_entities) for a in raw.args])
    else
        throw(CQLException("Cannot type constraint term: $(raw.head)"))
    end
end

"""Determine the entity of a constraint term."""
function _entity_of_constraint_term(sch, t::CQLTerm, var_entities)::Union{Symbol, Nothing}
    if t isa CQLVar && var_entities !== nothing
        return get(var_entities, t.name, nothing)
    elseif t isa CQLFk
        haskey(sch.fks, t.fk) && return sch.fks[t.fk][2]
        return nothing
    else
        return nothing
    end
end

# ============================================================================
# Chase algorithm
# ============================================================================

# Global counter for Skolem generators
const _chase_sk_counter = Ref(0)

"""Run the chase algorithm: apply constraints to an instance until fixed point."""
function chase(constraints::CQLConstraints, inst::CQLInstance, opts::CQLOptions;
               max_iters::Int=100)::CQLInstance
    current = inst
    sch = constraints.schema
    _chase_sk_counter[] = 0

    for iter in 1:max_iters
        new_eqs = Set{Equation}()
        new_gens = Dict{Symbol, Symbol}()
        alg = current.algebra

        for egd in constraints.egds
            if is_tgd(egd)
                _chase_tgd!(new_eqs, new_gens, egd, alg, sch, current.dp, current.pres)
            else
                _chase_egd!(new_eqs, egd, alg, sch, current.dp)
            end
        end

        if isempty(new_eqs) && isempty(new_gens)
            return current
        end

        # Merge new equations and generators with current presentation
        merged_gens = merge(copy(current.pres.gens), new_gens)
        merged_eqs = union(current.pres.eqs, new_eqs)
        # Preserve gen_order: current order + new gens appended
        merged_order = copy(current.pres.gen_order)
        for g in keys(new_gens)
            g in merged_order || push!(merged_order, g)
        end
        pres = Presentation(
            merged_gens,
            copy(current.pres.sks),
            merged_eqs,
            merged_order,
        )

        col = presentation_to_collage(sch, pres)
        prover, canonical = create_prover_with_canonical(col, opts)
        dp_fn = eq -> prover(Ctx(), eq)

        current = initial_instance(pres, dp_fn, sch)
    end

    throw(CQLException("Chase did not converge after $max_iters iterations"))
end

"""Extract variable names referenced in a constraint term."""
function _term_vars(t::CQLTerm, vars::Set{Symbol}=Set{Symbol}())::Set{Symbol}
    if t isa CQLVar
        push!(vars, t.name)
    elseif t isa CQLFk
        _term_vars(t.arg, vars)
    elseif t isa CQLAtt
        _term_vars(t.arg, vars)
    elseif t isa CQLSym
        for a in t.args
            _term_vars(a, vars)
        end
    end
    vars
end

"""Precompute premise groups: premise_groups[i] = premises checkable after assigning var i."""
function _compute_premise_groups(premises::Vector{Equation}, var_names::Vector{Symbol})
    n = length(var_names)
    var_idx = Dict{Symbol,Int}(v => i for (i, v) in enumerate(var_names))
    groups = [Equation[] for _ in 1:n+1]  # groups[n+1] for premises needing all vars

    for eq in premises
        vars = _term_vars(eq.lhs)
        _term_vars(eq.rhs, vars)
        if isempty(vars)
            push!(groups[1], eq)  # constant premise, check at first level
        else
            # This premise can be checked after the last variable it references is assigned
            max_idx = maximum(get(var_idx, v, n+1) for v in vars)
            push!(groups[max_idx], eq)
        end
    end
    groups
end

"""Process a single EGD against an algebra, collecting new equations."""
function _chase_egd!(new_eqs::Set{Equation}, egd::EGD,
                     alg::Algebra, sch::CQLSchema, dp::Function)
    # Get carrier sets for each variable's entity
    var_carriers = Vector{Vector{Any}}()
    for (_, en) in egd.vars
        elements = collect(carrier(alg, en))
        push!(var_carriers, elements)
    end

    # If any carrier is empty, no assignments possible
    any(isempty, var_carriers) && return

    # Enumerate all assignments (Cartesian product) with incremental premise checking
    var_names = [v for (v, _) in egd.vars]
    premise_groups = _compute_premise_groups(egd.premises, var_names)
    _enumerate_and_check!(new_eqs, egd, alg, sch, dp, var_names, var_carriers,
                          Dict{Symbol, Any}(), 1, premise_groups)
end

"""Recursively enumerate assignments with incremental premise checking."""
function _enumerate_and_check!(new_eqs, egd, alg, sch, dp, var_names, var_carriers,
                               assignment, idx, premise_groups)
    if idx > length(var_names)
        # Check any remaining premises (those needing all vars)
        _check_premises(premise_groups[idx], assignment, alg, sch) || return
        # Check conclusions - add equation if not already provable
        for ceq in egd.conclusions
            lhs = _ground_term(ceq.lhs, assignment, alg)
            rhs = _ground_term(ceq.rhs, assignment, alg)
            if lhs != rhs && !dp(Equation(lhs, rhs))
                push!(new_eqs, Equation(lhs, rhs))
            end
        end
        return
    end

    vname = var_names[idx]
    for elem in var_carriers[idx]
        assignment[vname] = elem
        # Check premises that become fully determined after this variable
        _check_premises(premise_groups[idx], assignment, alg, sch) || continue
        _enumerate_and_check!(new_eqs, egd, alg, sch, dp, var_names, var_carriers,
                              assignment, idx + 1, premise_groups)
    end
    delete!(assignment, vname)
end

"""Process a single TGD against an algebra, creating fresh generators when needed."""
function _chase_tgd!(new_eqs::Set{Equation}, new_gens::Dict{Symbol, Symbol},
                     egd::EGD, alg::Algebra, sch::CQLSchema, dp::Function,
                     pres::Presentation)
    # Get carrier sets for each universal variable's entity
    var_carriers = Vector{Vector{Any}}()
    for (_, en) in egd.vars
        elements = collect(carrier(alg, en))
        push!(var_carriers, elements)
    end

    # If any carrier is empty, no assignments possible
    any(isempty, var_carriers) && return

    # Enumerate all assignments of universal vars with incremental premise checking
    var_names = [v for (v, _) in egd.vars]
    premise_groups = _compute_premise_groups(egd.premises, var_names)
    _enumerate_and_check_tgd!(new_eqs, new_gens, egd, alg, sch, dp, pres,
                               var_names, var_carriers, Dict{Symbol, Any}(), 1, premise_groups)
end

"""Recursively enumerate universal assignments and check TGD firing with incremental premises."""
function _enumerate_and_check_tgd!(new_eqs, new_gens, egd, alg, sch, dp, pres,
                                    var_names, var_carriers, assignment, idx, premise_groups)
    if idx > length(var_names)
        # Check any remaining premises
        _check_premises(premise_groups[idx], assignment, alg, sch) || return
        # Check if witnesses already exist for existential vars
        if !_witnesses_exist(egd, assignment, alg, sch; dp=dp)
            # Fire TGD: create fresh Skolem generators for existential vars
            extended = copy(assignment)
            for (var, en) in egd.exists_vars
                _chase_sk_counter[] += 1
                fresh_gen = Symbol("chase_sk_", _chase_sk_counter[])
                new_gens[fresh_gen] = en
                extended[var] = CQLGen(fresh_gen)
            end

            # Ground conclusion equations using extended assignment
            for ceq in egd.conclusions
                lhs = _ground_term_tgd(ceq.lhs, extended, alg)
                rhs = _ground_term_tgd(ceq.rhs, extended, alg)
                if lhs != rhs
                    push!(new_eqs, Equation(lhs, rhs))
                end
            end
        end
        return
    end

    vname = var_names[idx]
    for elem in var_carriers[idx]
        assignment[vname] = elem
        # Check premises that become fully determined after this variable
        _check_premises(premise_groups[idx], assignment, alg, sch) || continue
        _enumerate_and_check_tgd!(new_eqs, new_gens, egd, alg, sch, dp, pres,
                                   var_names, var_carriers, assignment, idx + 1, premise_groups)
    end
    delete!(assignment, vname)
end

"""Check if witnesses already exist for existential variables in a TGD."""
function _witnesses_exist(egd::EGD, assignment::Dict, alg::Algebra, sch::CQLSchema;
                          dp=nothing)::Bool
    # Get carrier sets for each existential variable's entity
    exist_carriers = Vector{Vector{Any}}()
    for (_, en) in egd.exists_vars
        elements = collect(carrier(alg, en))
        push!(exist_carriers, elements)
    end

    # If any carrier is empty, no witnesses possible
    any(isempty, exist_carriers) && return false

    exist_var_names = [v for (v, _) in egd.exists_vars]
    return _search_witnesses(egd, assignment, alg, sch, exist_var_names, exist_carriers,
                              Dict{Symbol, Any}(), 1; dp=dp)
end

"""Recursively search for witness assignments."""
function _search_witnesses(egd, assignment, alg, sch, exist_var_names, exist_carriers,
                            exist_assignment, idx; dp=nothing)::Bool
    if idx > length(exist_var_names)
        # Check if all conclusions hold under combined assignment
        combined = merge(assignment, exist_assignment)
        for ceq in egd.conclusions
            lhs_val = _eval_constraint_term(ceq.lhs, combined, alg)
            rhs_val = _eval_constraint_term(ceq.rhs, combined, alg)
            if lhs_val != rhs_val
                # Try decision procedure for type-level terms
                if dp !== nothing && lhs_val isa CQLTerm && rhs_val isa CQLTerm
                    dp(Equation(lhs_val, rhs_val)) || return false
                else
                    return false
                end
            end
        end
        return true
    end

    vname = exist_var_names[idx]
    for elem in exist_carriers[idx]
        exist_assignment[vname] = elem
        if _search_witnesses(egd, assignment, alg, sch, exist_var_names, exist_carriers,
                              exist_assignment, idx + 1; dp=dp)
            delete!(exist_assignment, vname)
            return true
        end
    end
    delete!(exist_assignment, vname)
    return false
end

"""Ground a TGD constraint term: substitute variables. Existential vars map to CQLGen terms."""
function _ground_term_tgd(t::CQLTerm, assignment::Dict, alg::Algebra)::CQLTerm
    if t isa CQLVar
        val = assignment[t.name]
        if val isa CQLTerm
            return val  # existential var already mapped to CQLGen
        else
            return repr_x(alg, val)  # universal var: carrier element -> term
        end
    elseif t isa CQLFk
        inner = _ground_term_tgd(t.arg, assignment, alg)
        return CQLFk(t.fk, inner)
    elseif t isa CQLAtt
        inner = _ground_term_tgd(t.arg, assignment, alg)
        return CQLAtt(t.att, inner)
    elseif t isa CQLSym
        return CQLSym(t.sym, CQLTerm[_ground_term_tgd(a, assignment, alg) for a in t.args])
    elseif t isa CQLGen
        return t
    elseif t isa CQLSk
        return t
    else
        error("Cannot ground TGD term: $t")
    end
end

"""Check if all premises hold under the given assignment."""
function _check_premises(premises::Vector{Equation}, assignment::Dict,
                         alg::Algebra, sch::CQLSchema)::Bool
    for eq in premises
        lhs_val = _eval_constraint_term(eq.lhs, assignment, alg)
        rhs_val = _eval_constraint_term(eq.rhs, assignment, alg)
        lhs_val == rhs_val || return false
    end
    true
end

"""Evaluate a constraint term under an assignment, returning a carrier element or type term."""
function _eval_constraint_term(t::CQLTerm, assignment::Dict, alg::Algebra)
    if t isa CQLVar
        return assignment[t.name]
    elseif t isa CQLFk
        inner = _eval_constraint_term(t.arg, assignment, alg)
        return eval_fk(alg, t.fk, inner)
    elseif t isa CQLAtt
        inner = _eval_constraint_term(t.arg, assignment, alg)
        return eval_att(alg, t.att, inner)
    elseif t isa CQLSym
        args = [_eval_constraint_term(a, assignment, alg) for a in t.args]
        return CQLSym(t.sym, CQLTerm[a isa CQLTerm ? a : error("Bad sym arg") for a in args])
    elseif t isa CQLGen
        return alg.gen[t.gen]
    elseif t isa CQLSk
        return alg.nf_y(Left(t.sk))
    else
        error("Cannot evaluate constraint term: $t")
    end
end

"""Ground a constraint term: substitute variables with repr_x(alg, element)."""
function _ground_term(t::CQLTerm, assignment::Dict, alg::Algebra)::CQLTerm
    if t isa CQLVar
        elem = assignment[t.name]
        return repr_x(alg, elem)
    elseif t isa CQLFk
        inner = _ground_term(t.arg, assignment, alg)
        return CQLFk(t.fk, inner)
    elseif t isa CQLAtt
        inner = _ground_term(t.arg, assignment, alg)
        return CQLAtt(t.att, inner)
    elseif t isa CQLSym
        return CQLSym(t.sym, CQLTerm[_ground_term(a, assignment, alg) for a in t.args])
    elseif t isa CQLGen
        return t
    elseif t isa CQLSk
        return t
    else
        error("Cannot ground term: $t")
    end
end

