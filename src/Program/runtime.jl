# ============================================================================
# Program evaluation
# ============================================================================

"""Evaluate a single declaration and add its result to the environment."""
function eval_exp!(env::Env, e::Exp)
    try
        if e.kind == TYPESIDE
            env.typesides[e.name] = eval_typeside(env, e.body)
        elseif e.kind == SCHEMA
            env.schemas[e.name] = eval_schema(env, e.body)
        elseif e.kind == INSTANCE
            env.instances[e.name] = eval_instance(env, e.body)
        elseif e.kind == MAPPING
            env.mappings[e.name] = eval_mapping(env, e.body)
        elseif e.kind == TRANSFORM
            env.transforms[e.name] = eval_transform(env, e.body)
        elseif e.kind == QUERY
            env.queries[e.name] = eval_query(env, e.body)
        elseif e.kind == SCHEMA_COLIMIT
            env.colimits[e.name] = eval_schema_colimit_exp(env, e.body)
        elseif e.kind == CONSTRAINTS
            env.constraints[e.name] = eval_constraints_exp(env, e.body)
        elseif e.kind == GRAPH
            if e.body !== nothing
                (nodes, edges) = e.body
                env.graphs[e.name] = CQLGraph(nodes, edges)
            end
        elseif e.kind == COMMAND || e.kind == COMMENT
            cmd = e.body
            if cmd isa CommandExecJdbc
                local_opts = env.options
                eval_exec_jdbc(cmd.conn, cmd.sqls, local_opts)
            elseif cmd isa CommandExportJdbc
                haskey(env.instances, cmd.instance_name) || throw(CQLException(
                    "Undefined instance: $(cmd.instance_name)"))
                inst = env.instances[cmd.instance_name]
                local_opts = isempty(cmd.options) ? env.options : to_options(env.options, cmd.options)
                eval_export_jdbc(inst, cmd.conn, cmd.prefix, local_opts)
            elseif cmd isa CommandExecOdbc
                local_opts = env.options
                eval_exec_odbc(cmd.conn, cmd.sqls, local_opts)
            elseif cmd isa CommandExportOdbc
                haskey(env.instances, cmd.instance_name) || throw(CQLException(
                    "Undefined instance: $(cmd.instance_name)"))
                inst = env.instances[cmd.instance_name]
                local_opts = isempty(cmd.options) ? env.options : to_options(env.options, cmd.options)
                eval_export_odbc(inst, cmd.conn, cmd.prefix, local_opts)
            elseif cmd isa CommandExportRdfInstanceXml
                eval_export_rdf_instance_xml(env, cmd.instance_name, cmd.filepath,
                                             cmd.external_types, env.options)
            else
                # CommandSkip or nothing — silently ignore
            end
        else
            throw(CQLException("Unknown kind: $(e.kind)"))
        end
    catch ex
        if ex isa CQLException
            throw(CQLException("Error evaluating $(e.kind) $(e.name): $(ex.msg)"))
        end
        rethrow(ex)
    end
end

"""Evaluate a schema_colimit expression."""
function eval_schema_colimit_exp(env::Env, e)::SchemaColimitResult
    if e isa SchemaColimitLiteralExp
        return _eval_schema_colimit_literal(env, e)
    end
    if e isa SchemaColimitModify
        haskey(env.colimits, e.base_name) || throw(CQLException("Undefined schema_colimit: $(e.base_name)"))
        base = env.colimits[e.base_name]
        # If all rename/remove lists are empty, this is a 'simplify' operation
        if isempty(e.rename_ens) && isempty(e.rename_fks) && isempty(e.rename_atts) &&
           isempty(e.remove_fks) && isempty(e.remove_atts)
            return _simplify_colimit_names(base)
        end
        return eval_modify_colimit(base, e.rename_ens, e.rename_fks, e.rename_atts,
                                    e.remove_fks, e.remove_atts)
    end
    ts = eval_typeside(env, e.typeside_ref)
    schemas = Tuple{String, CQLSchema}[]
    for (name, sexp) in e.schema_refs
        sch = eval_schema(env, sexp)
        push!(schemas, (name, sch))
    end
    result = eval_schema_colimit(env.options, ts, schemas, e.entity_eqs, e.path_eqs;
                                  obs_eqs=e.obs_eqs,
                                  entity_isos=e.entity_isos)
    # Apply simplify_names if requested
    for (k, v) in e.options
        if k == "simplify_names" && lowercase(v) == "true"
            result = _simplify_colimit_names(result)
        end
    end
    result
end

"""Evaluate a literal schema_colimit over a graph diagram."""
function _eval_schema_colimit_literal(env::Env, e::SchemaColimitLiteralExp)::SchemaColimitResult
    haskey(env.graphs, e.graph_name) || throw(CQLException("Undefined graph: $(e.graph_name)"))
    graph = env.graphs[e.graph_name]
    ts = eval_typeside(env, e.typeside_ref)

    # Resolve node -> schema mappings
    node_schemas = Dict{String, CQLSchema}()
    for (node_name, sch_exp) in e.node_map
        node_schemas[node_name] = eval_schema(env, sch_exp)
    end

    # Build schema_refs list (one per graph node)
    schema_refs = Tuple{String, CQLSchema}[]
    for node in graph.nodes
        haskey(node_schemas, node) || throw(CQLException("Graph node '$node' has no schema mapping in colimit"))
        push!(schema_refs, (node, node_schemas[node]))
    end

    # Resolve edge -> mapping
    edge_mappings = Dict{String, CQLMapping}()
    for (edge_name, mapping_exp) in e.edge_map
        edge_mappings[edge_name] = eval_mapping(env, mapping_exp)
    end

    # Build entity equations from edge mappings:
    # For each edge e: src_node -> tgt_node with mapping M: S_src -> S_tgt,
    # for each entity E in S_src: identify src_node.E = tgt_node.M(E)
    entity_eqs = Tuple{String, String}[]
    for (edge_name, (src_node, tgt_node)) in graph.edges
        haskey(edge_mappings, edge_name) || throw(CQLException("Graph edge '$edge_name' has no mapping in colimit"))
        m = edge_mappings[edge_name]
        for (src_en, tgt_en) in m.ens
            push!(entity_eqs, ("$(src_node).$(src_en)", "$(tgt_node).$(tgt_en)"))
        end
    end

    result = eval_schema_colimit(env.options, ts, schema_refs, entity_eqs,
                                  Tuple{RawTerm,RawTerm}[])

    for (k, v) in e.options
        if k == "simplify_names" && lowercase(v) == "true"
            result = _simplify_colimit_names(result)
        end
    end
    result
end

"""Simplify colimit names by stripping schema prefixes where unambiguous."""
function _simplify_colimit_names(result::SchemaColimitResult)::SchemaColimitResult
    sch = result.schema

    # Step 0: Merge attributes equated by observation equations.
    # Obs eqs of form att1(x) = att2(x) mean att1 and att2 are functionally equivalent;
    # remove one and rename references to the survivor.
    att_merge_rename = Dict{Symbol, Symbol}()
    att_merge_remove = Set{Symbol}()
    # Union-find on attribute names
    att_parent = Dict{Symbol, Symbol}()
    function att_find(x)
        haskey(att_parent, x) || (att_parent[x] = x)
        while att_parent[x] != x
            att_parent[x] = att_parent[att_parent[x]]
            x = att_parent[x]
        end
        x
    end
    function att_union!(a, b)
        ra, rb = att_find(a), att_find(b)
        if ra != rb
            if string(ra) <= string(rb)
                att_parent[rb] = ra
            else
                att_parent[ra] = rb
            end
        end
    end

    # Merge attributes equated by obs_eqs
    for (en, eq) in sch.obs_eqs
        if eq.lhs isa CQLAtt && eq.rhs isa CQLAtt &&
           eq.lhs.arg isa CQLVar && eq.rhs.arg isa CQLVar
            a, b = eq.lhs.att, eq.rhs.att
            haskey(sch.atts, a) && haskey(sch.atts, b) || continue
            att_union!(a, b)
        end
    end

    # Step 0c: Build merge rename/remove from union-find
    for att in keys(sch.atts)
        haskey(att_parent, att) || continue
        canonical = att_find(att)
        if att != canonical
            att_merge_rename[att] = canonical
            push!(att_merge_remove, att)
        end
    end
    if !isempty(att_merge_remove)
        merge_rename_atts = [(string(old), string(new_name)) for (old, new_name) in att_merge_rename]
        merge_remove_atts = [(string(att), "") for att in att_merge_remove]
        result = eval_modify_colimit(result, Tuple{String,String}[], Tuple{String,String}[],
                                      merge_rename_atts, Tuple{String,String}[], merge_remove_atts)
        sch = result.schema
    end

    # Step 1: Build entity rename map: strip "SchemaName_" prefix if the suffix is unique
    en_suffix_count = Dict{Symbol, Int}()
    en_full_to_suffix = Dict{Symbol, Symbol}()
    for en in sch.ens
        s = string(en)
        idx = findfirst('_', s)
        suffix = idx !== nothing ? Symbol(s[idx+1:end]) : en
        en_full_to_suffix[en] = suffix
        en_suffix_count[suffix] = get(en_suffix_count, suffix, 0) + 1
    end

    en_rename = Dict{Symbol, Symbol}()
    for en in sch.ens
        suffix = en_full_to_suffix[en]
        if en_suffix_count[suffix] == 1 && suffix != en
            en_rename[en] = suffix
        end
    end

    # Build FK rename map: strip "SchemaName_Entity_" prefix if suffix is unique
    fk_suffix_count = Dict{Symbol, Int}()
    fk_full_to_suffix = Dict{Symbol, Symbol}()
    for fk in keys(sch.fks)
        s = string(fk)
        # Strip both schema and entity prefix (parts[3:end])
        parts = split(s, '_')
        suffix = length(parts) >= 3 ? Symbol(join(parts[3:end], '_')) : fk
        fk_full_to_suffix[fk] = suffix
        fk_suffix_count[suffix] = get(fk_suffix_count, suffix, 0) + 1
    end

    fk_rename = Dict{Symbol, Symbol}()
    for fk in keys(sch.fks)
        suffix = fk_full_to_suffix[fk]
        if fk_suffix_count[suffix] == 1 && suffix != fk
            fk_rename[fk] = suffix
        end
    end

    # Build att rename map: strip "SchemaName_Entity_" prefix if suffix is unique globally,
    # or use entity-qualified name "Entity__Suffix" via greedy assignment (first alphabetically wins)
    att_suffix_count = Dict{Symbol, Int}()
    att_full_to_suffix = Dict{Symbol, Symbol}()
    for att in keys(sch.atts)
        s = string(att)
        # Strip both schema and entity prefix (parts[3:end]) to get base name
        parts = split(s, '_')
        suffix = length(parts) >= 3 ? Symbol(join(parts[3:end], '_')) : att
        att_full_to_suffix[att] = suffix
        att_suffix_count[suffix] = get(att_suffix_count, suffix, 0) + 1
    end

    att_rename = Dict{Symbol, Symbol}()
    # First pass: globally unique suffixes
    for att in keys(sch.atts)
        suffix = att_full_to_suffix[att]
        if att_suffix_count[suffix] == 1 && suffix != att
            att_rename[att] = suffix
        end
    end
    # Second pass: greedy entity-qualified naming for non-unique suffixes
    entity_suffix_taken = Set{Tuple{Symbol,Symbol}}()
    for att in sort(collect(keys(sch.atts)))  # alphabetical order for greedy assignment
        suffix = att_full_to_suffix[att]
        att_suffix_count[suffix] == 1 && continue  # already handled
        entity = sch.atts[att][1]
        display_entity = get(en_rename, entity, entity)
        key = (display_entity, suffix)
        qualified = Symbol(display_entity, :__, suffix)
        if !(key in entity_suffix_taken) && qualified != att
            att_rename[att] = qualified
            push!(entity_suffix_taken, key)
        end
    end

    if isempty(en_rename) && isempty(fk_rename) && isempty(att_rename)
        return result
    end

    # Apply renames using eval_modify_colimit
    rename_ens = [(string(old), string(new_name)) for (old, new_name) in en_rename]
    rename_fks = [(string(old), string(new_name)) for (old, new_name) in fk_rename]
    rename_atts = [(string(old), string(new_name)) for (old, new_name) in att_rename]

    simplified = eval_modify_colimit(result, rename_ens, rename_fks, rename_atts,
                                      Tuple{String,String}[], Tuple{String,String}[])

    # Add original (unprefixed) entity names to entity_canonical so that
    # subsequent modify blocks can reference them (e.g., "Person -> P")
    new_canonical = copy(simplified.entity_canonical)
    for (prefixed, canonical) in simplified.entity_canonical
        s = string(prefixed)
        idx = findfirst('_', s)
        if idx !== nothing
            suffix = Symbol(s[idx+1:end])
            if !haskey(new_canonical, suffix)
                new_canonical[suffix] = canonical
            end
        end
    end
    SchemaColimitResult(simplified.schema, simplified.mappings, simplified.names, new_canonical)
end

"""Evaluate a constraints expression."""
function eval_constraints_exp(env::Env, e)::CQLConstraints
    if e isa ConstraintsEmpty
        sch = eval_schema(env, e.schema_ref)
        return CQLConstraints(sch, EGD[])
    elseif e isa ConstraintsInclude
        sch = eval_schema(env, e.schema_ref)
        return CQLConstraints(sch, EGD[])
    elseif e isa ConstraintsFromSchema
        sch = eval_schema(env, e.schema_ref)
        return CQLConstraints(sch, EGD[])  # fromSchema generates trivial constraints
    end
    return _eval_constraints_raw_exp(env, e)
end

function _eval_constraints_raw_exp(env::Env, e::ConstraintsRawExp)::CQLConstraints
    # Handle dummy schema references from 'all' or 'sigma' constraints
    sch_ref_name = e.schema_ref isa SchemaVar ? e.schema_ref.name : ""
    if sch_ref_name == "__sigma_dummy__" && e.sigma_mapping !== nothing
        # Sigma constraints: transform constraints through mapping
        m = eval_mapping(env, e.sigma_mapping)
        base_name = e.imports[1] isa String ? e.imports[1] : string(e.imports[1])
        haskey(env.constraints, base_name) || throw(CQLException("Undefined constraints: $base_name"))
        base = env.constraints[base_name]
        return _sigma_constraints(m, base)
    end
    if sch_ref_name == "__all_dummy__" || sch_ref_name == "__sigma_dummy__"
        # Try to resolve schema from imported constraints or instances
        for imp in e.imports
            name = imp isa String ? imp : string(imp)
            if haskey(env.constraints, name)
                return env.constraints[name]
            end
            if haskey(env.instances, name)
                # For 'all' constraints: return empty constraints on the instance's schema
                inst = env.instances[name]
                return CQLConstraints(inst.schema, EGD[])
            end
        end
        throw(CQLException("Cannot resolve schema for 'all'/'sigma' constraints"))
    end

    sch = eval_schema(env, e.schema_ref)
    imported = CQLConstraints[]
    for imp in e.imports
        name = imp isa String ? imp : string(imp)
        if haskey(env.constraints, name)
            push!(imported, env.constraints[name])
        end
    end
    eval_constraints_raw(sch, e, imported)
end

"""Transform constraints through a mapping (sigma on constraints)."""
function _sigma_constraints(m::CQLMapping, base::CQLConstraints)::CQLConstraints
    new_egds = EGD[]
    for egd in base.egds
        # Remap entity names for forall and exists variables
        new_vars = Tuple{Symbol,Symbol}[(v, m.ens[en]) for (v, en) in egd.vars]
        new_exists = Tuple{Symbol,Symbol}[(v, m.ens[en]) for (v, en) in egd.exists_vars]
        # Transform terms through the mapping
        new_premises = Equation[Equation(
            _change_en(m.fks, m.atts, eq.lhs),
            _change_en(m.fks, m.atts, eq.rhs)) for eq in egd.premises]
        new_conclusions = Equation[Equation(
            _change_en(m.fks, m.atts, eq.lhs),
            _change_en(m.fks, m.atts, eq.rhs)) for eq in egd.conclusions]
        push!(new_egds, EGD(new_vars, new_premises, new_exists, new_conclusions))
    end
    CQLConstraints(m.dst, new_egds)
end

"""Evaluate an instance coproduct."""
function eval_coproduct_instance(sch::CQLSchema, insts::Vector{CQLInstance}, opts::CQLOptions)::CQLInstance
    merged_gens = Dict{Symbol, Symbol}()
    merged_sks = Dict{Symbol, Symbol}()
    merged_eqs = Set{Equation}()
    merged_gen_order = Symbol[]

    for (k, inst) in enumerate(insts)
        prefix = Symbol("i", k, "_")

        # Prefix generators (entity-level elements are instance-specific)
        gen_rename = Dict{Symbol, Symbol}()
        for g in inst.pres.gen_order
            haskey(inst.pres.gens, g) || continue
            en = inst.pres.gens[g]
            new_g = Symbol(prefix, g)
            gen_rename[g] = new_g
            merged_gens[new_g] = en
            push!(merged_gen_order, new_g)
        end

        # Skolems (type-level constants) are shared across instances — don't prefix.
        # This ensures data values like "alexandra" remain identical across summands.
        sk_rename = Dict{Symbol, Symbol}()
        for (s, ty) in inst.pres.sks
            merged_sks[s] = ty
        end

        # Rewrite equations: only generators get prefixed
        for eq in inst.pres.eqs
            new_lhs = _rename_term(eq.lhs, gen_rename, sk_rename)
            new_rhs = _rename_term(eq.rhs, gen_rename, sk_rename)
            push!(merged_eqs, Equation(new_lhs, new_rhs))
        end
    end

    pres = Presentation(merged_gens, merged_sks, merged_eqs, merged_gen_order)
    typecheck_presentation(sch, pres)

    col = presentation_to_collage(sch, pres)
    prover = create_prover(col, opts)
    dp_fn = eq -> prover(Ctx(), eq)

    initial_instance(pres, dp_fn, sch)
end

"""Rename generators and skolems in a term."""
function _rename_term(t::CQLTerm, gen_map::Dict{Symbol,Symbol}, sk_map::Dict{Symbol,Symbol})::CQLTerm
    if t isa CQLGen
        CQLGen(get(gen_map, t.gen, t.gen))
    elseif t isa CQLSk
        CQLSk(get(sk_map, t.sk, t.sk))
    elseif t isa CQLFk
        CQLFk(t.fk, _rename_term(t.arg, gen_map, sk_map))
    elseif t isa CQLAtt
        CQLAtt(t.att, _rename_term(t.arg, gen_map, sk_map))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_rename_term(a, gen_map, sk_map) for a in t.args])
    elseif t isa CQLVar
        t
    else
        t
    end
end

"""Evaluate a coequalizer of two transforms f, g : I → J.

Produces the quotient of J where f(x) = g(x) for each generator x in I."""
function eval_coequalize(f::CQLTransform, g::CQLTransform, opts::CQLOptions)::CQLInstance
    # Both transforms must have the same source and target
    dst = f.dst  # = g.dst, the target instance J
    sch = dst.schema

    # Collect additional equations: f(x) = g(x) for each generator
    extra_eqs = Set{Equation}()
    for (gen, _) in f.src.pres.gens
        f_term = get(f.gens, gen, CQLGen(gen))
        g_term = get(g.gens, gen, CQLGen(gen))
        if f_term != g_term
            push!(extra_eqs, Equation(f_term, g_term))
        end
    end
    for (sk, _) in f.src.pres.sks
        f_term = get(f.sks, sk, CQLSk(sk))
        g_term = get(g.sks, sk, CQLSk(sk))
        if f_term != g_term
            push!(extra_eqs, Equation(f_term, g_term))
        end
    end

    # Build new presentation with the extra equations
    new_eqs = union(dst.pres.eqs, extra_eqs)
    new_pres = Presentation(dst.pres.gens, dst.pres.sks, new_eqs, copy(dst.pres.gen_order))

    # Rebuild the instance
    col = presentation_to_collage(sch, new_pres)
    prover = create_prover(col, opts)
    dp_fn = eq -> prover(Ctx(), eq)
    initial_instance(new_pres, dp_fn, sch)
end

"""Evaluate a colimit instance over a graph of instances and transforms."""
function eval_colimit_instance(env::Env, graph::CQLGraph, sch::CQLSchema,
                                node_map::Vector{Tuple{String,Any}},
                                edge_map::Vector{Tuple{String,Any}},
                                opts::CQLOptions)::CQLInstance
    # 1. Resolve node instances
    node_instances = Dict{String, CQLInstance}()
    for (node_name, inst_exp) in node_map
        node_instances[node_name] = eval_instance(env, inst_exp)
    end

    # 2. Resolve edge transforms
    edge_transforms = Dict{String, CQLTransform}()
    for (edge_name, tr_exp) in edge_map
        edge_transforms[edge_name] = eval_transform(env, tr_exp)
    end

    # 3. Compute coproduct of all node instances (in graph.nodes order)
    all_insts = CQLInstance[node_instances[n] for n in graph.nodes]
    coprod = eval_coproduct_instance(sch, all_insts, opts)

    # 4. For each edge, add equations identifying elements via transform
    extra_eqs = Set{Equation}()
    for (edge_name, (src_node, tgt_node)) in graph.edges
        haskey(edge_transforms, edge_name) || continue
        t = edge_transforms[edge_name]

        src_idx = findfirst(==(src_node), graph.nodes)
        tgt_idx = findfirst(==(tgt_node), graph.nodes)
        src_idx === nothing && throw(CQLException("Graph edge $edge_name references unknown source node: $src_node"))
        tgt_idx === nothing && throw(CQLException("Graph edge $edge_name references unknown target node: $tgt_node"))

        src_prefix = Symbol("i", src_idx, "_")
        tgt_prefix = Symbol("i", tgt_idx, "_")

        # For each generator in the source instance, build the identification equation
        for (gen, _) in t.src.pres.gens
            t_image = get(t.gens, gen, CQLGen(gen))
            lhs = CQLGen(Symbol(src_prefix, gen))
            rhs = _rename_gen_prefix(t_image, tgt_prefix)
            if lhs != rhs
                push!(extra_eqs, Equation(lhs, rhs))
            end
        end
        # Also handle skolem identifications
        for (sk, _) in t.src.pres.sks
            t_image = get(t.sks, sk, CQLSk(sk))
            lhs = CQLSk(Symbol(src_prefix, sk))
            rhs = _rename_sk_prefix(t_image, tgt_prefix)
            if lhs != rhs
                push!(extra_eqs, Equation(lhs, rhs))
            end
        end
    end

    if isempty(extra_eqs)
        return coprod
    end

    # 5. Build quotient instance with extra equations
    new_eqs = union(coprod.pres.eqs, extra_eqs)
    new_pres = Presentation(coprod.pres.gens, coprod.pres.sks, new_eqs, copy(coprod.pres.gen_order))

    col = presentation_to_collage(sch, new_pres)
    prover = create_prover(col, opts)
    dp_fn = eq -> prover(Ctx(), eq)
    initial_instance(new_pres, dp_fn, sch)
end

"""Rename generator references in a term by prepending a prefix to all gen names."""
function _rename_gen_prefix(t::CQLTerm, prefix::Symbol)::CQLTerm
    if t isa CQLGen
        CQLGen(Symbol(prefix, t.gen))
    elseif t isa CQLFk
        CQLFk(t.fk, _rename_gen_prefix(t.arg, prefix))
    elseif t isa CQLAtt
        CQLAtt(t.att, _rename_gen_prefix(t.arg, prefix))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_rename_gen_prefix(a, prefix) for a in t.args])
    elseif t isa CQLSk
        CQLSk(Symbol(prefix, t.sk))
    else
        t
    end
end

"""Rename skolem references in a term by prepending a prefix."""
function _rename_sk_prefix(t::CQLTerm, prefix::Symbol)::CQLTerm
    if t isa CQLSk
        CQLSk(Symbol(prefix, t.sk))
    elseif t isa CQLGen
        CQLGen(Symbol(prefix, t.gen))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_rename_sk_prefix(a, prefix) for a in t.args])
    else
        t
    end
end

"""Evaluate except (set difference) of two instances: I1 \\ I2.

Keeps generators from I1 whose canonical form does not appear in I2."""
function eval_except_instance(i1::CQLInstance, i2::CQLInstance, opts::CQLOptions)::CQLInstance
    sch = i1.schema

    # Collect the set of generator names that appear in I2
    i2_gens = Set{Symbol}(keys(i2.pres.gens))

    # Find which I1 generators also appear in I2 (by name)
    keep_gens = Dict{Symbol, Symbol}()
    keep_sks = Dict{Symbol, Symbol}()
    for (g, en) in i1.pres.gens
        if !(g in i2_gens)
            keep_gens[g] = en
        end
    end

    # If all generators are kept, return I1 as-is
    if length(keep_gens) == length(i1.pres.gens)
        return i1
    end

    # Keep only skolems referenced by kept generators
    for (s, ty) in i1.pres.sks
        keep_sks[s] = ty
    end

    # Filter equations to only those involving kept generators
    removed_gens = Set{Symbol}(g for (g, _) in i1.pres.gens if !(g in keys(keep_gens)))
    keep_eqs = Set{Equation}()
    for eq in i1.pres.eqs
        if !_term_references_any(eq.lhs, removed_gens) && !_term_references_any(eq.rhs, removed_gens)
            push!(keep_eqs, eq)
        end
    end

    keep_gen_order = Symbol[g for g in i1.pres.gen_order if haskey(keep_gens, g)]
    pres = Presentation(keep_gens, keep_sks, keep_eqs, keep_gen_order)

    if isempty(keep_gens)
        return empty_instance(sch)
    end

    col = presentation_to_collage(sch, pres)
    prover = create_prover(col, opts)
    dp_fn = eq -> prover(Ctx(), eq)
    initial_instance(pres, dp_fn, sch)
end

"""Check if a term references any generator in the given set."""
function _term_references_any(t::CQLTerm, gen_set::Set{Symbol})::Bool
    if t isa CQLGen
        return t.gen in gen_set
    elseif t isa CQLFk
        return _term_references_any(t.arg, gen_set)
    elseif t isa CQLAtt
        return _term_references_any(t.arg, gen_set)
    elseif t isa CQLSym
        return any(_term_references_any(a, gen_set) for a in t.args)
    else
        return false
    end
end

"""Prefix a schema: add a string prefix to all entity, FK, and attribute names."""
function _prefix_schema(sch::CQLSchema, prefix::String)::CQLSchema
    ts = sch.typeside
    p = Symbol(prefix)

    new_ens = Set{Symbol}(Symbol(p, en) for en in sch.ens)
    en_map = Dict{Symbol,Symbol}(en => Symbol(p, en) for en in sch.ens)

    new_fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    fk_map = Dict{Symbol,Symbol}()
    for (fk, (src, tgt)) in sch.fks
        new_fk = Symbol(p, fk)
        new_fks[new_fk] = (en_map[src], en_map[tgt])
        fk_map[fk] = new_fk
    end

    new_atts = Dict{Symbol, Tuple{Symbol, Symbol}}()
    att_map = Dict{Symbol,Symbol}()
    for (att, (src, ty)) in sch.atts
        new_att = Symbol(p, att)
        new_atts[new_att] = (en_map[src], ty)
        att_map[att] = new_att
    end

    rename_term(t) = begin
        if t isa CQLVar; t
        elseif t isa CQLFk; CQLFk(fk_map[t.fk], rename_term(t.arg))
        elseif t isa CQLAtt; CQLAtt(att_map[t.att], rename_term(t.arg))
        elseif t isa CQLSym; CQLSym(t.sym, CQLTerm[rename_term(a) for a in t.args])
        else; t
        end
    end

    new_peqs = Set{Tuple{Symbol, Equation}}()
    for (en, eq) in sch.path_eqs
        push!(new_peqs, (en_map[en], Equation(rename_term(eq.lhs), rename_term(eq.rhs))))
    end
    new_oeqs = Set{Tuple{Symbol, Equation}}()
    for (en, eq) in sch.obs_eqs
        push!(new_oeqs, (en_map[en], Equation(rename_term(eq.lhs), rename_term(eq.rhs))))
    end

    eq_fn = (en, eq) -> true  # simplified prover for prefixed schemas
    CQLSchema(ts, new_ens, new_fks, new_atts, new_peqs, new_oeqs, eq_fn)
end

"""Create inclusion mapping from a sub-schema to a super-schema (identity on shared elements)."""
function _include_mapping(src::CQLSchema, tgt::CQLSchema)::CQLMapping
    m_ens = Dict{Symbol, Symbol}(en => en for en in src.ens)
    m_fks = Dict{Symbol, CQLTerm}(fk => CQLFk(fk, CQLVar(Symbol("_unit"))) for fk in keys(src.fks))
    m_atts = Dict{Symbol, CQLTerm}(att => CQLAtt(att, CQLVar(Symbol("_unit"))) for att in keys(src.atts))
    CQLMapping(src, tgt, m_ens, m_fks, m_atts)
end

"""Create mapping from schema to its prefixed version."""
function _to_prefix_mapping(src::CQLSchema, prefixed::CQLSchema, prefix::String)::CQLMapping
    p = Symbol(prefix)
    m_ens = Dict{Symbol, Symbol}(en => Symbol(p, en) for en in src.ens)
    m_fks = Dict{Symbol, CQLTerm}(fk => CQLFk(Symbol(p, fk), CQLVar(Symbol("_unit"))) for fk in keys(src.fks))
    m_atts = Dict{Symbol, CQLTerm}(att => CQLAtt(Symbol(p, att), CQLVar(Symbol("_unit"))) for att in keys(src.atts))
    CQLMapping(src, prefixed, m_ens, m_fks, m_atts)
end

"""Create mapping from prefixed schema back to original."""
function _from_prefix_mapping(prefixed::CQLSchema, src::CQLSchema, prefix::String)::CQLMapping
    p = Symbol(prefix)
    m_ens = Dict{Symbol, Symbol}(Symbol(p, en) => en for en in src.ens)
    m_fks = Dict{Symbol, CQLTerm}(Symbol(p, fk) => CQLFk(fk, CQLVar(Symbol("_unit"))) for fk in keys(src.fks))
    m_atts = Dict{Symbol, CQLTerm}(Symbol(p, att) => CQLAtt(att, CQLVar(Symbol("_unit"))) for att in keys(src.atts))
    CQLMapping(prefixed, src, m_ens, m_fks, m_atts)
end

"""Create inclusion query from sub-schema to super-schema (identity on shared entities)."""
function _include_query(src::CQLSchema, tgt::CQLSchema)::CQLQuery
    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}()
    fks_map = Dict{Symbol, Dict{Symbol, CQLTerm}}()
    atts_map = Dict{Symbol, CQLTerm}()

    for en in src.ens
        v = Symbol("v_", en)
        ens[en] = (Dict(v => en), Set{Equation}())
        for (fk, (fk_src, _)) in src.fks
            if fk_src == en
                if !haskey(fks_map, fk)
                    fks_map[fk] = Dict{Symbol, CQLTerm}()
                end
                fks_map[fk][v] = CQLFk(fk, CQLVar(v))
            end
        end
        for (att, (att_src, _)) in src.atts
            if att_src == en
                atts_map[att] = CQLAtt(att, CQLVar(v))
            end
        end
    end

    CQLQuery(src, tgt, ens, fks_map, atts_map)
end

"""Get options from an expression."""
function get_exp_options(e::Exp)::Vector{Tuple{String,String}}
    body = e.body
    if body isa TypesideRawExp
        body.raw.options
    elseif body isa SchemaRawExp
        body.raw.options
    elseif body isa InstanceRawExp
        body.raw.options
    elseif body isa MappingRawExp
        body.raw.options
    elseif body isa TransformRawExp
        body.options
    else
        Tuple{String,String}[]
    end
end

"""Run a complete CQL program: parse, resolve dependencies, evaluate."""
function run_program(source::String)::Env
    prog = parse_program(source)

    # Build global options
    opts = isempty(prog.options) ? default_options() : to_options(default_options(), prog.options)
    env = Env(opts)

    # Find evaluation order
    order = find_order(prog)

    # Build name -> Exp lookup
    exp_map = Dict{String, Exp}()
    for e in prog.exps
        exp_map[e.name] = e
    end

    # Evaluate in order
    for (name, kind) in order
        if haskey(exp_map, name)
            e = exp_map[name]
            # Merge per-expression options
            exp_opts = get_exp_options(e)
            if !isempty(exp_opts)
                env.options = to_options(opts, exp_opts)
            end
            eval_exp!(env, e)
            # Restore global options
            env.options = opts
        end
    end

    env
end

