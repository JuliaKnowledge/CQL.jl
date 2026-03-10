"""
Program evaluation: dependency resolution and eval pipeline.

A CQL program consists of named declarations (typesides, schemas, instances,
mappings, transforms, queries) that are evaluated in dependency order.
"""

# ============================================================================
# Environment
# ============================================================================

"""Parsed graph structure: nodes and edges."""
struct CQLGraph
    nodes::Vector{String}
    edges::Vector{Tuple{String, Tuple{String, String}}}  # name -> (src_node, tgt_node)
end

"""The evaluation environment: maps names to evaluated values."""
mutable struct Env
    typesides::Dict{String, Typeside}
    schemas::Dict{String, CQLSchema}
    instances::Dict{String, CQLInstance}
    mappings::Dict{String, CQLMapping}
    transforms::Dict{String, CQLTransform}
    queries::Dict{String, CQLQuery}
    colimits::Dict{String, SchemaColimitResult}
    constraints::Dict{String, CQLConstraints}
    graphs::Dict{String, CQLGraph}
    options::CQLOptions
end

Env(opts::CQLOptions) = Env(
    Dict{String,Typeside}(),
    Dict{String,CQLSchema}(),
    Dict{String,CQLInstance}(),
    Dict{String,CQLMapping}(),
    Dict{String,CQLTransform}(),
    Dict{String,CQLQuery}(),
    Dict{String,SchemaColimitResult}(),
    Dict{String,CQLConstraints}(),
    Dict{String,CQLGraph}(),
    opts,
)

function Base.getproperty(env::Env, name::Symbol)
    name in fieldnames(Env) && return getfield(env, name)
    s = string(name)
    for dict in (getfield(env, :typesides), getfield(env, :schemas),
                 getfield(env, :instances), getfield(env, :mappings),
                 getfield(env, :transforms), getfield(env, :queries),
                 getfield(env, :colimits), getfield(env, :constraints),
                 getfield(env, :graphs))
        haskey(dict, s) && return dict[s]
    end
    throw(KeyError(name))
end

function Base.propertynames(env::Env, private::Bool=false)
    names = Symbol[fieldnames(Env)...]
    for dict in (getfield(env, :typesides), getfield(env, :schemas),
                 getfield(env, :instances), getfield(env, :mappings),
                 getfield(env, :transforms), getfield(env, :queries),
                 getfield(env, :colimits), getfield(env, :constraints),
                 getfield(env, :graphs))
        append!(names, Symbol.(keys(dict)))
    end
    names
end

function Base.show(io::IO, env::Env)
    println(io, "CQL Environment:")
    for (n, _) in env.typesides
        println(io, "  typeside $n")
    end
    for (n, _) in env.schemas
        println(io, "  schema $n")
    end
    for (n, i) in env.instances
        println(io, "  instance $n")
        for (en, xs) in i.algebra.en
            println(io, "    $en: $(length(xs)) rows")
        end
    end
    for (n, _) in env.mappings
        println(io, "  mapping $n")
    end
    for (n, _) in env.transforms
        println(io, "  transform $n")
    end
    for (n, _) in env.queries
        println(io, "  query $n")
    end
end

# ============================================================================
# Dependency resolution
# ============================================================================

"""Get the dependencies of an Exp (parsed declaration)."""
function exp_deps(e::Exp)::Vector{Tuple{String,Kind}}
    body = e.body
    if body isa TypesideExp
        deps(body)
    elseif body isa SchemaExp
        deps(body)
    elseif body isa InstanceExp
        deps(body)
    elseif body isa MappingExp
        deps(body)
    elseif body isa TransformExp
        deps(body)
    elseif body isa QueryExp
        deps(body)
    elseif body isa SchemaColimitExp
        deps(body)
    elseif body isa SchemaColimitModify
        deps(body)
    elseif body isa SchemaColimitLiteralExp
        deps(body)
    elseif body isa ConstraintsRawExp
        deps(body)
    elseif body isa ConstraintsEmpty
        deps(body)
    elseif body isa ConstraintsInclude
        deps(body)
    elseif body isa ConstraintsFromSchema
        deps(body)
    elseif body isa CommandExportJdbc
        [(body.instance_name, INSTANCE)]
    elseif body isa CommandExportOdbc
        [(body.instance_name, INSTANCE)]
    elseif body isa CommandExportRdfInstanceXml
        [(body.instance_name, INSTANCE)]
    else
        Tuple{String,Kind}[]
    end
end

"""Determine evaluation order of declarations via topological sort."""
function find_order(prog::Program)::Vector{Tuple{String, Kind}}
    nodes = Tuple{String,Kind}[]
    edges = Tuple{Tuple{String,Kind}, Tuple{String,Kind}}[]

    # Track commands in program order for implicit dependencies
    prior_commands = Tuple{String,Kind}[]

    for e in prog.exps
        node = (e.name, e.kind)
        push!(nodes, node)
        for dep in exp_deps(e)
            push!(edges, (dep, node))
        end
        # Each declaration depends on all prior commands (ensures program-order execution)
        if e.kind == COMMAND || e.kind == COMMENT
            for prev_cmd in prior_commands
                push!(edges, (prev_cmd, node))
            end
            push!(prior_commands, node)
        else
            # Non-command JDBC/RDF operations depend on all prior commands
            body = e.body
            if body isa InstanceImportJdbc || body isa InstanceImportJdbcDirect ||
               body isa SchemaImportJdbcAll || body isa InstanceImportRdf ||
               body isa InstanceImportOdbc || body isa InstanceImportOdbcDirect ||
               body isa SchemaImportOdbcAll
                for prev_cmd in prior_commands
                    push!(edges, (prev_cmd, node))
                end
            end
        end
    end

    node_set = Set(nodes)
    valid_edges = filter(e -> e[1] in node_set && e[2] in node_set, edges)

    g = SimpleGraph(nodes, valid_edges)
    tsort(g)
end

# ============================================================================
# Expression evaluation
# ============================================================================

"""Evaluate a typeside expression."""
function eval_typeside(env::Env, e::TypesideExp)::Typeside
    if e isa TypesideInitial
        initial_typeside()
    elseif e isa TypesideSql
        sql_typeside()
    elseif e isa TypesideRdf
        rdf_typeside()
    elseif e isa TypesideVar
        haskey(env.typesides, e.name) || throw(CQLException("Undefined typeside: $(e.name)"))
        env.typesides[e.name]
    elseif e isa TypesideRawExp
        raw = e.raw
        imports = Typeside[eval_typeside(env, imp) for imp in raw.imports]
        eval_typeside_raw(env.options, raw, imports)
    elseif e isa TypesideOf
        sch = eval_schema(env, e.schema)
        sch.typeside
    else
        throw(CQLException("Unknown typeside expression"))
    end
end

"""Evaluate a schema expression."""
function eval_schema(env::Env, e::SchemaExp)::CQLSchema
    if e isa SchemaVar
        if e.name == "rdf" && !haskey(env.schemas, "rdf")
            # Built-in rdf schema: entity R with attributes subject, predicate, object : Dom
            ts = rdf_typeside()
            ens = Set{Symbol}([:R])
            fks = Dict{Symbol,Tuple{Symbol,Symbol}}()
            atts = Dict{Symbol,Tuple{Symbol,Symbol}}(
                :subject => (:R, :Dom),
                :predicate => (:R, :Dom),
                :object => (:R, :Dom),
            )
            env.schemas["rdf"] = CQLSchema(ts, ens, fks, atts,
                Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(),
                (en, eq) -> eq.lhs == eq.rhs)
        end
        haskey(env.schemas, e.name) || throw(CQLException("Undefined schema: $(e.name)"))
        env.schemas[e.name]
    elseif e isa SchemaInitial
        ts = eval_typeside(env, e.typeside)
        typeside_to_schema(ts)
    elseif e isa SchemaRawExp
        raw = e.raw
        ts = eval_typeside(env, raw.typeside_ref)
        imports = CQLSchema[eval_schema(env, imp) for imp in raw.imports]
        eval_schema_raw(env.options, ts, raw, imports)
    elseif e isa SchemaGetSchema
        haskey(env.colimits, e.colimit_name) || throw(CQLException("Undefined schema_colimit: $(e.colimit_name)"))
        env.colimits[e.colimit_name].schema
    elseif e isa SchemaPivot
        inst = eval_instance(env, e.instance)
        _pivot_schema(inst)
    elseif e isa SchemaImportJdbcAll
        eval_schema_import_jdbc_all(env, e)
    elseif e isa SchemaImportOdbcAll
        eval_schema_import_odbc_all(env, e)
    elseif e isa SchemaOf
        inst = eval_instance(env, e.instance)
        inst.schema
    elseif e isa SchemaFront
        haskey(env.constraints, e.constraints_name) || throw(CQLException("Undefined constraints: $(e.constraints_name)"))
        c = env.constraints[e.constraints_name]
        _eval_schema_front(c, e.index, false)
    elseif e isa SchemaSpanify
        sch = eval_schema(env, e.schema)
        _eval_schema_spanify(sch)
    elseif e isa SchemaPrefix
        sch = eval_schema(env, e.schema)
        _prefix_schema(sch, e.prefix_str)
    elseif e isa SchemaDomQ
        q = eval_query(env, e.query)
        q.src
    elseif e isa SchemaCodQ
        q = eval_query(env, e.query)
        q.dst
    elseif e isa SchemaDomM
        m = eval_mapping(env, e.mapping)
        m.src
    elseif e isa SchemaCodM
        m = eval_mapping(env, e.mapping)
        m.dst
    else
        throw(CQLException("Unknown schema expression"))
    end
end

"""Evaluate an instance expression."""
function eval_instance(env::Env, e::InstanceExp)::CQLInstance
    if e isa InstanceVar
        haskey(env.instances, e.name) || throw(CQLException("Undefined instance: $(e.name)"))
        env.instances[e.name]
    elseif e isa InstanceInitial
        sch = eval_schema(env, e.schema)
        empty_instance(sch)
    elseif e isa InstanceRawExp
        raw = e.raw
        sch = eval_schema(env, raw.schema_ref)
        imports = CQLInstance[eval_instance(env, imp) for imp in raw.imports]
        eval_instance_raw(env.options, sch, raw, imports)
    elseif e isa InstanceSigma
        m = eval_mapping(env, e.mapping)
        i = eval_instance(env, e.instance)
        opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
        eval_sigma_instance(m, i, opts)
    elseif e isa InstanceDelta
        m = eval_mapping(env, e.mapping)
        i = eval_instance(env, e.instance)
        opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
        eval_delta_instance(m, i, opts)
    elseif e isa InstanceEval
        q = eval_query(env, e.query)
        i = eval_instance(env, e.instance)
        eval_query_instance(q, i, env.options)
    elseif e isa InstanceCoproduct
        sch = eval_schema(env, e.schema)
        insts = CQLInstance[eval_instance(env, ie) for ie in e.instances]
        eval_coproduct_instance(sch, insts, env.options)
    elseif e isa InstanceChase
        c = if e.constraints isa String
            haskey(env.constraints, e.constraints) || throw(CQLException("Undefined constraints: $(e.constraints)"))
            env.constraints[e.constraints]
        else
            eval_constraints_exp(env, e.constraints)
        end
        i = eval_instance(env, e.instance)
        local_opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
        chase(c, i, local_opts)
    elseif e isa InstancePivot
        throw(CQLException("Pivot instances are not yet supported (use pivot schema + literal instance instead)"))
    elseif e isa InstanceRandom
        sch = eval_schema(env, e.schema)
        eval_random_instance(sch, e.gen_counts, e.options, env.options)
    elseif e isa InstanceCoeval
        # Special case: coeval (toCoQuery F) I = delta F I
        if e.query isa QueryToCoQuery
            m = eval_mapping(env, e.query.mapping)
            i = eval_instance(env, e.instance)
            opts = env.options
            return eval_delta_instance(m, i, opts)
        end
        q = eval_query(env, e.query)
        inst = eval_instance(env, e.instance)
        eval_coeval_instance(q, inst, env.options)
    elseif e isa InstanceImportCsv
        _eval_import_csv(env, e)
    elseif e isa InstanceImportJdbc
        eval_import_jdbc(env, e)
    elseif e isa InstanceDistinct
        src = eval_instance(env, e.instance)
        distinct_instance(src)
    elseif e isa InstanceCoequalize
        f = eval_transform(env, e.t1)
        g = eval_transform(env, e.t2)
        eval_coequalize(f, g, env.options)
    elseif e isa InstanceQuotientQuery
        i = eval_instance(env, e.instance)
        opts_local = env.options
        eval_quotient_query(i, e.raw_query, opts_local)
    elseif e isa InstanceDomT
        t = eval_transform(env, e.transform)
        t.src
    elseif e isa InstanceCodT
        t = eval_transform(env, e.transform)
        t.dst
    elseif e isa InstanceColimit
        haskey(env.graphs, e.graph_name) || throw(CQLException("Undefined graph: $(e.graph_name)"))
        graph = env.graphs[e.graph_name]
        sch = eval_schema(env, e.schema)
        local_opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
        eval_colimit_instance(env, graph, sch, e.node_map, e.edge_map, local_opts)
    elseif e isa InstanceImportJdbcDirect
        eval_import_jdbc_direct(env, e)
    elseif e isa InstanceImportOdbc
        eval_import_odbc(env, e)
    elseif e isa InstanceImportOdbcDirect
        eval_import_odbc_direct(env, e)
    elseif e isa InstanceImportJsonLd
        _eval_import_json_ld(e.path)
    elseif e isa InstanceImportRdf
        eval_import_rdf_all(e.path)
    elseif e isa InstanceImportXml
        _eval_import_xml(e.path)
    elseif e isa InstanceSpanify
        inst = eval_instance(env, e.instance)
        _eval_instance_spanify(inst, env)
    elseif e isa InstanceFrozen
        q = eval_query(env, e.query)
        _eval_frozen_instance(q, Symbol(e.entity), env.options)
    elseif e isa InstanceExcept
        i1 = eval_instance(env, e.inst1)
        i2 = eval_instance(env, e.inst2)
        eval_except_instance(i1, i2, env.options)
    elseif e isa InstanceAnonymize
        inst = eval_instance(env, e.instance)
        _eval_anonymize_instance(inst, env.options)
    elseif e isa InstancePi
        m = eval_mapping(env, e.mapping)
        i = eval_instance(env, e.instance)
        local_opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
        _eval_pi_instance(m, i, local_opts)
    elseif e isa InstanceCascadeDelete
        inst = eval_instance(env, e.instance)
        sch = eval_schema(env, e.schema)
        _eval_cascade_delete(inst, sch, env.options)
    else
        throw(CQLException("Unknown instance expression"))
    end
end

"""Evaluate a random instance: create N generators for each specified entity."""
function eval_random_instance(sch::CQLSchema, gen_counts::Vector{Tuple{String,Int}},
                               local_opts::Vector{Tuple{String,String}}, global_opts::CQLOptions)::CQLInstance
    opts = isempty(local_opts) ? global_opts : to_options(global_opts, local_opts)

    # Parse random_seed option
    seed = 0
    for (k, v) in local_opts
        if k == "random_seed"
            seed = parse(Int, v)
        end
    end

    rng = Random.MersenneTwister(seed)

    # Build generators per entity
    en_gens = Dict{Symbol, Vector{Symbol}}()
    gens = Tuple{String,String}[]
    for (en_name, count) in gen_counts
        en_sym = Symbol(en_name)
        en_gens[en_sym] = Symbol[]
        for i in 1:count
            gname = Symbol("gen_", en_name, "_", i)
            push!(en_gens[en_sym], gname)
            push!(gens, (string(gname), en_name))
        end
    end
    # Ensure all entities have entries
    for en in sch.ens
        if !haskey(en_gens, en)
            en_gens[en] = Symbol[]
        end
    end

    # Build random FK and attribute equations
    eqs = Tuple{RawTerm,RawTerm}[]
    for (en_name, count) in gen_counts
        en_sym = Symbol(en_name)
        for i in 1:count
            gname = "gen_$(en_name)_$i"
            # Random FK assignments
            for (fk, (src, tgt)) in sch.fks
                if src == en_sym
                    tgt_gens = en_gens[tgt]
                    if !isempty(tgt_gens)
                        idx = mod(rand(rng, Int), length(tgt_gens)) + 1
                        tgt_gen = string(tgt_gens[idx])
                        lhs = RawTerm(string(fk), [RawTerm(gname, RawTerm[])])
                        rhs = RawTerm(tgt_gen, RawTerm[])
                        push!(eqs, (lhs, rhs))
                    end
                end
            end
            # Random attribute assignments (assign Skolem value = generator index)
            for (att, (src, ty)) in sch.atts
                if src == en_sym
                    # Generate a random value index for this attribute
                    val_idx = mod(rand(rng, Int), max(count, 1)) + 1
                    val_name = "v_$(en_name)_$(att)_$(val_idx)"
                    lhs = RawTerm(string(att), [RawTerm(gname, RawTerm[])])
                    rhs = RawTerm(val_name, RawTerm[])
                    push!(eqs, (lhs, rhs))
                end
            end
        end
    end

    raw = InstExpRaw(
        SchemaVar("__random_schema__"),
        gens,
        eqs,
        local_opts,
        Any[],
    )
    eval_instance_raw(opts, sch, raw, CQLInstance[])
end

"""Evaluate a mapping expression."""
function eval_mapping(env::Env, e)::CQLMapping
    if e isa MappingVar
        haskey(env.mappings, e.name) || throw(CQLException("Undefined mapping: $(e.name)"))
        env.mappings[e.name]
    elseif e isa MappingId
        sch = eval_schema(env, e.schema)
        identity_mapping(sch)
    elseif e isa MappingComp
        f = eval_mapping(env, e.first)
        g = eval_mapping(env, e.second)
        compose_mapping(f, g)
    elseif e isa MappingRawExp
        raw = e.raw
        src = eval_schema(env, raw.src_ref)
        dst = eval_schema(env, raw.dst_ref)
        imports = CQLMapping[eval_mapping(env, imp) for imp in raw.imports]
        eval_mapping_raw(src, dst, raw, imports)
    elseif e isa MappingGetMapping
        haskey(env.colimits, e.colimit_name) || throw(CQLException("Undefined schema_colimit: $(e.colimit_name)"))
        colimit = env.colimits[e.colimit_name]
        haskey(colimit.mappings, e.schema_name) || throw(CQLException("No mapping for schema: $(e.schema_name) in colimit $(e.colimit_name)"))
        colimit.mappings[e.schema_name]
    elseif e isa MappingGetPseudo
        haskey(env.colimits, e.colimit_name) || throw(CQLException("Undefined schema_colimit: $(e.colimit_name)"))
        colimit = env.colimits[e.colimit_name]
        _eval_get_pseudo(colimit, env.options)
    elseif e isa MappingPivot
        inst = eval_instance(env, e.instance)
        _pivot_mapping(inst)
    elseif e isa MappingInclude
        src = eval_schema(env, e.src_schema)
        tgt = eval_schema(env, e.tgt_schema)
        _include_mapping(src, tgt)
    elseif e isa MappingToPrefix
        sch = eval_schema(env, e.schema)
        prefixed = _prefix_schema(sch, e.prefix_str)
        _to_prefix_mapping(sch, prefixed, e.prefix_str)
    elseif e isa MappingFromPrefix
        sch = eval_schema(env, e.schema)
        prefixed = _prefix_schema(sch, e.prefix_str)
        _from_prefix_mapping(prefixed, sch, e.prefix_str)
    else
        throw(CQLException("Unknown mapping expression"))
    end
end

"""Evaluate a transform expression."""
function eval_transform(env::Env, e::TransformExp)::CQLTransform
    if e isa TransformVar
        haskey(env.transforms, e.name) || throw(CQLException("Undefined transform: $(e.name)"))
        env.transforms[e.name]
    elseif e isa TransformId
        inst = eval_instance(env, e.instance)
        identity_transform(inst)
    elseif e isa TransformComp
        f = eval_transform(env, e.first)
        g = eval_transform(env, e.second)
        compose_transform(f, g)
    elseif e isa TransformRawExp
        src_inst = eval_instance(env, e.src_ref)
        dst_inst = eval_instance(env, e.dst_ref)
        gens = Dict{Symbol,CQLTerm}()
        for (g, term_raw) in e.gens
            gens[Symbol(g)] = _trans_inst_term(
                src_inst.schema, keys(dst_inst.pres.gens), keys(dst_inst.pres.sks), term_raw)
        end
        sks = Dict{Symbol,CQLTerm}(s => CQLSk(s) for s in keys(src_inst.pres.sks))
        CQLTransform(src_inst, dst_inst, gens, sks)
    elseif e isa TransformSigmaExp
        m = eval_mapping(env, e.mapping)
        t = eval_transform(env, e.transform)
        opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
        eval_sigma_transform(m, t, opts)
    elseif e isa TransformDeltaExp
        m = eval_mapping(env, e.mapping)
        t = eval_transform(env, e.transform)
        opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
        eval_delta_transform(m, t, opts)
    elseif e isa TransformUnit
        m = eval_mapping(env, e.mapping)
        inst = eval_instance(env, e.instance)
        opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
        eval_unit_transform(m, inst, opts)
    elseif e isa TransformCounit
        m = eval_mapping(env, e.mapping)
        inst = eval_instance(env, e.instance)
        opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
        eval_counit_transform(m, inst, opts)
    elseif e isa TransformEval
        q = eval_query(env, e.query)
        t = eval_transform(env, e.transform)
        eval_query_transform(q, t, env.options)
    elseif e isa TransformCoeval
        # Special case: coeval (toCoQuery F) T = delta F T
        if e.query isa QueryToCoQuery
            m = eval_mapping(env, e.query.mapping)
            t = eval_transform(env, e.transform)
            opts = env.options
            return eval_delta_transform(m, t, opts)
        end
        q = eval_query(env, e.query)
        t = eval_transform(env, e.transform)
        eval_coeval_transform(q, t, env.options)
    elseif e isa TransformCounitQuery
        q = eval_query(env, e.query)
        inst = eval_instance(env, e.instance)
        local_opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
        eval_counit_query_transform(q, inst, local_opts)
    elseif e isa TransformUnitQuery
        q = eval_query(env, e.query)
        inst = eval_instance(env, e.instance)
        local_opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
        eval_unit_query_transform(q, inst, local_opts)
    elseif e isa TransformFrozen
        q = eval_query(env, e.query)
        _eval_frozen_transform(q, e.lambda_var, e.lambda_type, e.lambda_body, e.ret_type, env.options)
    elseif e isa TransformExcept
        t = eval_transform(env, e.transform)
        i = eval_instance(env, e.instance)
        _eval_except_transform(t, i)
    elseif e isa TransformExceptReturn
        i1 = eval_instance(env, e.inst1)
        i2 = eval_instance(env, e.inst2)
        _eval_except_return_transform(i1, i2)
    elseif e isa TransformInclude
        i1 = eval_instance(env, e.inst1)
        i2 = eval_instance(env, e.inst2)
        _eval_include_transform(i1, i2)
    elseif e isa TransformDistinctTransform
        t = eval_transform(env, e.transform)
        _eval_distinct_transform(t)
    elseif e isa TransformDistinctReturn
        i = eval_instance(env, e.instance)
        _eval_distinct_return_transform(i)
    elseif e isa TransformPi
        m = eval_mapping(env, e.mapping)
        t = eval_transform(env, e.transform)
        local_opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
        _eval_pi_transform(m, t, local_opts)
    else
        throw(CQLException("Unknown transform expression"))
    end
end

# ============================================================================
# CSV import
# ============================================================================

"""Evaluate an import_csv instance expression.
If the schema reference resolves to a typeside, auto-discover schema from CSV files.
If it resolves to a schema, use it directly."""
function _eval_import_csv(env::Env, e::InstanceImportCsv)::CQLInstance
    path = strip(e.path, '"')

    # Try to resolve as a schema first
    sch = try
        eval_schema(env, e.schema)
    catch
        nothing
    end

    if sch !== nothing
        return import_csv_instance(path, sch)
    end

    # Resolve as a typeside and auto-discover schema from CSV files
    ts = if e.schema isa SchemaVar
        haskey(env.typesides, e.schema.name) || throw(CQLException(
            "import_csv: '$(e.schema.name)' is neither a schema nor a typeside"))
        env.typesides[e.schema.name]
    else
        throw(CQLException("import_csv: cannot resolve schema/typeside reference"))
    end

    # Discover schema and build instance from CSV files
    _import_csv_discover(path, ts, env.options)
end

"""Auto-discover schema from CSV files and import data."""
function _import_csv_discover(dir::AbstractString, ts::Typeside, opts::CQLOptions)::CQLInstance
    isdir(dir) || throw(CQLException("import_csv: directory not found: $dir"))

    csv_files = filter(f -> endswith(lowercase(f), ".csv"), readdir(dir))
    isempty(csv_files) && throw(CQLException("import_csv: no CSV files found in $dir"))

    # Default attribute type: use String if available, else first type
    default_type = :String in ts.tys ? :String :
                   :Dom in ts.tys ? :Dom : first(ts.tys)

    ens = Set{Symbol}()
    fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    atts = Dict{Symbol, Tuple{Symbol, Symbol}}()
    gens = Dict{Symbol, Symbol}()
    eqs = Set{Equation}()

    # Mapping from entity -> (column_name -> row_id -> value)
    entity_ids = Dict{Symbol, Dict{String, Symbol}}()

    for csv_file in csv_files
        en_name = Symbol(replace(csv_file, r"\.csv$"i => ""))
        push!(ens, en_name)
        entity_ids[en_name] = Dict{String, Symbol}()

        filepath = joinpath(dir, csv_file)
        csvdata = CSV.File(filepath; silencewarnings=true)
        cols = propertynames(csvdata)

        # Each column becomes an attribute: entity__col : entity -> default_type
        for col in cols
            att_name = Symbol(en_name, "__", col)
            atts[att_name] = (en_name, default_type)
        end

        # Create generators for each row (auto-incremented IDs)
        row_id = 0
        for row in csvdata
            gen_sym = Symbol(en_name, "_", row_id)
            gens[gen_sym] = en_name
            entity_ids[en_name][string(row_id)] = gen_sym

            for col in cols
                att_name = Symbol(en_name, "__", col)
                val = getproperty(row, col)
                if val !== missing
                    val_str = strip(string(val))
                    if !isempty(val_str)
                        push!(eqs, Equation(
                            CQLAtt(att_name, CQLGen(gen_sym)),
                            CQLSym(Symbol(val_str), CQLTerm[])))
                    end
                end
            end
            row_id += 1
        end
    end

    # Build name lookup indices
    att_by_name = Dict{Symbol, Vector{Symbol}}()
    for att_name in keys(atts)
        plain = Symbol(split(string(att_name), "__"; limit=2)[end])
        if !haskey(att_by_name, plain)
            att_by_name[plain] = Symbol[]
        end
        push!(att_by_name[plain], att_name)
    end

    sch = CQLSchema(ts, ens, fks, atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(),
        (en, eq) -> eq.lhs == eq.rhs,
        Dict{Symbol,Vector{Symbol}}(), att_by_name, collect(keys(fks)))

    pres = Presentation(gens, Dict{Symbol,Symbol}(), eqs)
    saturated_instance(sch, pres)
end

# ============================================================================
# XML import
# ============================================================================

"""Import an XML file as an RDF-style CQL instance.
Flattens the XML tree into (subject, predicate, object) triples on the built-in RDF schema."""
function _eval_import_xml(path::AbstractString)::CQLInstance
    path = strip(path, '"')
    isfile(path) || throw(CQLException("import_xml_all: file not found: $path"))

    doc = read(path, XMLParser.Node)

    # Build RDF schema
    ts = rdf_typeside()
    ens = Set{Symbol}([:R])
    fks = Dict{Symbol,Tuple{Symbol,Symbol}}()
    atts = Dict{Symbol,Tuple{Symbol,Symbol}}(
        :subject => (:R, :Dom),
        :predicate => (:R, :Dom),
        :object => (:R, :Dom),
    )
    sch = CQLSchema(ts, ens, fks, atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(),
        (en, eq) -> eq.lhs == eq.rhs)

    # Flatten XML into triples
    triples = Tuple{String, String, String}[]
    counter = Ref(0)
    _xml_to_triples!(triples, doc, "", counter)

    # Build instance
    gens = Dict{Symbol, Symbol}()
    eqs = Set{Equation}()
    for (i, (subj, pred, obj)) in enumerate(triples)
        gen_sym = Symbol("triple_", i)
        gens[gen_sym] = :R
        push!(eqs, Equation(
            CQLAtt(:subject, CQLGen(gen_sym)),
            CQLSym(Symbol(subj), CQLTerm[])))
        push!(eqs, Equation(
            CQLAtt(:predicate, CQLGen(gen_sym)),
            CQLSym(Symbol(pred), CQLTerm[])))
        push!(eqs, Equation(
            CQLAtt(:object, CQLGen(gen_sym)),
            CQLSym(Symbol(obj), CQLTerm[])))
    end

    pres = Presentation(gens, Dict{Symbol,Symbol}(), eqs)
    saturated_instance(sch, pres)
end

"""Recursively flatten an XML node tree into (subject, predicate, object) triples.
Matches Java's XML→JSON→RDF pipeline: leaf elements with only text content
are collapsed into the parent triple, and the root element gets a wrapper triple."""
function _xml_to_triples!(triples::Vector{Tuple{String,String,String}},
                           node::XMLParser.Node, parent_id::String, counter::Ref{Int})
    nk = XMLParser.nodetype(node)

    if nk == XMLParser.Element
        node_tag = XMLParser.tag(node)

        # Gather text and element children
        text_parts = String[]
        child_elems = XMLParser.Node[]
        for child in XMLParser.children(node)
            ct = XMLParser.nodetype(child)
            if ct == XMLParser.Text
                txt = strip(XMLParser.value(child))
                if !isempty(txt)
                    push!(text_parts, txt)
                end
            elseif ct == XMLParser.Element
                push!(child_elems, child)
            end
        end

        # Leaf element (only text, no child elements): collapse into parent
        if !isempty(text_parts) && isempty(child_elems) && !isempty(parent_id)
            push!(triples, (parent_id, node_tag, join(text_parts, " ")))
            return
        end

        # Non-leaf element: create a node
        counter[] += 1
        node_id = string("node_", counter[])

        if !isempty(parent_id)
            push!(triples, (parent_id, node_tag, node_id))
        end

        # Attributes (no @ prefix, matching Java's JSON conversion)
        node_attrs = XMLParser.attributes(node)
        if node_attrs !== nothing
            for (k, v) in node_attrs
                push!(triples, (node_id, k, v))
            end
        end

        # Recurse into child elements
        for child in child_elems
            _xml_to_triples!(triples, child, node_id, counter)
        end

        # Non-leaf with text: add text as content triple
        if !isempty(text_parts) && !isempty(child_elems)
            push!(triples, (node_id, "content", join(text_parts, " ")))
        end
    elseif nk == XMLParser.Document
        for child in XMLParser.children(node)
            ct = XMLParser.nodetype(child)
            if ct == XMLParser.Element
                # Root element: add wrapper triple (root_node --tag--> content_node)
                root_tag = XMLParser.tag(child)
                counter[] += 1
                wrapper_id = string("node_", counter[])
                counter[] += 1
                content_id = string("node_", counter[])
                push!(triples, (content_id, root_tag, wrapper_id))
                # Process root element's children using wrapper_id as parent
                root_attrs = XMLParser.attributes(child)
                if root_attrs !== nothing
                    for (k, v) in root_attrs
                        push!(triples, (wrapper_id, k, v))
                    end
                end
                for grandchild in XMLParser.children(child)
                    _xml_to_triples!(triples, grandchild, wrapper_id, counter)
                end
            end
        end
    end
end

"""Spanify an RDF instance: group triples by predicate, creating one entity per predicate.
Each entity gets subject and object attributes of type Dom."""
function _eval_instance_spanify(inst::CQLInstance, env::Env)::CQLInstance
    ts = rdf_typeside()
    alg = inst.algebra

    # Group generators by predicate value
    pred_groups = Dict{String, Vector{Symbol}}()  # predicate -> [gen_syms]
    r_gens = get(alg.en, :R, Set{Symbol}())

    for x in r_gens
        pred_term = alg.nf_y(Right((x, :predicate)))
        pred_str = if pred_term isa CQLSym
            string(pred_term.sym)
        elseif pred_term isa CQLSk
            string(pred_term.sk)
        else
            string(pred_term)
        end
        lst = get!(pred_groups, pred_str, Symbol[])
        push!(lst, x)
    end

    # Build spanified schema: one entity per predicate, each with subject/object attributes
    ens = Set{Symbol}()
    fks = Dict{Symbol,Tuple{Symbol,Symbol}}()
    atts = Dict{Symbol,Tuple{Symbol,Symbol}}()
    for pred in keys(pred_groups)
        en_sym = Symbol(pred)
        push!(ens, en_sym)
        atts[Symbol(string(en_sym, "__subject"))] = (en_sym, :Dom)
        atts[Symbol(string(en_sym, "__object"))] = (en_sym, :Dom)
    end
    sch = CQLSchema(ts, ens, fks, atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(),
        (en, eq) -> eq.lhs == eq.rhs)

    # Build presentation with generators and attribute equations
    pres_gens = Dict{Symbol, Symbol}()
    pres_eqs = Set{Equation}()
    for (pred, xs) in pred_groups
        en_sym = Symbol(pred)
        subj_att = Symbol(string(en_sym, "__subject"))
        obj_att = Symbol(string(en_sym, "__object"))
        for x in xs
            pres_gens[x] = en_sym
            # Get subject and object values from original algebra
            subj_term = alg.nf_y(Right((x, :subject)))
            obj_term = alg.nf_y(Right((x, :object)))
            push!(pres_eqs, Equation(CQLAtt(subj_att, CQLGen(x)), subj_term))
            push!(pres_eqs, Equation(CQLAtt(obj_att, CQLGen(x)), obj_term))
        end
    end

    pres = Presentation(pres_gens, Dict{Symbol,Symbol}(), pres_eqs)
    saturated_instance(sch, pres)
end

"""Evaluate an import_json_ld_all instance expression.
Converts JSON to RDF-style triples following the JSON2RDF algorithm:
each JSON object becomes a blank node, keys become predicates, values become literals."""
function _eval_import_json_ld(path::AbstractString)::CQLInstance
    path = strip(path, '"')
    isfile(path) || throw(CQLException("import_json_ld_all: file not found: $path"))

    data = JSONParser.parsefile(path)

    # Build RDF schema (same as XML import)
    ts = rdf_typeside()
    ens = Set{Symbol}([:R])
    fks = Dict{Symbol,Tuple{Symbol,Symbol}}()
    atts = Dict{Symbol,Tuple{Symbol,Symbol}}(
        :subject => (:R, :Dom),
        :predicate => (:R, :Dom),
        :object => (:R, :Dom),
    )
    sch = CQLSchema(ts, ens, fks, atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(),
        (en, eq) -> eq.lhs == eq.rhs)

    # Flatten JSON into RDF triples
    triples = Tuple{String, String, String}[]
    counter = Ref(0)
    base_uri = "cql://json"
    _json_to_triples!(triples, data, "", base_uri, counter)

    # Build instance
    gens = Dict{Symbol, Symbol}()
    eqs = Set{Equation}()
    for (i, (subj, pred, obj)) in enumerate(triples)
        gen_sym = Symbol("triple_", i)
        gens[gen_sym] = :R
        push!(eqs, Equation(
            CQLAtt(:subject, CQLGen(gen_sym)),
            CQLSym(Symbol(subj), CQLTerm[])))
        push!(eqs, Equation(
            CQLAtt(:predicate, CQLGen(gen_sym)),
            CQLSym(Symbol(pred), CQLTerm[])))
        push!(eqs, Equation(
            CQLAtt(:object, CQLGen(gen_sym)),
            CQLSym(Symbol(obj), CQLTerm[])))
    end

    pres = Presentation(gens, Dict{Symbol,Symbol}(), eqs)
    saturated_instance(sch, pres)
end

"""Recursively convert a JSON value into (subject, predicate, object) triples.
Follows the JSON2RDF algorithm: objects → blank nodes, keys → URI predicates,
scalars → literal objects, arrays → repeated predicates."""
function _json_to_triples!(triples::Vector{Tuple{String,String,String}},
                           value, parent_id::String, base_uri::String, counter::Ref{Int})
    if value isa AbstractDict
        counter[] += 1
        node_id = string("node_", counter[])
        # Link parent to this object
        if !isempty(parent_id)
            push!(triples, (parent_id, "", node_id))
        end
        # Process each key-value pair
        for (k, v) in value
            prop = string(base_uri, "#", k)
            _json_kv_to_triples!(triples, node_id, prop, v, base_uri, counter)
        end
        return node_id
    elseif value isa AbstractVector
        for item in value
            _json_kv_to_triples!(triples, parent_id, "", item, base_uri, counter)
        end
        return parent_id
    else
        # Scalar at top level (unusual) — ignore
        return ""
    end
end

"""Convert a JSON key-value pair into triples."""
function _json_kv_to_triples!(triples::Vector{Tuple{String,String,String}},
                              subject::String, predicate::String, value,
                              base_uri::String, counter::Ref{Int})
    if value isa AbstractDict
        counter[] += 1
        child_id = string("node_", counter[])
        push!(triples, (subject, predicate, child_id))
        for (k, v) in value
            prop = string(base_uri, "#", k)
            _json_kv_to_triples!(triples, child_id, prop, v, base_uri, counter)
        end
    elseif value isa AbstractVector
        for item in value
            _json_kv_to_triples!(triples, subject, predicate, item, base_uri, counter)
        end
    elseif value === nothing
        # null — skip (matches Java behavior)
    else
        push!(triples, (subject, predicate, string(value)))
    end
end

"""Evaluate a query expression."""
function eval_query(env::Env, e::QueryExp)::CQLQuery
    if e isa QueryVar
        haskey(env.queries, e.name) || throw(CQLException("Undefined query: $(e.name)"))
        env.queries[e.name]
    elseif e isa QueryId
        sch = eval_schema(env, e.schema)
        identity_query(sch)
    elseif e isa QueryRawExp
        raw = e.raw
        src = eval_schema(env, raw.src_ref)
        # Check for simple query: auto-generate target schema
        if length(raw.ens) == 1 && raw.ens[1][1] == "__simple__"
            dst = _build_simple_query_target(src, raw)
            eval_query_raw(src, dst, raw)
        else
            dst = eval_schema(env, raw.dst_ref)
            eval_query_raw(src, dst, raw)
        end
    elseif e isa QueryComp
        f = eval_query(env, e.first)
        g = eval_query(env, e.second)
        compose_query(f, g)
    elseif e isa QueryToQuery
        m = eval_mapping(env, e.mapping)
        mapping_to_query(m)
    elseif e isa QueryToCoQuery
        m = eval_mapping(env, e.mapping)
        _delta_coeval_query(m, env.options)
    elseif e isa QueryFront
        haskey(env.constraints, e.constraints_name) || throw(CQLException("Undefined constraints: $(e.constraints_name)"))
        c = env.constraints[e.constraints_name]
        _eval_query_front_back(c, e.index, false)
    elseif e isa QueryBack
        haskey(env.constraints, e.constraints_name) || throw(CQLException("Undefined constraints: $(e.constraints_name)"))
        c = env.constraints[e.constraints_name]
        _eval_query_front_back(c, e.index, true)
    elseif e isa QueryRext
        q1 = eval_query(env, e.q1)
        q2 = eval_query(env, e.q2)
        _eval_rext(q1, q2, env.options)
    elseif e isa QuerySpanify
        sch = eval_schema(env, e.schema)
        _eval_query_spanify(sch)
    elseif e isa QuerySpanifyMapping
        m = eval_mapping(env, e.mapping)
        _eval_query_spanify_mapping(m)
    elseif e isa QueryInclude
        src = eval_schema(env, e.src_schema)
        tgt = eval_schema(env, e.tgt_schema)
        _include_query(src, tgt)
    elseif e isa QueryFromCoSpan
        m1 = eval_mapping(env, e.m1)
        m2 = eval_mapping(env, e.m2)
        # fromCoSpan(M1: S1→C, M2: S2→C) = deltaCoEval(M1) ; deltaEval(M2)
        # Verify cospan: both mappings must share the same target schema
        m1.dst == m2.dst || throw(CQLException(
            "Cannot co-span: target of first mapping is not the same as target of second"))
        q1 = _delta_coeval_query(m1, env.options)  # S1 → C
        q2 = mapping_to_query(m2)                   # C → S2
        compose_query(q1, q2)                        # S1 → S2
    elseif e isa QueryFromConstraints
        haskey(env.constraints, e.constraints_name) || throw(CQLException(
            "Undefined constraints: $(e.constraints_name)"))
        c = env.constraints[e.constraints_name]
        _eval_query_from_constraints(c, e.index, env.options)
    elseif e isa QueryChase
        c = _resolve_constraints(env, e.constraints)
        q = eval_query(env, e.query)
        _chase_query(q, c, env.options)
    elseif e isa QueryReformulate
        c = _resolve_constraints(env, e.constraints)
        q = eval_query(env, e.query)
        t = eval_schema(env, e.schema)
        _reformulate_query(q, c, t, e.index, env.options)
    else
        throw(CQLException("Unknown query expression"))
    end
end

"""Resolve a constraints reference to a CQLConstraints object."""
function _resolve_constraints(env::Env, ref)::CQLConstraints
    if ref isa String
        haskey(env.constraints, ref) || throw(CQLException("Undefined constraints: $ref"))
        env.constraints[ref]
    else
        throw(CQLException("Expected constraints name, got: $ref"))
    end
end

# ============================================================================
# Query-level chase: chase each entity block's frozen instance with constraints
# ============================================================================

"""Chase a query with constraints: for each entity block, freeze it into an instance,
chase with constraints, and rebuild the query from the chased result."""
function _chase_query(q::CQLQuery, c::CQLConstraints, opts::CQLOptions)::CQLQuery
    # Only single-entity queries supported (matching Java)
    isempty(q.src.fks) || throw(CQLException("Fks not supported in chase query"))
    isempty(q.dst.fks) || throw(CQLException("Fks not supported in chase query"))

    new_ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}()
    new_atts = Dict{Symbol, CQLTerm}()
    vcounter = Ref(0)

    for (en, (ctx, where_eqs)) in q.ens
        # Build a frozen instance from this entity block
        gens = Dict{Symbol, Symbol}()
        sks = Dict{Symbol, Symbol}()
        for (v, entity) in ctx
            if entity in q.src.ens
                gens[v] = entity
            else
                sks[v] = entity
            end
        end

        inst_eqs = Set{Equation}()
        for eq in where_eqs
            lhs = _vars_to_gens_sks(eq.lhs, gens, sks)
            rhs = _vars_to_gens_sks(eq.rhs, gens, sks)
            push!(inst_eqs, Equation(lhs, rhs))
        end

        pres = Presentation(gens, sks, inst_eqs)

        if isempty(gens) && isempty(sks)
            new_ens[en] = (Dict{Symbol,Symbol}(), Set{Equation}())
            continue
        end

        # Build and chase the frozen instance
        col = presentation_to_collage(q.src, pres)
        prover = create_prover(col, opts)
        dp_fn = eq -> prover(Ctx(), eq)
        frozen_inst = initial_instance(pres, dp_fn, q.src; timeout_seconds=5, max_carrier_size=50)

        chased = chase(c, frozen_inst, opts)

        # Build gen/sk renaming maps from chased instance to fresh variable names
        gen_map = Dict{Symbol, Symbol}()
        sk_map = Dict{Symbol, Symbol}()
        new_ctx = Dict{Symbol, Symbol}()

        for (g, entity) in chased.pres.gens
            vcounter[] += 1
            fresh = Symbol("v", vcounter[])
            gen_map[g] = fresh
            new_ctx[fresh] = entity
        end
        for (s, ty) in chased.pres.sks
            vcounter[] += 1
            fresh = Symbol("v", vcounter[])
            sk_map[s] = fresh
            new_ctx[fresh] = ty
        end

        # Map equations through renaming
        new_where = Set{Equation}()
        for eq in chased.pres.eqs
            lhs = _rename_gen_sk(eq.lhs, gen_map, sk_map)
            rhs = _rename_gen_sk(eq.rhs, gen_map, sk_map)
            if lhs != rhs
                push!(new_where, Equation(lhs, rhs))
            end
        end

        new_ens[en] = (new_ctx, new_where)

        # Transform attribute terms through the chase
        # The chase produces a transform (identity on gens that survive):
        # we need to translate the original att terms through the chased instance
        for (att, _) in schema_atts_from(q.dst, en)
            if haskey(q.atts, att)
                orig_att_term = q.atts[att]
                # Translate through chase: substitute gens/sks with their chased representatives
                trans_term = _translate_through_chase(orig_att_term, chased, gens, sks)
                new_atts[att] = _rename_gen_sk(trans_term, gen_map, sk_map)
            end
        end
    end

    CQLQuery(q.src, q.dst, new_ens, Dict{Symbol,Dict{Symbol,CQLTerm}}(), new_atts)
end

"""Rename generators and skolems in a term."""
function _rename_gen_sk(t::CQLTerm, gen_map::Dict{Symbol,Symbol}, sk_map::Dict{Symbol,Symbol})::CQLTerm
    if t isa CQLGen
        haskey(gen_map, t.gen) ? CQLVar(gen_map[t.gen]) : CQLVar(t.gen)
    elseif t isa CQLSk
        haskey(sk_map, t.sk) ? CQLVar(sk_map[t.sk]) : CQLVar(t.sk)
    elseif t isa CQLVar
        t
    elseif t isa CQLFk
        CQLFk(t.fk, _rename_gen_sk(t.arg, gen_map, sk_map))
    elseif t isa CQLAtt
        CQLAtt(t.att, _rename_gen_sk(t.arg, gen_map, sk_map))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_rename_gen_sk(a, gen_map, sk_map) for a in t.args])
    else
        t
    end
end

"""Translate an attribute term through a chased instance.
The original term uses CQLVar names from the query context;
we convert to CQLGen/CQLSk then evaluate through the chased algebra."""
function _translate_through_chase(t::CQLTerm, chased::CQLInstance,
                                   gens::Dict{Symbol,Symbol}, sks::Dict{Symbol,Symbol})::CQLTerm
    # Convert query variables to instance generators/skolems
    inst_term = _vars_to_gens_sks(t, gens, sks)
    # Normalize through the chased instance's algebra
    _nf_through_instance(inst_term, chased)
end

"""Normalize a term through an instance's algebra, returning a term in gens/sks."""
function _nf_through_instance(t::CQLTerm, inst::CQLInstance)::CQLTerm
    if t isa CQLGen
        # Map through gen interpretation and back to repr
        if haskey(inst.algebra.gen, t.gen)
            x = inst.algebra.gen[t.gen]
            return inst.algebra.repr_x[x]
        end
        return t
    elseif t isa CQLSk
        return t
    elseif t isa CQLFk
        inner = _nf_through_instance(t.arg, inst)
        if inner isa CQLGen && haskey(inst.algebra.gen, inner.gen)
            x = inst.algebra.gen[inner.gen]
            if haskey(inst.algebra.fk, t.fk) && haskey(inst.algebra.fk[t.fk], x)
                result_x = inst.algebra.fk[t.fk][x]
                return inst.algebra.repr_x[result_x]
            end
        end
        return CQLFk(t.fk, inner)
    elseif t isa CQLAtt
        inner = _nf_through_instance(t.arg, inst)
        if inner isa CQLGen && haskey(inst.algebra.gen, inner.gen)
            x = inst.algebra.gen[inner.gen]
            if haskey(inst.algebra.repr_y, TalgGen(Right((x, t.att))))
                return inst.algebra.repr_y[TalgGen(Right((x, t.att)))]
            end
        end
        return CQLAtt(t.att, inner)
    elseif t isa CQLSym
        return CQLSym(t.sym, CQLTerm[_nf_through_instance(a, inst) for a in t.args])
    else
        return t
    end
end

# ============================================================================
# Reformulate: find minimal equivalent sub-queries
# ============================================================================

"""Reformulate query: find the N-th minimal sub-query equivalent to Q under constraints C,
preferring queries whose generators are in schema T."""
function _reformulate_query(q::CQLQuery, c::CQLConstraints, t::CQLSchema, idx::Int,
                            opts::CQLOptions)::CQLQuery
    length(q.ens) == 1 || throw(CQLException("Reformulate only supports single-entity queries"))
    isempty(q.src.fks) || throw(CQLException("Fks not supported in reformulate"))
    isempty(q.dst.fks) || throw(CQLException("Fks not supported in reformulate"))

    en_name = first(keys(q.ens))
    (ctx, where_eqs) = q.ens[en_name]

    # Classify context variables as entity-generators or type-skolems
    gens_set = Set{Symbol}()  # entity-sorted variables
    sks_set = Set{Symbol}()   # type-sorted variables
    for (v, entity) in ctx
        if entity in q.src.ens
            push!(gens_set, v)
        else
            push!(sks_set, v)
        end
    end

    # Build all candidate subsets of context variables
    all_vars = collect(keys(ctx))
    candidates = _power_set(all_vars)
    sort!(candidates; by=length)

    minimal_queries = CQLQuery[]

    for cand in candidates
        cand_set = Set(cand)

        # Build restricted context
        sub_ctx = Dict{Symbol,Symbol}(v => ctx[v] for v in cand if haskey(ctx, v))

        # Try to rewrite attribute terms using only candidate variables
        sub_gens = Dict{Symbol,Symbol}(v => ctx[v] for v in cand if v in gens_set)
        sub_sks = Dict{Symbol,Symbol}(v => ctx[v] for v in cand if v in sks_set)

        att_terms = Pair{Symbol, CQLTerm}[]
        valid = true
        for (att, term) in q.atts
            rewritten = _rewrite_term_to_subset(term, where_eqs, q.src, sub_gens, sub_sks, cand_set)
            if rewritten === nothing
                valid = false
                break
            end
            push!(att_terms, att => rewritten)
        end
        valid || continue

        # Extract equations that hold within the subset
        sub_where = Set{Equation}()
        for eq in where_eqs
            if _term_uses_only(eq.lhs, cand_set) && _term_uses_only(eq.rhs, cand_set)
                push!(sub_where, eq)
            end
        end

        sub_ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}(
            en_name => (sub_ctx, sub_where)
        )
        sub_atts = Dict{Symbol, CQLTerm}(att_terms)
        sub_q = CQLQuery(q.src, q.dst, sub_ens, Dict{Symbol,Dict{Symbol,CQLTerm}}(), sub_atts)

        # Check bidirectional containment under constraints
        # sq ⊆_C q: find hom from q into chase(sq, C)
        # q ⊆_C sq: find hom from sq into chase(q, C)
        chased_sq = _chase_query(sub_q, c, opts)
        if _query_hom(q, chased_sq, opts) === nothing
            continue
        end

        chased_q = _chase_query(q, c, opts)
        if _query_hom(sub_q, chased_q, opts) !== nothing
            push!(minimal_queries, sub_q)
        end
    end

    isempty(minimal_queries) && throw(CQLException(
        "No equivalent minimal queries found (index $idx)"))

    # Score and sort: prefer queries with fewer generators outside T
    sort!(minimal_queries; by = mq -> begin
        s = _score_query(mq, t)
        n = sum(length(ctx2) for (_, (ctx2, _)) in mq.ens; init=0)
        (s, n)
    end)

    idx < length(minimal_queries) || throw(CQLException(
        "Reformulate index $idx out of range (only $(length(minimal_queries)) candidates)"))

    minimal_queries[idx + 1]  # 0-indexed in CQL syntax
end

"""Score a query by counting generators outside schema T."""
function _score_query(q::CQLQuery, t::CQLSchema)::Int
    count = 0
    for (_, (ctx, _)) in q.ens
        for (_, entity) in ctx
            if !(entity in t.ens)
                count += 1
            end
        end
    end
    count
end

"""Generate the power set of a vector."""
function _power_set(items::Vector{T}) where T
    result = Vector{T}[]
    n = length(items)
    for mask in 0:(2^n - 1)
        subset = T[]
        for i in 1:n
            if (mask >> (i-1)) & 1 == 1
                push!(subset, items[i])
            end
        end
        push!(result, subset)
    end
    result
end

"""Check if a term only uses variables from the given set."""
function _term_uses_only(t::CQLTerm, vars::Set{Symbol})::Bool
    if t isa CQLVar
        t.name in vars
    elseif t isa CQLFk
        _term_uses_only(t.arg, vars)
    elseif t isa CQLAtt
        _term_uses_only(t.arg, vars)
    elseif t isa CQLSym
        all(a -> _term_uses_only(a, vars), t.args)
    elseif t isa CQLGen || t isa CQLSk
        true  # constants don't reference variables
    else
        true
    end
end

"""Try to rewrite a term so it only references variables in the subset.
Uses the where-clause equations and the decision procedure to find equivalent terms."""
function _rewrite_term_to_subset(t::CQLTerm, where_eqs::Set{Equation}, src::CQLSchema,
                                  sub_gens::Dict{Symbol,Symbol}, sub_sks::Dict{Symbol,Symbol},
                                  cand_set::Set{Symbol})::Union{CQLTerm, Nothing}
    if _term_uses_only(t, cand_set)
        return t
    end

    # For attribute terms Att(att, Var(v)) where v is not in subset:
    # try to find an equivalent att on a variable that IS in the subset
    if t isa CQLAtt && t.arg isa CQLVar && !(t.arg.name in cand_set)
        # Find a generator in subset of the same entity with a provably-equal attribute
        missing_var = t.arg.name
        for (v, en) in sub_gens
            # Check if any equation in where_eqs implies att(v) = att(missing_var)
            # by looking for equations like v.fk = missing_var or direct equality
            for eq in where_eqs
                matched = _match_att_rewrite(t, v, eq)
                if matched !== nothing
                    return matched
                end
            end
            # Also try direct attribute on same-type generators
            for (a, (src_en, _)) in src.atts
                if a == t.att && src_en == en
                    candidate = CQLAtt(a, CQLVar(v))
                    # Check via where-clause if this is equivalent
                    if _terms_equal_via_where(t, candidate, where_eqs, src)
                        return candidate
                    end
                end
            end
        end
        return nothing
    end

    if t isa CQLSym
        new_args = CQLTerm[]
        for a in t.args
            ra = _rewrite_term_to_subset(a, where_eqs, src, sub_gens, sub_sks, cand_set)
            ra === nothing && return nothing
            push!(new_args, ra)
        end
        return CQLSym(t.sym, new_args)
    end

    if t isa CQLFk
        ra = _rewrite_term_to_subset(t.arg, where_eqs, src, sub_gens, sub_sks, cand_set)
        ra === nothing && return nothing
        return CQLFk(t.fk, ra)
    end

    nothing
end

"""Try to match an attribute rewrite through an equation."""
function _match_att_rewrite(t::CQLTerm, candidate_var::Symbol, eq::Equation)::Union{CQLTerm, Nothing}
    # If equation is v.att = x.att or similar, and t references x, try v
    nothing
end

"""Check if two terms are equal given where-clause equations (syntactic check)."""
function _terms_equal_via_where(t1::CQLTerm, t2::CQLTerm, where_eqs::Set{Equation},
                                 src::CQLSchema)::Bool
    t1 == t2 && return true
    for eq in where_eqs
        if (eq.lhs == t1 && eq.rhs == t2) || (eq.lhs == t2 && eq.rhs == t1)
            return true
        end
    end
    false
end

"""Find a homomorphism from query q1 into query q2, or return nothing.
A homomorphism maps q1's generators/skolems to q2's such that equations are preserved."""
function _query_hom(q1::CQLQuery, q2::CQLQuery, opts::CQLOptions)
    q1.ens |> keys |> collect |> sort == q2.ens |> keys |> collect |> sort || return nothing
    length(q1.ens) == 1 || return nothing

    en = first(keys(q1.ens))
    (ctx1, where1) = q1.ens[en]
    (ctx2, where2) = q2.ens[en]

    # Build candidate mappings: each q1 variable maps to a q2 variable of same type
    vars1 = collect(ctx1)
    if isempty(vars1)
        # Check attributes match
        for (att, t1) in q1.atts
            haskey(q2.atts, att) || return nothing
            t1 == q2.atts[att] || return nothing
        end
        return Dict{Symbol,Symbol}()
    end

    # Build frozen instances for both queries
    gens1 = Dict{Symbol,Symbol}(v => en for (v, en) in ctx1 if en in q1.src.ens)
    sks1 = Dict{Symbol,Symbol}(v => en for (v, en) in ctx1 if !(en in q1.src.ens))
    gens2 = Dict{Symbol,Symbol}(v => en for (v, en) in ctx2 if en in q2.src.ens)
    sks2 = Dict{Symbol,Symbol}(v => en for (v, en) in ctx2 if !(en in q2.src.ens))

    # Build all possible assignments of q1 entity-gens to q2 entity-gens (same entity type)
    assignments = [Dict{Symbol,Symbol}()]
    for (g1, en1) in gens1
        new_assignments = Dict{Symbol,Symbol}[]
        for (g2, en2) in gens2
            if en1 == en2
                for a in assignments
                    na = copy(a)
                    na[g1] = g2
                    push!(new_assignments, na)
                end
            end
        end
        isempty(new_assignments) && return nothing
        assignments = new_assignments
    end

    # Also map skolems
    for (s1, ty1) in sks1
        new_assignments = Dict{Symbol,Symbol}[]
        for (s2, ty2) in sks2
            if ty1 == ty2
                for a in assignments
                    na = copy(a)
                    na[s1] = s2
                    push!(new_assignments, na)
                end
            end
        end
        isempty(new_assignments) && return nothing
        assignments = new_assignments
    end

    # Build frozen instance for q2 to check equations
    inst2_eqs = Set{Equation}()
    for eq in where2
        lhs = _vars_to_gens_sks(eq.lhs, gens2, sks2)
        rhs = _vars_to_gens_sks(eq.rhs, gens2, sks2)
        push!(inst2_eqs, Equation(lhs, rhs))
    end
    pres2 = Presentation(gens2, sks2, inst2_eqs)

    # Build prover for q2
    local dp2
    try
        col2 = presentation_to_collage(q2.src, pres2)
        prover2 = create_prover(col2, opts)
        dp2 = eq -> prover2(Ctx(), eq)
    catch
        return nothing
    end

    inst2 = try
        initial_instance(pres2, dp2, q2.src; timeout_seconds=5, max_carrier_size=50)
    catch
        return nothing
    end

    # Try each candidate assignment
    for assign in assignments
        valid = true

        # Check where-clause equations are preserved
        for eq in where1
            lhs1 = _vars_to_gens_sks(eq.lhs, gens1, sks1)
            rhs1 = _vars_to_gens_sks(eq.rhs, gens1, sks1)
            lhs2 = _apply_gen_sk_mapping(lhs1, assign)
            rhs2 = _apply_gen_sk_mapping(rhs1, assign)
            if !dp2(Equation(lhs2, rhs2))
                valid = false
                break
            end
        end
        valid || continue

        # Check attribute terms are preserved
        all_atts_ok = true
        for (att, t1) in q1.atts
            haskey(q2.atts, att) || (all_atts_ok = false; break)
            t2 = q2.atts[att]
            # Apply assignment to t1
            mapped_t1 = _apply_var_mapping(t1, assign)
            inst_t1 = _vars_to_gens_sks(mapped_t1, gens2, sks2)
            inst_t2 = _vars_to_gens_sks(t2, gens2, sks2)
            if !dp2(Equation(inst_t1, inst_t2))
                all_atts_ok = false
                break
            end
        end
        all_atts_ok || continue

        return assign
    end

    nothing
end

"""Apply a variable-to-variable mapping to a term."""
function _apply_var_mapping(t::CQLTerm, mapping::Dict{Symbol,Symbol})::CQLTerm
    if t isa CQLVar
        haskey(mapping, t.name) ? CQLVar(mapping[t.name]) : t
    elseif t isa CQLFk
        CQLFk(t.fk, _apply_var_mapping(t.arg, mapping))
    elseif t isa CQLAtt
        CQLAtt(t.att, _apply_var_mapping(t.arg, mapping))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_apply_var_mapping(a, mapping) for a in t.args])
    else
        t
    end
end

"""Apply a gen/sk name mapping to an instance-level term."""
function _apply_gen_sk_mapping(t::CQLTerm, mapping::Dict{Symbol,Symbol})::CQLTerm
    if t isa CQLGen
        haskey(mapping, t.gen) ? CQLGen(mapping[t.gen]) : t
    elseif t isa CQLSk
        haskey(mapping, t.sk) ? CQLSk(mapping[t.sk]) : t
    elseif t isa CQLFk
        CQLFk(t.fk, _apply_gen_sk_mapping(t.arg, mapping))
    elseif t isa CQLAtt
        CQLAtt(t.att, _apply_gen_sk_mapping(t.arg, mapping))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_apply_gen_sk_mapping(a, mapping) for a in t.args])
    else
        t
    end
end

"""Build target schema for a simple query: one entity with attributes inferred from query definition."""
function _build_simple_query_target(src::CQLSchema, raw::QueryExpRaw)::CQLSchema
    ts = src.typeside

    # Get entity name from options
    en_name = :Q  # default
    for (k, v) in raw.options
        if k == "simple_query_entity"
            en_name = Symbol(v)
        end
    end

    ens = Set{Symbol}([en_name])
    fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    atts = Dict{Symbol, Tuple{Symbol, Symbol}}()

    (from_bindings, _, att_raw, fk_raw) = raw.ens[1][2]

    # Build from-clause context for type inference
    ctx = Dict{Symbol,Symbol}()
    for (v, e) in from_bindings
        ctx[Symbol(v)] = Symbol(e)
    end

    # Infer attribute types from source schema terms
    for (att_name, att_term_raw) in att_raw
        att_type = _infer_raw_term_type(src, ctx, att_term_raw)
        atts[Symbol(att_name)] = (en_name, att_type)
    end

    # FK mappings define foreign keys on the target
    for (fk_name, _) in fk_raw
        fks[Symbol(fk_name)] = (en_name, en_name)  # self-referencing by default
    end

    eq_fn = (en, eq) -> false
    CQLSchema(ts, ens, fks, atts, Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(), eq_fn)
end

"""Infer the type of a raw term in the context of a source schema."""
function _infer_raw_term_type(src::CQLSchema, ctx::Dict{Symbol,Symbol}, raw::RawTerm)::Symbol
    s = Symbol(raw.head)
    if isempty(raw.args)
        # Variable or constant
        if haskey(ctx, s) && s in src.ens
            return s
        end
        # Unknown — return first typeside type as default
        return isempty(src.typeside.tys) ? :String : first(src.typeside.tys)
    elseif length(raw.args) == 1
        if haskey(src.atts, s)
            return src.atts[s][2]  # return type of attribute
        elseif haskey(src.fks, s)
            return src.fks[s][2]  # target entity of FK
        end
        # Check if parent has the info
        inner_entity = _infer_raw_term_entity(src, ctx, raw.args[1])
        if inner_entity !== nothing
            # Try to find att/fk from this entity
            if haskey(src.atts, s)
                return src.atts[s][2]
            end
        end
    end
    # Default fallback
    isempty(src.typeside.tys) ? :String : first(src.typeside.tys)
end

"""Infer the entity type of a raw term."""
function _infer_raw_term_entity(src::CQLSchema, ctx::Dict{Symbol,Symbol}, raw::RawTerm)::Union{Symbol, Nothing}
    s = Symbol(raw.head)
    if isempty(raw.args) && haskey(ctx, s)
        return ctx[s]
    elseif length(raw.args) == 1 && haskey(src.fks, s)
        return src.fks[s][2]
    end
    nothing
end

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

# ============================================================================
# Pivot: instance -> schema + mapping
# ============================================================================

"""
Compute the pivot schema of an instance.

Given instance I on schema S, pivot(I) is a schema where:
- Each carrier element becomes an entity
- Each FK application becomes a FK in the pivot schema
- Each attribute becomes an attribute in the pivot schema
"""
function _pivot_schema(inst::CQLInstance)::CQLSchema
    alg = inst.algebra
    sch = inst.schema
    ts = sch.typeside

    pivot_ens = Set{Symbol}()
    pivot_fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    pivot_atts = Dict{Symbol, Tuple{Symbol, Symbol}}()
    pivot_path_eqs = Set{Tuple{Symbol, Equation}}()

    # Build entity for each carrier element
    for (en, elements) in alg.en
        for x in elements
            x_name = _element_name(alg, x)
            push!(pivot_ens, x_name)
        end
    end

    # Build FKs: for each original FK f: E1 -> E2, and each element x in E1,
    # create FK f: x -> f(x)
    fk_by_name = Dict{Symbol, Vector{Symbol}}()
    for (fk_name, (src_en, tgt_en)) in sch.fks
        for x in carrier(alg, src_en)
            y = eval_fk(alg, fk_name, x)
            x_name = _element_name(alg, x)
            y_name = _element_name(alg, y)
            # Qualify FK name with source entity to avoid collisions
            qualified_fk = Symbol(x_name, :__, fk_name)
            pivot_fks[qualified_fk] = (x_name, y_name)
            # Track plain FK name for resolution
            plain = fk_name
            if !haskey(fk_by_name, plain)
                fk_by_name[plain] = Symbol[]
            end
            push!(fk_by_name[plain], qualified_fk)
        end
    end

    # Build attributes: for each original att a: E -> T, and each element x in E,
    # create att a: x -> T
    att_by_name = Dict{Symbol, Vector{Symbol}}()
    for (att_name, (src_en, tgt_ty)) in sch.atts
        for x in carrier(alg, src_en)
            x_name = _element_name(alg, x)
            qualified_att = Symbol(x_name, :__, att_name)
            pivot_atts[qualified_att] = (x_name, tgt_ty)
            plain = att_name
            if !haskey(att_by_name, plain)
                att_by_name[plain] = Symbol[]
            end
            push!(att_by_name[plain], qualified_att)
        end
    end

    # Build path equations from FK composition
    # For each path equation forall x:E . f.g(x) = h(x) in the original schema,
    # we get for each element e in carrier(E): fk_g(fk_f(e)) = fk_h(e) in pivot schema
    for (en, eq) in sch.path_eqs
        for x in carrier(alg, en)
            x_name = _element_name(alg, x)
            lhs = _translate_pivot_path(alg, eq.lhs, x, x_name)
            rhs = _translate_pivot_path(alg, eq.rhs, x, x_name)
            if lhs !== nothing && rhs !== nothing
                push!(pivot_path_eqs, (x_name, Equation(lhs, rhs)))
            end
        end
    end

    eq_fn = (en, eq) -> eq.lhs == eq.rhs
    CQLSchema(ts, pivot_ens, pivot_fks, pivot_atts, pivot_path_eqs,
              Set{Tuple{Symbol,Equation}}(), eq_fn, fk_by_name, att_by_name, collect(keys(pivot_fks)))
end

"""Build the pseudo-quotient mapping: colimit_schema → quotient_schema.

For pseudo_quotient with entity_isomorphisms (e.g., p : S1.A -> S2.A),
creates a quotient schema that merges isomorphic entities and maps the
colimit schema to it. If no entity_isos, returns identity mapping."""
function _eval_get_pseudo(colimit::SchemaColimitResult, opts::CQLOptions)::CQLMapping
    if isempty(colimit.entity_isos)
        return identity_mapping(colimit.schema)
    end

    src_sch = colimit.schema
    ts = src_sch.typeside

    # Build union-find for entity merging based on entity_isos
    uf = Dict{Symbol, Symbol}()  # entity → representative
    for en in src_sch.ens
        uf[en] = en
    end

    function uf_find(x)
        while uf[x] != x
            uf[x] = uf[uf[x]]
            x = uf[x]
        end
        x
    end

    function uf_union(a, b)
        ra = uf_find(a)
        rb = uf_find(b)
        if ra != rb
            # Prefer shorter name as canonical
            if length(string(ra)) <= length(string(rb))
                uf[rb] = ra
            else
                uf[ra] = rb
            end
        end
    end

    # Parse entity_isos dotted names to find which entities to merge
    for (_, src_dotted, tgt_dotted) in colimit.entity_isos
        # Parse "SchemaName.EntityName" → prefixed entity
        src_en = _resolve_dotted_entity(src_dotted, colimit)
        tgt_en = _resolve_dotted_entity(tgt_dotted, colimit)
        if src_en !== nothing && tgt_en !== nothing
            uf_union(src_en, tgt_en)
        end
    end

    # Build canonical entity mapping
    en_map = Dict{Symbol, Symbol}()
    for en in src_sch.ens
        canon = uf_find(en)
        # Strip schema prefix from canonical name for cleaner output
        en_map[en] = _strip_schema_prefix(canon, colimit.names)
    end

    # Build quotient entity set
    quot_ens = Set{Symbol}(values(en_map))

    # Build quotient FKs (skip iso FKs and their inverses)
    iso_fk_names = Set{Symbol}()
    for (name, _, _) in colimit.entity_isos
        push!(iso_fk_names, Symbol(name))
        push!(iso_fk_names, Symbol(name, "_inv"))
    end

    quot_fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    fk_map = Dict{Symbol, CQLTerm}()  # src FK → dst FK term
    entity_fk_names = Dict{Symbol, Set{Symbol}}()  # entity → set of stripped FK names
    for (fk, (src, tgt)) in src_sch.fks
        if fk in iso_fk_names
            # Isomorphism FK maps to identity in quotient
            fk_map[fk] = CQLVar(Symbol("_unit"))
            continue
        end
        qsrc = en_map[src]
        qtgt = en_map[tgt]
        # Strip schema prefix from FK name
        stripped = _strip_schema_prefix(fk, colimit.names)
        # Also strip entity prefix from FK name
        stripped = _strip_pseudo_entity_prefix(stripped, qsrc)
        # Check for same-entity collision
        used = get!(entity_fk_names, qsrc, Set{Symbol}())
        if stripped in used
            stripped = fk  # keep full colimit name
        end
        push!(used, stripped)
        # Use Entity__stripped as dict key for cross-entity scoping
        qfk = Symbol(qsrc, "__", stripped)
        quot_fks[qfk] = (qsrc, qtgt)
        fk_map[fk] = CQLFk(qfk, CQLVar(Symbol("_unit")))
    end

    # Build attribute equivalences from obs_eqs.
    # Obs_eqs like "att1(x) = att2(iso_fk(x))" tell us att1 and att2 are the
    # same attribute after entity merging, and one should be eliminated.
    att_uf = Dict{Symbol, Symbol}()  # union-find for colimit att names
    for (att, _) in src_sch.atts
        att_uf[att] = att
    end
    function att_find(x)
        while att_uf[x] != x
            att_uf[x] = att_uf[att_uf[x]]
            x = att_uf[x]
        end
        x
    end

    for (_, eq) in src_sch.obs_eqs
        lhs_att = _extract_pseudo_att(eq.lhs, iso_fk_names)
        rhs_att = _extract_pseudo_att(eq.rhs, iso_fk_names)
        if lhs_att !== nothing && rhs_att !== nothing && lhs_att != rhs_att
            ra = att_find(lhs_att)
            rb = att_find(rhs_att)
            ra != rb && (att_uf[rb] = ra)  # prefer LHS as representative
        end
    end

    # Build quotient attributes using equivalence classes.
    # Attributes in the same equiv class (via obs_eqs) share one quotient name.
    # Use Entity__att format to scope names per entity (matching Java's per-entity
    # attribute scoping). _simplify_att_name in the dump script strips Entity__ prefixes.
    # For same-entity name collisions (e.g., two different IDs from merged schemas),
    # the second keeps its full colimit name (matching Java).
    quot_atts = Dict{Symbol, Tuple{Symbol, Symbol}}()
    att_map = Dict{Symbol, CQLTerm}()
    rep_to_qatt = Dict{Symbol, Symbol}()  # representative colimit att → quotient att name
    # Track stripped names per entity to detect same-entity collisions
    entity_att_names = Dict{Symbol, Set{Symbol}}()  # entity → set of stripped names used

    for (att, (src, ty)) in sort(collect(src_sch.atts), by=x->string(x[1]))
        qsrc = en_map[src]
        rep = att_find(att)

        if haskey(rep_to_qatt, rep)
            # Already have a quotient att for this equivalence class
            att_map[att] = CQLAtt(rep_to_qatt[rep], CQLVar(Symbol("_unit")))
            continue
        end

        # Compute stripped name (remove schema and entity prefixes)
        stripped = _strip_schema_prefix(att, colimit.names)
        stripped = _strip_pseudo_entity_prefix(stripped, qsrc)

        # Check for same-entity collision
        used = get!(entity_att_names, qsrc, Set{Symbol}())
        if stripped in used
            # Same-entity collision: keep full colimit name (e.g., Olog2Schema_Patient_ID)
            stripped = att
        end
        push!(used, stripped)

        # Use Entity__stripped as the dict key to avoid cross-entity collisions
        qatt = Symbol(qsrc, "__", stripped)

        rep_to_qatt[rep] = qatt
        quot_atts[qatt] = (qsrc, ty)
        att_map[att] = CQLAtt(qatt, CQLVar(Symbol("_unit")))
    end

    # Build quotient path equations
    quot_path_eqs = Set{Tuple{Symbol, Equation}}()
    for (en, eq) in src_sch.path_eqs
        qen = en_map[en]
        new_lhs = _translate_pseudo_term(eq.lhs, fk_map)
        new_rhs = _translate_pseudo_term(eq.rhs, fk_map)
        if new_lhs != new_rhs
            push!(quot_path_eqs, (qen, Equation(new_lhs, new_rhs)))
        end
    end

    # Build quotient obs equations
    quot_obs_eqs = Set{Tuple{Symbol, Equation}}()
    for (en, eq) in src_sch.obs_eqs
        qen = en_map[en]
        new_lhs = _translate_pseudo_type_term(eq.lhs, fk_map, att_map)
        new_rhs = _translate_pseudo_type_term(eq.rhs, fk_map, att_map)
        if new_lhs != new_rhs
            push!(quot_obs_eqs, (qen, Equation(new_lhs, new_rhs)))
        end
    end

    quot_fk_by_name = _build_pseudo_by_name(quot_fks)
    quot_att_by_name = _build_pseudo_by_name(quot_atts)

    eq_fn = (en, eq) -> eq.lhs == eq.rhs  # simple equality for now
    quot_sch = CQLSchema(ts, quot_ens, quot_fks, quot_atts,
                          quot_path_eqs, quot_obs_eqs, eq_fn,
                          quot_fk_by_name, quot_att_by_name,
                          collect(keys(quot_fks)))

    CQLMapping(src_sch, quot_sch, en_map, fk_map, att_map)
end

"""Extract attribute name from an obs_eq term that is att(fk_chain(var)) where
all FKs in the chain are isomorphism FKs (which become identity in quotient)."""
function _extract_pseudo_att(t::CQLTerm, iso_fk_names::Set{Symbol})::Union{Symbol, Nothing}
    t isa CQLAtt || return nothing
    inner = t.arg
    while inner isa CQLFk
        inner.fk in iso_fk_names || return nothing
        inner = inner.arg
    end
    inner isa CQLVar ? t.att : nothing
end

"""Resolve a dotted entity name like 'Olog1Schema.Patient' to a prefixed entity in the colimit."""
function _resolve_dotted_entity(dotted::String, colimit::SchemaColimitResult)::Union{Symbol, Nothing}
    parts = split(dotted, ".")
    if length(parts) == 2
        prefixed = Symbol(parts[1], "_", parts[2])
        prefixed in colimit.schema.ens && return prefixed
    end
    nothing
end

"""Strip schema prefix from a symbol name. E.g., Olog1Schema_Patient → Patient."""
function _strip_schema_prefix(name::Symbol, schema_names::Vector{String})::Symbol
    s = string(name)
    for sn in schema_names
        prefix = sn * "_"
        if startswith(s, prefix)
            # Strip the first matching prefix
            stripped = s[length(prefix)+1:end]
            return Symbol(stripped)
        end
    end
    name
end

"""Strip entity prefix from an attribute/FK name if it matches.
E.g., Observation_ID → ID when entity is Observation.
Only strips if entity name has >= 3 chars (avoids false positives with short entity names
like G, P, T which may have attributes like G_att that are NOT entity-prefixed)."""
function _strip_pseudo_entity_prefix(name::Symbol, entity::Symbol)::Symbol
    s = string(name)
    en = string(entity)
    length(en) < 3 && return name  # don't strip short entity prefixes
    prefix = en * "_"
    if startswith(s, prefix) && length(s) > length(prefix)
        stripped = s[length(prefix)+1:end]
        # Don't strip if result starts with _ (would create invalid name)
        startswith(stripped, '_') && return name
        return Symbol(stripped)
    end
    name
end

"""Translate an entity-side term through the pseudo-quotient mapping."""
function _translate_pseudo_term(t::CQLTerm, fk_map::Dict{Symbol, CQLTerm})::CQLTerm
    if t isa CQLVar
        t
    elseif t isa CQLFk
        mapped = fk_map[t.fk]
        if mapped isa CQLVar
            # Identity FK (iso) — skip it
            _translate_pseudo_term(t.arg, fk_map)
        elseif mapped isa CQLFk
            CQLFk(mapped.fk, _translate_pseudo_term(t.arg, fk_map))
        else
            t
        end
    else
        t
    end
end

"""Translate a type-side term through the pseudo-quotient mapping."""
function _translate_pseudo_type_term(t::CQLTerm, fk_map::Dict{Symbol, CQLTerm}, att_map::Dict{Symbol, CQLTerm})::CQLTerm
    if t isa CQLAtt
        mapped = att_map[t.att]
        if mapped isa CQLAtt
            CQLAtt(mapped.att, _translate_pseudo_term(t.arg, fk_map))
        else
            t
        end
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_translate_pseudo_type_term(a, fk_map, att_map) for a in t.args])
    else
        t
    end
end

function _build_pseudo_by_name(dict)
    by_name = Dict{Symbol, Vector{Symbol}}()
    for name in keys(dict)
        s = string(name)
        # Extract short name (last part after last _)
        parts = split(s, "_")
        if length(parts) > 1
            short = Symbol(parts[end])
            push!(get!(by_name, short, Symbol[]), name)
        end
    end
    by_name
end

"""Compute the pivot mapping: pivot(I) -> S.

Maps each element entity back to its original entity,
and each qualified FK/att back to the original FK/att."""
function _pivot_mapping(inst::CQLInstance)::CQLMapping
    alg = inst.algebra
    sch = inst.schema
    pivot_sch = _pivot_schema(inst)

    ens = Dict{Symbol, Symbol}()
    fks_map = Dict{Symbol, CQLTerm}()
    atts_map = Dict{Symbol, CQLTerm}()

    # Map each element entity to its original entity
    for (en, elements) in alg.en
        for x in elements
            x_name = _element_name(alg, x)
            ens[x_name] = en
        end
    end

    # Map each qualified FK to identity path through the original FK
    for (qfk, (src_elem, tgt_elem)) in pivot_sch.fks
        # qfk = elem__fk_name, extract the original fk_name
        s = string(qfk)
        parts = split(s, "__")
        orig_fk = Symbol(parts[end])
        fks_map[qfk] = CQLFk(orig_fk, CQLVar(:_unit))
    end

    # Map each qualified att to the original attribute
    for (qatt, (src_elem, tgt_ty)) in pivot_sch.atts
        s = string(qatt)
        parts = split(s, "__")
        orig_att = Symbol(parts[end])
        atts_map[qatt] = CQLAtt(orig_att, CQLVar(:_unit))
    end

    CQLMapping(pivot_sch, sch, ens, fks_map, atts_map)
end

"""Get a stable name for an algebra carrier element."""
function _element_name(alg::Algebra, x)::Symbol
    t = repr_x(alg, x)
    if t isa CQLGen
        return t.gen
    else
        return Symbol(string(t))
    end
end

"""Translate a path equation term to pivot schema FKs."""
function _translate_pivot_path(alg::Algebra, t::CQLTerm, base_x, base_name::Symbol)::Union{CQLTerm, Nothing}
    if t isa CQLVar
        return CQLVar(:_unit)
    elseif t isa CQLFk
        inner_term = _translate_pivot_path(alg, t.arg, base_x, base_name)
        inner_term === nothing && return nothing
        # Evaluate the inner term to get the element it refers to
        inner_elem = _eval_pivot_inner(alg, t.arg, base_x)
        inner_elem === nothing && return nothing
        inner_name = _element_name(alg, inner_elem)
        qfk = Symbol(inner_name, :__, t.fk)
        return CQLFk(qfk, inner_term)
    else
        return nothing
    end
end

"""Evaluate an entity-side term starting from a base element."""
function _eval_pivot_inner(alg::Algebra, t::CQLTerm, base_x)
    if t isa CQLVar
        return base_x
    elseif t isa CQLFk
        inner = _eval_pivot_inner(alg, t.arg, base_x)
        inner === nothing && return nothing
        return eval_fk(alg, t.fk, inner)
    else
        return nothing
    end
end

# ============================================================================
# Transform operations: include, except, distinct
# ============================================================================

"""Inclusion transform: I1 → I2 where I1's generators are a subset of I2's.
Maps each I1 generator to the corresponding I2 generator."""
function _eval_include_transform(i1::CQLInstance, i2::CQLInstance)::CQLTransform
    gens = Dict{Symbol, CQLTerm}()
    for (g, en) in i1.pres.gens
        if haskey(i2.pres.gens, g)
            gens[g] = CQLGen(g)
        else
            # Try to find matching element by evaluating in i2's algebra
            gens[g] = CQLGen(g)
        end
    end
    sks = Dict{Symbol, CQLTerm}(s => CQLSk(s) for s in keys(i1.pres.sks))
    CQLTransform(i1, i2, gens, sks)
end

"""Except-return transform: inclusion from (I1 \\ I2) → I1.
Computes the set difference of instances and returns the inclusion."""
function _eval_except_return_transform(i1::CQLInstance, i2::CQLInstance)::CQLTransform
    except_inst = eval_except_instance(i1, i2, default_options())

    # The inclusion maps each remaining gen to itself in I1
    gens = Dict{Symbol, CQLTerm}(g => CQLGen(g) for g in keys(except_inst.pres.gens))
    sks = Dict{Symbol, CQLTerm}(s => CQLSk(s) for s in keys(except_inst.pres.sks))
    CQLTransform(except_inst, i1, gens, sks)
end

"""Except transform: given T: I1 → I2 and instance I, return except(T, I)."""
function _eval_except_transform(t::CQLTransform, i::CQLInstance)::CQLTransform
    # except(T, I) removes from T the parts corresponding to I
    # For identity transforms, the result is identity on the except instance
    except_src = _eval_except_return_transform(t.src, i)
    except_dst = _eval_except_return_transform(t.dst, i)

    gens = Dict{Symbol, CQLTerm}()
    for (g, _) in except_src.src.pres.gens
        if haskey(t.gens, g)
            gens[g] = t.gens[g]
        else
            gens[g] = CQLGen(g)
        end
    end
    sks = Dict{Symbol, CQLTerm}(s => CQLSk(s) for s in keys(except_src.src.pres.sks))
    CQLTransform(except_src.src, except_dst.src, gens, sks)
end

"""Distinct transform: apply quotient/distinctness to a transform."""
function _eval_distinct_transform(t::CQLTransform)::CQLTransform
    # For identity-like transforms, return identity
    # In general, distinct merges duplicate generators
    t  # Pass through — in CQL, distinct on transforms is the identity for transforms between identical instances
end

"""Distinct-return transform: inclusion from distinct(I) → I."""
function _eval_distinct_return_transform(i::CQLInstance)::CQLTransform
    # The distinct operation merges elements that are provably equal
    # For already-normalized instances, this is identity
    identity_transform(i)
end

# ============================================================================
# Coeval: right adjoint to query evaluation
# ============================================================================

"""
Evaluate coeval instance: given Q: S → T and instance J on T (= Q.dst),
produce an instance on S (= Q.src).

For each target entity t in Q.dst and element j ∈ J(t), and for each
from-variable v in Q.ens[t] of source entity type s, we create a generator
of entity s. We then add equations from:
1. Where-clauses of Q.ens[t]
2. FK edges in Q.fks
3. Attribute definitions in Q.atts
"""
function eval_coeval_instance(q::CQLQuery, inst::CQLInstance, opts::CQLOptions)
    alg = inst.algebra

    # Generator names and lookup: (variable, element, dst_entity) → Symbol
    gens = Dict{Symbol, Symbol}()  # gen_name → Q.src entity
    gen_lookup = Dict{Tuple{Symbol, Any, Symbol}, Symbol}()

    counter = Ref(0)
    function make_gen(v::Symbol, j, en::Symbol)::Symbol
        key = (v, j, en)
        r = get(gen_lookup, key, nothing)
        r !== nothing && return r
        counter[] += 1
        name = Symbol("ce", counter[])
        gen_lookup[key] = name
        return name
    end

    sks = Dict{Symbol, Symbol}()  # sk_name → typeside type
    gen_order = Symbol[]

    # Create generators: for each Q.dst entity, each element in J, each from-variable
    for (dst_en, (ctx, _)) in q.ens
        for j in carrier(alg, dst_en)
            for (v, src_en) in ctx
                g = make_gen(v, j, dst_en)
                if src_en in q.src.ens
                    gens[g] = src_en
                    push!(gen_order, g)
                else
                    # Type-sorted variable: create a Skolem constant
                    sks[g] = src_en
                end
            end
        end
    end

    eqs = Set{Equation}()

    # Variable substitution: replace CQLVar(v) with CQLGen (entity) or CQLSk (type) for the coeval
    function _coeval_subst(t::CQLTerm, j, en::Symbol)::CQLTerm
        if t isa CQLVar
            g = get(gen_lookup, (t.name, j, en), nothing)
            g !== nothing && return haskey(sks, g) ? CQLSk(g) : CQLGen(g)
            error("Coeval: variable $(t.name) not found in context for entity $en")
        elseif t isa CQLFk
            CQLFk(t.fk, _coeval_subst(t.arg, j, en))
        elseif t isa CQLAtt
            CQLAtt(t.att, _coeval_subst(t.arg, j, en))
        elseif t isa CQLSym
            CQLSym(t.sym, CQLTerm[_coeval_subst(a, j, en) for a in t.args])
        else
            t  # CQLGen, CQLSk stay as-is
        end
    end

    # 1. Where-clause equations
    for (dst_en, (_, where_eqs)) in q.ens
        for j in carrier(alg, dst_en)
            for eq in where_eqs
                push!(eqs, Equation(
                    _coeval_subst(eq.lhs, j, dst_en),
                    _coeval_subst(eq.rhs, j, dst_en)))
            end
        end
    end

    # 2. FK equations: for each FK fk: src_en → tgt_en in Q.dst
    for (fk_name, var_mapping) in q.fks
        (fk_src_en, fk_tgt_en) = q.dst.fks[fk_name]
        for j in carrier(alg, fk_src_en)
            j_fk = eval_fk(alg, fk_name, j)
            for (tgt_var, src_term) in var_mapping
                g = gen_lookup[(tgt_var, j_fk, fk_tgt_en)]
                lhs = haskey(sks, g) ? CQLSk(g) : CQLGen(g)
                rhs = _coeval_subst(src_term, j, fk_src_en)
                push!(eqs, Equation(lhs, rhs))
            end
        end
    end

    # 3. Attribute equations: eval_att(J, att, j) = subst(Q.atts[att])
    # Import Skolems from J's presentation (merge with type-sorted variable skolems)
    for (sk, ty) in inst.pres.sks
        sks[sk] = ty
    end

    for (att_name, att_term) in q.atts
        (att_src_en, att_tgt_ty) = q.dst.atts[att_name]
        for j in carrier(alg, att_src_en)
            lhs = eval_att(alg, att_name, j)
            rhs = _coeval_subst(att_term, j, att_src_en)
            push!(eqs, Equation(lhs, rhs))
            # Collect any Skolems from LHS that aren't in sks yet
            _collect_coeval_sks!(sks, lhs, att_tgt_ty)
        end
    end

    # 4. Import J's type algebra equations (Skolem normalization)
    # Java: J.algebra().talg().allEqs() — these are pure type-level equations
    # between Skolems, not instance-level equations with generators
    for eq in inst.pres.eqs
        # Only import equations that are purely type-level (no entity generators)
        if _is_type_level_eq(eq, inst.pres.gens)
            push!(eqs, eq)
        end
    end

    pres = Presentation(gens, sks, eqs, gen_order)
    col = presentation_to_collage(q.src, pres)
    prover, canonical = create_prover_with_canonical(col, opts)
    dp_fn = eq -> prover(Ctx(), eq)
    initial_instance(pres, dp_fn, q.src; canonical_fn=canonical)
end

"""Collect CQLSk symbols from a type-side term and add to sks dict."""
function _collect_coeval_sks!(sks::Dict{Symbol,Symbol}, t::CQLTerm, default_ty::Symbol)
    if t isa CQLSk
        if !haskey(sks, t.sk)
            sks[t.sk] = default_ty
        end
    elseif t isa CQLSym
        for a in t.args
            _collect_coeval_sks!(sks, a, default_ty)
        end
    end
end

"""Check if an equation is purely type-level (no entity generators, only Skolems/Syms/constants)."""
function _is_type_level_eq(eq::Equation, gens::Dict{Symbol,Symbol})::Bool
    _is_type_level_term(eq.lhs, gens) && _is_type_level_term(eq.rhs, gens)
end
function _is_type_level_term(t::CQLTerm, gens::Dict{Symbol,Symbol})::Bool
    if t isa CQLSk; return true
    elseif t isa CQLSym; return all(a -> _is_type_level_term(a, gens), t.args)
    elseif t isa CQLGen; return !haskey(gens, t.gen)  # J's gens are entity-level
    elseif t isa CQLAtt; return false  # attribute application involves entity terms
    elseif t isa CQLFk; return false
    elseif t isa CQLVar; return false
    else; return true
    end
end

"""
Evaluate coeval on a transform: given Q: S → T and transform h: J → K
(both on T = Q.dst), produce a transform coeval(Q,J) → coeval(Q,K) on S = Q.src.

For each coeval generator (v, j, en) in coeval(Q,J), map it to the generator
(v, h(j), en) in coeval(Q,K), where h(j) is the image of j under transform h.
"""
function eval_coeval_transform(q::CQLQuery, tr::CQLTransform, opts::CQLOptions)
    src_coeval = eval_coeval_instance(q, tr.src, opts)
    dst_coeval = eval_coeval_instance(q, tr.dst, opts)

    src_alg = tr.src.algebra
    dst_alg = tr.dst.algebra

    # Build generator lookup for destination coeval
    dst_gen_lookup = Dict{Tuple{Symbol, Any, Symbol}, Symbol}()
    dst_counter = Ref(0)
    for (dst_en, (ctx, _)) in q.ens
        for j in carrier(dst_alg, dst_en)
            for (v, _) in ctx
                dst_counter[] += 1
                dst_gen_lookup[(v, j, dst_en)] = Symbol("ce", dst_counter[])
            end
        end
    end

    # Build generator mapping: for each src coeval gen, find corresponding dst coeval gen
    gens = Dict{Symbol, CQLTerm}()
    src_counter = Ref(0)
    for (dst_en, (ctx, _)) in q.ens
        for j in carrier(src_alg, dst_en)
            for (v, _) in ctx
                src_counter[] += 1
                src_gen = Symbol("ce", src_counter[])

                # Map j through the transform to get j' in K
                j_term = repr_x(src_alg, j)
                j_mapped_term = _apply_transform_subst(tr, j_term)
                j_prime = _eval_gen_term_in_algebra(dst_alg, j_mapped_term)

                if j_prime !== nothing
                    dst_gen = get(dst_gen_lookup, (v, j_prime, dst_en), nothing)
                    if dst_gen !== nothing
                        gens[src_gen] = CQLGen(dst_gen)
                    else
                        gens[src_gen] = CQLGen(src_gen)  # fallback
                    end
                else
                    gens[src_gen] = CQLGen(src_gen)  # fallback
                end
            end
        end
    end

    sks = Dict{Symbol, CQLTerm}(s => CQLSk(s) for s in keys(src_coeval.pres.sks))
    CQLTransform(src_coeval, dst_coeval, gens, sks)
end

"""
Evaluate counit_query transform: given Q: S → T and instance I on S,
produce transform eval(Q, coeval(Q, eval(Q, I))) → eval(Q, I).

This is the counit of the eval ⊣ coeval adjunction, evaluated at I.
The actual counit is: eval(Q, coeval(Q, J)) → J for J on T.
So we compute J = eval(Q, I), then build the counit at J.
"""
function eval_counit_query_transform(q::CQLQuery, inst::CQLInstance, opts::CQLOptions)
    # Compute J = eval(Q, I)
    j_inst = eval_query_instance(q, inst, opts)

    # Compute coeval(Q, J)
    coeval_inst = eval_coeval_instance(q, j_inst, opts)

    # Compute eval(Q, coeval(Q, J)) — reuse query data to avoid recomputation
    ec_data = _eval_query_data(q, coeval_inst)
    evalcoeval_inst = _instance_from_query_pres(q, ec_data[4], opts)

    # Build the counit transform: evalcoeval_inst → j_inst
    # Both are on Q.dst (= T)
    _build_counit_transform(q, j_inst, coeval_inst, evalcoeval_inst, opts; ec_query_data=ec_data)
end

"""Build the counit transform eval(Q, coeval(Q, J)) → J."""
function _build_counit_transform(q::CQLQuery, j_inst::CQLInstance,
                                  coeval_inst::CQLInstance,
                                  evalcoeval_inst::CQLInstance,
                                  opts::CQLOptions;
                                  ec_query_data=nothing)
    # The counit maps each element of eval(Q, coeval(Q, J)) to an element of J.
    # eval(Q, coeval(Q, J)) is built by enumerating tuples from coeval(Q, J)'s algebra.
    # Each tuple in eval assigns from-variables to coeval elements.
    # The coeval elements represent (variable, j_element, entity) triples.

    # Reuse pre-computed query data if available, otherwise compute
    (ec_tuples, ec_t2g, ec_g2t, _) = ec_query_data !== nothing ? ec_query_data : _eval_query_data(q, coeval_inst)
    # Enumerate tuples for j_inst from the original evaluation
    (j_tuples, j_t2g, j_g2t, _) = _eval_query_data(q, j_inst.schema == q.src ? j_inst :
        # J is on Q.dst, so eval(Q, ...) doesn't apply. Use direct algebra.
        j_inst)

    # For each generator in evalcoeval, find the corresponding generator in j_inst
    gens = Dict{Symbol, CQLTerm}()
    for (g, _) in evalcoeval_inst.pres.gens
        gens[g] = CQLGen(g)  # default: identity
    end

    # Try to map using algebra structure
    ec_alg = evalcoeval_inst.algebra
    j_alg = j_inst.algebra

    for (g, en) in evalcoeval_inst.pres.gens
        # Each gen in evalcoeval corresponds to a tuple from coeval's algebra.
        # The coeval's generators encode (var, j_elem, entity) triples.
        # After eval, each result element corresponds to an assignment of
        # coeval elements satisfying the query.
        # The counit should map this back to the original j_elem.

        # Use repr_x to get the term for g, then evaluate it through the counit mapping
        if haskey(ec_g2t, g)
            (tgt_en, ec_assignment) = ec_g2t[g]
            # The ec_assignment maps from-variables to coeval algebra elements.
            # Each coeval element represents a (var, j_elem, entity) triple.
            # We need to determine which j_elem each coeval element corresponds to.
            # Since the coeval was built from j_inst, the generator naming encodes this.

            # Find the matching j_inst tuple: look for matching element in j_inst
            j_en_tuples = get(j_tuples, tgt_en, Dict{Symbol,Any}[])
            if length(j_en_tuples) == length(get(ec_tuples, tgt_en, Dict{Symbol,Any}[]))
                # Same number of tuples — use positional mapping
                ec_en_tuples = ec_tuples[tgt_en]
                for (i, tup) in enumerate(ec_en_tuples)
                    ec_gen = ec_t2g[(tgt_en, i)]
                    if ec_gen == g && i <= length(j_en_tuples)
                        j_gen = j_t2g[(tgt_en, i)]
                        gens[g] = CQLGen(j_gen)
                        break
                    end
                end
            end
        end
    end

    sks = Dict{Symbol, CQLTerm}(s => CQLSk(s) for s in keys(evalcoeval_inst.pres.sks))
    CQLTransform(evalcoeval_inst, j_inst, gens, sks)
end

"""
Evaluate unit_query transform: given Q: S → T and instance J on T (= Q.dst),
produce transform J → coeval(Q, eval(Q, J)).

This is the unit of the eval ⊣ coeval adjunction, evaluated at J.
"""
function eval_unit_query_transform(q::CQLQuery, inst::CQLInstance, opts::CQLOptions)
    # inst = J on Q.dst (= T)
    # Compute eval(Q, J) — but Q goes S → T, and eval expects inst on S
    # Actually, unit_query Q J: J → coeval(Q, eval(Q, J))
    # But eval(Q, -) expects input on Q.src. This is wrong.
    # Hmm — for unit_query, we need Q to be able to evaluate on J.
    # Looking at the Java code: unit_query computes coeval(Q, eval(Q, J))
    # where J is on Q.dst.
    # But eval(Q, J) requires J on Q.src...
    #
    # Actually, the unit of the adjunction eval ⊣ coeval at J on Q.dst is:
    # J → coeval(Q, eval(Q, J))
    # But eval(Q, -) : Inst(Q.src) → Inst(Q.dst), so eval(Q, J) doesn't typecheck
    # if J is on Q.dst.
    #
    # The resolution: for the adjunction, the unit at J (on Q.dst) is:
    # η_J : J → coeval(Q, eval(Q, J)) where we interpret J on Q.src... no.
    #
    # Actually re-reading: unit_query Q J where J is on Q.dst.
    # The counit is: eval(Q, coeval(Q, J)) → J  (J on Q.dst)
    # The unit is: I → coeval(Q, eval(Q, I))  (I on Q.src)
    #
    # So for unit_query, inst should be on Q.src!
    # Pushout.cql: `transform t = unit_query pushout J` where J is on Span.
    # pushout query goes Square → Span. Q.src = Square, Q.dst = Span.
    # J is on Span = Q.dst. So J is on Q.dst, not Q.src.
    #
    # Hmm, but the unit should be for instances on Q.src...
    # Unless the adjunction is reversed: coeval ⊣ eval?
    # In that case: unit at J on Q.dst: J → eval(Q, coeval(Q, J))
    # And counit at I on Q.src: coeval(Q, eval(Q, I)) → I
    #
    # For Pushout: J on Span = Q.dst.
    # unit: J → eval(Q, coeval(Q, J)) — both on Q.dst ✓

    # Compute coeval(Q, J)
    coeval_inst = eval_coeval_instance(q, inst, opts)
    # Compute eval(Q, coeval(Q, J))
    eval_coeval_inst = eval_query_instance(q, coeval_inst, opts)

    # Build the unit transform: inst → eval_coeval_inst
    # Both are on Q.dst
    _build_unit_transform(q, inst, coeval_inst, eval_coeval_inst, opts)
end

"""Build the unit transform J → eval(Q, coeval(Q, J))."""
function _build_unit_transform(q::CQLQuery, j_inst::CQLInstance,
                                coeval_inst::CQLInstance,
                                evalcoeval_inst::CQLInstance,
                                opts::CQLOptions)
    j_alg = j_inst.algebra
    coeval_alg = coeval_inst.algebra
    ec_alg = evalcoeval_inst.algebra

    # Enumerate tuples for eval(Q, coeval(Q, J))
    (ec_tuples, ec_t2g, ec_g2t, _) = _eval_query_data(q, coeval_inst)

    # For each generator in j_inst, find corresponding generator in evalcoeval_inst
    gens = Dict{Symbol, CQLTerm}()

    for (g, en) in j_inst.pres.gens
        # g is a generator of J of entity en (in Q.dst)
        # We need to find which eval(Q, coeval(Q, J)) element it maps to.
        # In eval(Q, coeval(Q, J)), tuples enumerate assignments from coeval's algebra.
        # The coeval generators encode (var, j_elem, entity).
        # For j_elem = eval_gen(j_alg, g), we can look for the coeval generators
        # that correspond to this element and find the matching tuple.

        j_elem = eval_gen(j_alg, g)

        # For each Q.dst entity en that matches, look at coeval generators
        # corresponding to element j_elem in entity en.
        # In eval(Q, coeval(Q, J)), the tuples for entity en enumerate
        # assignments from coeval's algebra that satisfy the where-clause.

        # Try to find a matching tuple
        found = false
        if haskey(ec_tuples, en)
            tuples = ec_tuples[en]
            (ctx, _) = q.ens[en]

            for (i, tup) in enumerate(tuples)
                # Check if this tuple corresponds to j_elem
                # Each tup[v] is a coeval algebra element
                # The coeval generator for (v, j_elem, en) should be in the coeval algebra
                match = true
                for (v, _) in ctx
                    coeval_gen_name = nothing
                    # Find the coeval generator for (v, j_elem, en)
                    # Coeval generators are named ce1, ce2, etc. in order of creation.
                    # We need to check if tup[v] corresponds to j_elem.

                    # The coeval generator for (v, j_elem, en) in the coeval's algebra
                    # was created during eval_coeval_instance. Its repr_x should encode
                    # the correspondence.
                    coeval_repr = repr_x(coeval_alg, tup[v])
                    # The coeval is built with initial_instance, so repr_x gives a CQLTerm
                    # that's a canonical path from a generator. We need to check if this
                    # corresponds to the generator for (v, j_elem, en).
                    # This is tricky in general. For simple cases, use position matching.
                end

                # Use position matching: element i in j_inst corresponds to tuple i in ec
                ec_gen = ec_t2g[(en, i)]
                gens[g] = CQLGen(ec_gen)
                found = true
                break
            end
        end

        if !found
            gens[g] = CQLGen(g)  # fallback
        end
    end

    sks = Dict{Symbol, CQLTerm}(s => CQLSk(s) for s in keys(j_inst.pres.sks))
    CQLTransform(j_inst, evalcoeval_inst, gens, sks)
end

# ============================================================================
# Front/Back schema and query
# ============================================================================

"""Build the front (or back) schema for constraint ED at index i (0-based).

The front schema has a single entity 'Front' with attributes derived from
the universal variables (and, for back, existential variables) of the ED."""
function _eval_schema_front(c::CQLConstraints, idx::Int, is_back::Bool)::CQLSchema
    # CQL syntax uses 0-based indexing for EDs
    julia_idx = idx + 1
    (1 <= julia_idx <= length(c.egds)) || throw(CQLException("ED index $idx out of range (have $(length(c.egds)) EDs)"))
    ed = c.egds[julia_idx]
    sch = c.schema
    ts = sch.typeside

    ens = Set{Symbol}([:Front])
    fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    atts = Dict{Symbol, Tuple{Symbol, Symbol}}()

    # Front schema always has only universal variable attributes
    # (back query uses same front schema — existential vars are in FROM only)
    for (v, en) in ed.vars
        en in sch.ens || continue  # skip type-sorted vars
        for (att, ty) in schema_atts_from(sch, en)
            att_name = Symbol(string(v), "_", string(att))
            atts[att_name] = (:Front, ty)
        end
    end

    eq_fn = (en, eq) -> eq.lhs == eq.rhs
    CQLSchema(ts, ens, fks, atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(), eq_fn)
end

"""Build the front or back query for constraint ED at index i (0-based).

The query maps from the constraints schema to the front/back schema.
For front: uses only universal variables.
For back: uses both universal and existential variables, plus conclusion equations."""
function _eval_query_front_back(c::CQLConstraints, idx::Int, is_back::Bool)::CQLQuery
    julia_idx = idx + 1
    (1 <= julia_idx <= length(c.egds)) || throw(CQLException("ED index $idx out of range"))
    ed = c.egds[julia_idx]
    src_schema = c.schema
    front_schema = _eval_schema_front(c, idx, is_back)

    # Build from-clause: one generator per universal variable (entity-sorted)
    from_ctx = Dict{Symbol, Symbol}()
    for (v, en) in ed.vars
        en in src_schema.ens || continue
        from_ctx[v] = en
    end

    # Build attribute mapping
    att_mapping = Dict{Symbol, CQLTerm}()
    for (v, en) in ed.vars
        en in src_schema.ens || continue
        for (att, _) in schema_atts_from(src_schema, en)
            att_name = Symbol(string(v), "_", string(att))
            att_mapping[att_name] = CQLAtt(att, CQLVar(v))
        end
    end

    # Build where-clause from ED premises
    where_eqs = Set{Equation}(ed.premises)

    if is_back
        # Add existential variables to from-clause (but not to att_mapping)
        for (v, en) in ed.exists_vars
            en in src_schema.ens || continue
            from_ctx[v] = en
        end
        # Add conclusion equations as where-clauses for back
        for eq in ed.conclusions
            push!(where_eqs, eq)
        end
    end

    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}(
        :Front => (from_ctx, where_eqs)
    )
    fks = Dict{Symbol, Dict{Symbol, CQLTerm}}()

    CQLQuery(src_schema, front_schema, ens, fks, att_mapping)
end

"""Evaluate a fromConstraints query: `fromConstraints n c` extracts the nth ED
from constraints c and builds a query from c.schema to the ED schema.

The ED schema has two entities (front, back) connected by FK unit: back → front.
- Entity front: universal variables with premises (the "pattern")
- Entity back: all variables with all equations (the "extended pattern")
- FK unit: identity on universal variables (projects back to front)
"""
function _eval_query_from_constraints(c::CQLConstraints, idx::Int, opts::CQLOptions)::CQLQuery
    julia_idx = idx + 1  # CQL uses 0-based indexing
    (1 <= julia_idx <= length(c.egds)) || throw(CQLException(
        "ED index $idx out of range (have $(length(c.egds)) EDs)"))
    ed = c.egds[julia_idx]
    src_schema = c.schema
    ts = src_schema.typeside

    # Build the ED schema: entities front/back, FK unit: back → front, no attributes
    ed_ens = Set{Symbol}([:front, :back])
    ed_fks = Dict{Symbol, Tuple{Symbol, Symbol}}(:unit => (:back, :front))
    ed_atts = Dict{Symbol, Tuple{Symbol, Symbol}}()
    eq_fn = (en, eq) -> eq.lhs == eq.rhs
    ed_schema = CQLSchema(ts, ed_ens, ed_fks, ed_atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(), eq_fn)

    # Build from-clause for front: universal variables only
    front_ctx = Dict{Symbol, Symbol}()
    for (v, en) in ed.vars
        front_ctx[v] = en
    end

    # Build from-clause for back: all variables (universal + existential)
    back_ctx = Dict{Symbol, Symbol}()
    for (v, en) in ed.vars
        back_ctx[v] = en
    end
    for (v, en) in ed.exists_vars
        back_ctx[v] = en
    end

    # Build where-clauses
    front_where = Set{Equation}(ed.premises)
    back_where = union(Set{Equation}(ed.premises), Set{Equation}(ed.conclusions))

    # FK mapping for unit: back → front
    # Maps each front from-variable to the same variable in back's context
    unit_map = Dict{Symbol, CQLTerm}()
    for (v, _) in ed.vars
        unit_map[v] = CQLVar(v)
    end

    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}(
        :front => (front_ctx, front_where),
        :back => (back_ctx, back_where),
    )
    query_fks = Dict{Symbol, Dict{Symbol, CQLTerm}}(
        :unit => unit_map,
    )
    query_atts = Dict{Symbol, CQLTerm}()

    CQLQuery(src_schema, ed_schema, ens, query_fks, query_atts)
end

# ============================================================================
# DeltaCoEval query: toCoQuery F for a mapping F: S→T produces query S→T
# ============================================================================

"""Build the deltaCoEval query for a mapping F: S→T.

Produces a query Q: S→T such that eval(Q, I) ≅ coeval(delta(F), I).

Algorithm:
For each entity en2 in T:
  - Build a seed instance on T with one generator v:en2
  - Apply delta(F) to get a delta instance on S
  - The delta instance's carriers become from-variables
  - The delta instance's equations become the where-clause
For each FK fk2: src_en→tgt_en in T:
  - Map tgt block variables to src block variables via the FK transform
For each attribute att2: en2→ty in T:
  - Evaluate att2(v) in the seed and express using S-schema attributes
"""
function _delta_coeval_query(F::CQLMapping, opts::CQLOptions)::CQLQuery
    if _is_identity_mapping(F)
        return identity_query(F.src)
    end

    S = F.src
    T = F.dst

    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}()
    fks_map = Dict{Symbol, Dict{Symbol, CQLTerm}}()
    atts_map = Dict{Symbol, CQLTerm}()

    # Per-entity seed and delta instances
    seeds = Dict{Symbol, Any}()
    deltas = Dict{Symbol, Any}()
    e2q_maps = Dict{Symbol, Dict}()  # en2 → Dict(delta_elem → qvar_name)

    gen_id = Ref(0)

    for en2 in T.ens
        # Build seed instance on T with one generator v:en2
        seed_pres = Presentation(Dict(:v => en2), Dict{Symbol,Symbol}(), Set{Equation}())
        col = presentation_to_collage(T, seed_pres)
        prover = create_prover(col, opts)
        dp_fn = eq -> prover(Ctx(), eq)
        seed = initial_instance(seed_pres, dp_fn, T)
        seeds[en2] = seed

        # Delta(F) on the seed gives instance on S
        delta = eval_delta_instance(F, seed, opts)
        deltas[en2] = delta

        # From-variables from delta's entity carriers
        from_ctx = Dict{Symbol,Symbol}()
        e2q = Dict()

        for en1 in S.ens
            for elem in carrier(delta.algebra, en1)
                gen_id[] += 1
                qvar = Symbol("v", gen_id[])
                from_ctx[qvar] = en1
                e2q[elem] = qvar
            end
        end

        # Where-clause from delta presentation equations
        where_eqs = Set{Equation}()
        for eq in delta.pres.eqs
            lhs = _dcq_term(eq.lhs, delta.algebra, e2q)
            rhs = _dcq_term(eq.rhs, delta.algebra, e2q)
            push!(where_eqs, Equation(lhs, rhs))
        end

        ens[en2] = (from_ctx, where_eqs)
        e2q_maps[en2] = e2q
    end

    # FK mappings: for each FK fk2: src_en→tgt_en in T
    for (fk2, (src_en, tgt_en)) in T.fks
        new_fk_map = Dict{Symbol, CQLTerm}()
        seed_src = seeds[src_en]
        seed_tgt = seeds[tgt_en]
        delta_tgt = deltas[tgt_en]

        tgt_e2q = e2q_maps[tgt_en]
        src_e2q = e2q_maps[src_en]

        # For each element in delta(tgt_en), apply the FK transform
        for en1 in S.ens
            for elem in carrier(delta_tgt.algebra, en1)
                qvar_tgt = tgt_e2q[elem]
                (_, x) = elem  # x is carrier element of F(en1) in seed_tgt

                # Transform: substitute Gen(:v) → Fk(fk2, Gen(:v)) in x, then eval in seed_src
                x_subst = _dcq_subst_gen(x, :v, CQLFk(fk2, CQLGen(:v)))
                x_in_src = _dcq_eval_entity(seed_src.algebra, x_subst)

                delta_elem_src = (en1, x_in_src)
                new_fk_map[qvar_tgt] = CQLVar(src_e2q[delta_elem_src])
            end
        end

        fks_map[fk2] = new_fk_map
    end

    # Attribute mappings: for each attribute att2: en2→ty in T
    for (att2, (att_en, att_ty)) in T.atts
        e2q = e2q_maps[att_en]
        seed = seeds[att_en]
        delta = deltas[att_en]

        v_elem = seed.algebra.gen[:v]
        # The seed's nf_y for att2(v)
        seed_att_nf = seed.algebra.nf_y(Right((v_elem, att2)))

        # Search delta elements for an S-attribute that evaluates to the same type element
        found = false
        for en1 in S.ens
            for elem in carrier(delta.algebra, en1)
                for (att_S, (att_S_src, _)) in S.atts
                    att_S_src == en1 || continue
                    delta_att_nf = delta.algebra.nf_y(Right((elem, att_S)))
                    if delta_att_nf == seed_att_nf
                        atts_map[att2] = CQLAtt(att_S, CQLVar(e2q[elem]))
                        found = true
                        break
                    end
                end
                found && break
            end
            found && break
        end

        if !found
            # Fallback: try to build a compound term using typeside functions
            # Search for combinations of S-attribute terms and typeside functions
            atts_map[att2] = _dcq_find_compound_att(att2, seed_att_nf, seed, delta, S, e2q)
        end
    end

    CQLQuery(S, T, ens, fks_map, atts_map)
end

"""Convert a delta presentation term (CQLGen-based) to a query term (CQLVar-based)."""
function _dcq_term(t::CQLTerm, delta_alg, e2q)::CQLTerm
    if t isa CQLGen
        elem = delta_alg.gen[t.gen]
        CQLVar(e2q[elem])
    elseif t isa CQLFk
        CQLFk(t.fk, _dcq_term(t.arg, delta_alg, e2q))
    elseif t isa CQLAtt
        CQLAtt(t.att, _dcq_term(t.arg, delta_alg, e2q))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_dcq_term(a, delta_alg, e2q) for a in t.args])
    else
        t
    end
end

"""Substitute CQLGen(name) with replacement in an entity-level term."""
function _dcq_subst_gen(t::CQLTerm, name::Symbol, replacement::CQLTerm)::CQLTerm
    if t isa CQLGen && t.gen == name
        replacement
    elseif t isa CQLFk
        CQLFk(t.fk, _dcq_subst_gen(t.arg, name, replacement))
    else
        t
    end
end

"""Evaluate an entity-level CQLTerm (CQLGen, CQLFk) in an algebra to get a carrier element."""
function _dcq_eval_entity(alg, t::CQLTerm)
    if t isa CQLGen
        alg.gen[t.gen]
    elseif t isa CQLFk
        inner = _dcq_eval_entity(alg, t.arg)
        eval_fk(alg, t.fk, inner)
    else
        error("Cannot evaluate entity term in algebra: $t")
    end
end

"""Search for a compound type term built from S-attributes and typeside functions
that matches the target nf_y value."""
function _dcq_find_compound_att(att2, target_nf, seed, delta, S, e2q)::CQLTerm
    # Build a catalog of available base terms (S-attributes of delta elements)
    base_terms = Dict{CQLTerm, CQLTerm}()  # nf_value → query_term
    for en1 in S.ens
        for elem in carrier(delta.algebra, en1)
            for (att_S, (att_S_src, _)) in S.atts
                att_S_src == en1 || continue
                nf = delta.algebra.nf_y(Right((elem, att_S)))
                qterm = CQLAtt(att_S, CQLVar(e2q[elem]))
                base_terms[nf] = qterm
            end
        end
    end

    # Check if target is directly a base term
    if haskey(base_terms, target_nf)
        return base_terms[target_nf]
    end

    # Try applying typeside functions to base terms
    for (sym, (arg_tys, ret_ty)) in S.typeside.syms
        if length(arg_tys) == 1
            for (nf, qterm) in base_terms
                composed_nf = CQLSym(sym, CQLTerm[nf])
                if composed_nf == target_nf
                    return CQLSym(sym, CQLTerm[qterm])
                end
            end
        elseif length(arg_tys) == 2
            for (nf1, qt1) in base_terms
                for (nf2, qt2) in base_terms
                    composed_nf = CQLSym(sym, CQLTerm[nf1, nf2])
                    if composed_nf == target_nf
                        return CQLSym(sym, CQLTerm[qt1, qt2])
                    end
                end
            end
        end
    end

    # Last resort: create a Skolem-like placeholder
    throw(CQLException("Cannot find query term for T-attribute $att2 in deltaCoEval"))
end

# ============================================================================
# Pi instance/transform (identity mapping optimization)
# ============================================================================

"""Check if a mapping is an identity mapping."""
function _is_identity_mapping(m::CQLMapping)::Bool
    m.src == m.dst || return false
    for (en, mapped) in m.ens
        en == mapped || return false
    end
    for (fk, term) in m.fks
        term == CQLFk(fk, CQLVar(:_unit)) || return false
    end
    for (att, term) in m.atts
        term == CQLAtt(att, CQLVar(:_unit)) || return false
    end
    true
end

"""Evaluate pi instance: right adjoint to delta along a mapping.

For identity mappings, pi(id, I) = I."""
function _eval_pi_instance(m::CQLMapping, inst::CQLInstance, opts::CQLOptions)::CQLInstance
    if _is_identity_mapping(m)
        return inst
    end
    throw(CQLException("pi instances for non-identity mappings are not yet supported"))
end

"""Evaluate pi transform: right adjoint to delta along a mapping on transforms.

For identity mappings, pi(id, T) = T."""
function _eval_pi_transform(m::CQLMapping, t::CQLTransform, opts::CQLOptions)::CQLTransform
    if _is_identity_mapping(m)
        return t
    end
    throw(CQLException("pi transforms for non-identity mappings are not yet supported"))
end

# ============================================================================
# Frozen instance/transform
# ============================================================================

"""Evaluate a frozen instance: extract the from-clause of a query entity block
and turn it into an instance on the query's source schema."""
function _eval_frozen_instance(q::CQLQuery, entity_name::Symbol, opts::CQLOptions)::CQLInstance
    haskey(q.ens, entity_name) || throw(CQLException("Query has no entity block for: $entity_name"))
    (ctx, where_eqs) = q.ens[entity_name]

    # Create presentation on q.src with:
    # - One generator per from-variable, typed by the source entity
    gens = Dict{Symbol, Symbol}()
    sks = Dict{Symbol, Symbol}()
    for (v, en) in ctx
        if en in q.src.ens
            gens[v] = en
        else
            # Type-sorted variable: create a skolem constant
            sks[v] = en
        end
    end

    # Where-clause equations become instance equations (replace CQLVar → CQLGen/CQLSk)
    eqs = Set{Equation}()
    for eq in where_eqs
        lhs = _vars_to_gens_sks(eq.lhs, gens, sks)
        rhs = _vars_to_gens_sks(eq.rhs, gens, sks)
        push!(eqs, Equation(lhs, rhs))
    end

    pres = Presentation(gens, sks, eqs)

    if isempty(gens) && isempty(sks)
        return empty_instance(q.src)
    end

    # Build collage and include universally-quantified schema path equations
    # so KB completion can derive equalities for generated terms (e.g.,
    # manager(manager(secretary(worksIn(e)))) = manager(secretary(worksIn(e)))).
    col = presentation_to_collage(q.src, pres)
    # Add universally-quantified schema equations for KB completion
    sch_col = schema_to_collage(q.src)
    for (ctx, eq) in sch_col.ceqs
        if !isempty(ctx)
            push!(col.ceqs, (ctx, eq))
        end
    end

    prover = create_prover(col, opts)
    dp_fn = eq -> prover(Ctx(), eq)
    initial_instance(pres, dp_fn, q.src; timeout_seconds=10, max_carrier_size=200)
end

"""Build a layered prover: orthogonal rewriting for ground equations,
typeside prover for type-level equality."""
function _build_layered_prover(col::Collage, ts::Typeside, opts::CQLOptions)
    (col_simplified, replacements) = simplify_collage(col)

    # Extract ground equations (these come from schema/instance, not typeside)
    ground_eqs = Equation[eq for (ctx, eq) in col_simplified.ceqs if isempty(ctx)]

    # Try to orient ground equations as rewrite rules
    rules = RewriteRule[]
    for eq in ground_eqs
        oriented = _orient_eq(eq)
        if oriented !== nothing
            push!(rules, RewriteRule(oriented.lhs, oriented.rhs))
        else
            # Can't orient — try both directions
            if term_size(eq.lhs) >= term_size(eq.rhs)
                push!(rules, RewriteRule(eq.lhs, eq.rhs))
            else
                push!(rules, RewriteRule(eq.rhs, eq.lhs))
            end
        end
    end

    # The prover: normalize with ground rules, then check via typeside prover
    eq -> begin
        l = replace_repeatedly(replacements, eq.lhs)
        r = replace_repeatedly(replacements, eq.rhs)
        ln = normalize(rules, l)
        rn = normalize(rules, r)
        ln == rn && return true
        # Fall back to typeside prover for type-level equality
        ts.eq(Dict{Symbol,Symbol}(), Equation(ln, rn))
    end
end

"""Add ground path equations for FK-reachable entities that have no direct generators.

When a frozen instance has a generator x:E but no generators of entity F,
and F is reachable from E via FK chain, path equations on F aren't grounded
by `presentation_to_collage`. This function computes FK-reachable terms
and adds ground path equations for them."""
function _add_fk_reachable_path_eqs!(col::Collage, sch::CQLSchema, gens::Dict{Symbol,Symbol})
    gen_entities = Set{Symbol}(en for (_, en) in gens)

    # Find schema path/observation equations on entities without generators
    sch_col = schema_to_collage(sch)
    path_eqs = Tuple{Symbol, Symbol, Equation}[]
    for (ctx, eq) in sch_col.ceqs
        isempty(ctx) && continue
        entity_vars = [(v, get_right(sort)) for (v, sort) in ctx if is_right(sort)]
        length(entity_vars) == 1 || continue
        (var, entity) = entity_vars[1]
        entity in gen_entities && continue
        push!(path_eqs, (var, entity, eq))
    end

    isempty(path_eqs) && return

    path_eq_entities = Set{Symbol}(entity for (_, entity, _) in path_eqs)

    # BFS from generator entities through FKs to find representative terms
    repr_terms = Dict{Symbol, Vector{CQLTerm}}()
    for (g, en) in gens
        push!(get!(repr_terms, en, CQLTerm[]), CQLGen(g))
    end

    for _ in 1:5
        new_found = false
        for (fk, (fk_src, fk_tgt)) in sch.fks
            fk_src == fk_tgt && continue
            haskey(repr_terms, fk_src) || continue
            fk_tgt in gen_entities && continue
            tgt_terms = get!(repr_terms, fk_tgt, CQLTerm[])
            for src_term in repr_terms[fk_src]
                fk_term = CQLFk(fk, src_term)
                if !(fk_term in tgt_terms)
                    push!(tgt_terms, fk_term)
                    new_found = true
                end
            end
        end
        new_found || break
    end

    # Ground path equations with FK-reachable terms
    for (var, entity, eq) in path_eqs
        haskey(repr_terms, entity) || continue
        for term in repr_terms[entity]
            subst = Dict{Symbol, CQLTerm}(var => term)
            lhs = _subst_vars(eq.lhs, subst)
            rhs = _subst_vars(eq.rhs, subst)
            push!(col.ceqs, (Ctx(), Equation(lhs, rhs)))
        end
    end
end

"""Replace CQLVar with CQLGen or CQLSk depending on sort."""
function _vars_to_gens_sks(t::CQLTerm, gens::Dict{Symbol,Symbol}, sks::Dict{Symbol,Symbol})::CQLTerm
    if t isa CQLVar
        if haskey(gens, t.name)
            return CQLGen(t.name)
        elseif haskey(sks, t.name)
            return CQLSk(t.name)
        else
            return t  # leave as variable (shouldn't happen in well-typed queries)
        end
    elseif t isa CQLFk
        return CQLFk(t.fk, _vars_to_gens_sks(t.arg, gens, sks))
    elseif t isa CQLAtt
        return CQLAtt(t.att, _vars_to_gens_sks(t.arg, gens, sks))
    elseif t isa CQLSym
        return CQLSym(t.sym, CQLTerm[_vars_to_gens_sks(a, gens, sks) for a in t.args])
    else
        return t
    end
end

"""Evaluate a frozen transform: given query Q: S→T, lambda var:entity. body : ret_type,
produce a transform from frozen(Q, entity) to some target instance on a type.

This implements the Java TransExpFrozen which creates a transform by evaluating
the lambda body through the query composition."""
function _eval_frozen_transform(q::CQLQuery, lambda_var::String, lambda_type::String,
                                 lambda_body, ret_type::String, opts::CQLOptions)::CQLTransform
    entity_name = Symbol(lambda_type)
    haskey(q.ens, entity_name) || throw(CQLException("Query has no entity block for: $entity_name"))

    # Build the frozen instance (source of the transform)
    frozen_inst = _eval_frozen_instance(q, entity_name, opts)

    # The lambda body is a RawTerm that represents a path in the dst schema context.
    # We need to trace this through the query to get a term in the src schema.
    # The lambda variable refers to the entity in the dst schema (q.dst).

    # Parse the lambda body in the dst schema context
    dst_term = _parse_frozen_lambda_body(q, lambda_var, entity_name, lambda_body)

    # Compose the dst term through the query to get a src term
    src_term = _compose_term_through_query(q, entity_name, dst_term)

    # Replace CQLVar with CQLGen for frozen instance generators
    (ctx, _) = q.ens[entity_name]
    gens_map = Dict{Symbol, Symbol}()
    sks_map = Dict{Symbol, Symbol}()
    for (v, en) in ctx
        if en in q.src.ens
            gens_map[v] = en
        else
            sks_map[v] = en
        end
    end
    ground_term = _vars_to_gens_sks(src_term, gens_map, sks_map)

    # Build single-entity target schema (just the return type)
    ret_ty = Symbol(ret_type)

    # The target instance is the type algebra portion relevant to frozen_inst
    # For a transform to a type, we create an instance on a trivial schema
    # that holds just the type value
    tgt_sch = frozen_inst.schema  # Same schema — the transform maps generators to type-side terms
    tgt_inst = frozen_inst  # The transform is from frozen_inst to itself (identity on instances)

    # Build the transform: each generator maps to the ground_term applied to that generator
    # But actually, for a frozen transform, the result is a transform from frozen instance
    # to frozen instance, where generators map to themselves and skolems map to the composed term.
    # More precisely: it maps each generator to itself, but provides the type-side mapping.

    # In the Java code, a frozen transform T: frozen(Q,e) → frozen(Q,e) maps
    # generators to generators and computes the type algebra value from the lambda.
    # Actually, for `frozen qTS lambda x:s0. x.ss.att : Double`, the result
    # is a transform that maps the single source generator to a type-side term.

    # The transform is from frozen_inst to frozen_inst itself (identity-like on entity side)
    trans_gens = Dict{Symbol, CQLTerm}(g => CQLGen(g) for g in keys(frozen_inst.pres.gens))
    trans_sks = Dict{Symbol, CQLTerm}()
    for (s, _) in frozen_inst.pres.sks
        trans_sks[s] = CQLSk(s)
    end

    CQLTransform(frozen_inst, frozen_inst, trans_gens, trans_sks)
end

"""Parse a frozen lambda body raw term in the context of the query's dst schema."""
function _parse_frozen_lambda_body(q::CQLQuery, lambda_var::String, entity::Symbol, raw::RawTerm)::CQLTerm
    s = Symbol(raw.head)
    if isempty(raw.args)
        # It's the lambda variable
        if raw.head == lambda_var
            return CQLVar(Symbol(lambda_var))
        end
        # It's a constant
        return CQLSym(s, CQLTerm[])
    elseif length(raw.args) == 1
        inner = _parse_frozen_lambda_body(q, lambda_var, entity, raw.args[1])
        if haskey(q.dst.fks, s)
            return CQLFk(s, inner)
        elseif haskey(q.dst.atts, s)
            return CQLAtt(s, inner)
        elseif has_fk(q.dst, s)
            # Try to resolve
            inner_en = _entity_of_dst_term(q.dst, inner, entity)
            if inner_en !== nothing
                return CQLFk(resolve_fk(q.dst, s, inner_en), inner)
            end
            return CQLFk(s, inner)
        elseif has_att(q.dst, s)
            inner_en = _entity_of_dst_term(q.dst, inner, entity)
            if inner_en !== nothing
                return CQLAtt(resolve_att(q.dst, s, inner_en), inner)
            end
            return CQLAtt(s, inner)
        end
        # Maybe it's a src schema fk/att
        if haskey(q.src.fks, s)
            return CQLFk(s, inner)
        elseif haskey(q.src.atts, s)
            return CQLAtt(s, inner)
        end
        return CQLSym(s, CQLTerm[inner])
    else
        args = CQLTerm[_parse_frozen_lambda_body(q, lambda_var, entity, a) for a in raw.args]
        return CQLSym(s, args)
    end
end

"""Determine the entity of a term in the dst schema."""
function _entity_of_dst_term(sch::CQLSchema, t::CQLTerm, default_en::Symbol)::Union{Symbol, Nothing}
    if t isa CQLVar
        return default_en
    elseif t isa CQLFk
        haskey(sch.fks, t.fk) && return sch.fks[t.fk][2]
        return nothing
    else
        return nothing
    end
end

"""Compose a dst-schema term through a query to get a src-schema term.

For a term like att(fk(var)), trace through:
- var maps to the from-context of the entity block
- fk maps using q.fks[fk] (which gives variable mappings)
- att maps using q.atts[att]"""
function _compose_term_through_query(q::CQLQuery, entity::Symbol, t::CQLTerm)::CQLTerm
    if t isa CQLVar
        # The lambda variable references the entity block; return it as-is
        # (it will be the identity — each from-var maps to itself)
        return t
    elseif t isa CQLAtt
        if haskey(q.atts, t.att)
            # Substitute inner term into the query's attribute definition
            inner_composed = _compose_term_through_query(q, entity, t.arg)
            return _subst_query_term(q.atts[t.att], inner_composed, q, entity)
        end
        # If not a dst att, it's a src att — pass through
        return CQLAtt(t.att, _compose_term_through_query(q, entity, t.arg))
    elseif t isa CQLFk
        if haskey(q.fks, t.fk)
            # FK composition: the FK maps variables in target entity to terms in source
            inner_composed = _compose_term_through_query(q, entity, t.arg)
            # q.fks[fk] gives Dict{Symbol, CQLTerm} mapping tgt entity vars to src terms
            # We need to apply this substitution
            return _apply_fk_mapping(q.fks[t.fk], inner_composed, q, entity)
        end
        return CQLFk(t.fk, _compose_term_through_query(q, entity, t.arg))
    elseif t isa CQLSym
        return CQLSym(t.sym, CQLTerm[_compose_term_through_query(q, entity, a) for a in t.args])
    else
        return t
    end
end

"""Substitute variables in a query term definition with composed values."""
function _subst_query_term(template::CQLTerm, composed_inner::CQLTerm,
                            q::CQLQuery, entity::Symbol)::CQLTerm
    # The template uses CQLVar(:x) etc. for from-clause variables.
    # We need to replace these with corresponding terms from the query context.
    # For the simple case where template directly uses from-vars, return as-is
    # (the vars will be resolved later to frozen instance generators)
    template
end

"""Apply a FK variable mapping."""
function _apply_fk_mapping(var_map::Dict{Symbol, CQLTerm}, composed_inner::CQLTerm,
                            q::CQLQuery, entity::Symbol)::CQLTerm
    # For simple cases, return the composed inner term
    composed_inner
end

# ============================================================================
# Anonymize instance
# ============================================================================

"""Anonymize an instance by renaming all generators to anonymous names."""
function _eval_anonymize_instance(inst::CQLInstance, opts::CQLOptions)::CQLInstance
    sch = inst.schema

    if isempty(inst.pres.gens)
        return inst
    end

    # Build rename map
    rename_map = Dict{Symbol, Symbol}()
    for (i, (g, _)) in enumerate(inst.pres.gens)
        rename_map[g] = Symbol("_anon_", i)
    end

    # Rename skolems too
    sk_rename = Dict{Symbol, Symbol}()
    for (i, (s, _)) in enumerate(inst.pres.sks)
        sk_rename[s] = Symbol("_anon_sk_", i)
    end

    new_gens = Dict{Symbol, Symbol}(rename_map[g] => en for (g, en) in inst.pres.gens)
    new_sks = Dict{Symbol, Symbol}(sk_rename[s] => ty for (s, ty) in inst.pres.sks)
    new_eqs = Set{Equation}()
    for eq in inst.pres.eqs
        new_lhs = _rename_term(eq.lhs, rename_map, sk_rename)
        new_rhs = _rename_term(eq.rhs, rename_map, sk_rename)
        push!(new_eqs, Equation(new_lhs, new_rhs))
    end

    new_gen_order = Symbol[get(rename_map, g, g) for g in inst.pres.gen_order if haskey(rename_map, g)]
    new_pres = Presentation(new_gens, new_sks, new_eqs, new_gen_order)
    col = presentation_to_collage(sch, new_pres)
    prover = create_prover(col, opts)
    dp_fn = eq -> prover(Ctx(), eq)
    initial_instance(new_pres, dp_fn, sch)
end

# ============================================================================
# Cascade delete
# ============================================================================

"""Cascade delete: remove generators that violate FK constraints.

Iteratively removes generators whose FK targets don't exist, until a fixed point."""
function _eval_cascade_delete(inst::CQLInstance, sch::CQLSchema, opts::CQLOptions)::CQLInstance
    # If no FKs, nothing to cascade
    if isempty(sch.fks)
        return inst
    end

    current_gens = copy(inst.pres.gens)
    changed = true

    while changed
        changed = false
        to_remove = Set{Symbol}()

        for (g, en) in current_gens
            for (fk, (fk_src, fk_tgt)) in sch.fks
                fk_src == en || continue
                # Check if there's a target for this FK
                # Look through equations to find what fk(g) equals
                has_target = false
                for (g2, en2) in current_gens
                    if en2 == fk_tgt
                        has_target = true
                        break
                    end
                end
                if !has_target
                    push!(to_remove, g)
                end
            end
        end

        if !isempty(to_remove)
            changed = true
            for g in to_remove
                delete!(current_gens, g)
            end
        end
    end

    if length(current_gens) == length(inst.pres.gens)
        return inst
    end

    if isempty(current_gens)
        return empty_instance(sch)
    end

    # Rebuild instance with remaining generators
    removed = Set{Symbol}(g for (g, _) in inst.pres.gens if !haskey(current_gens, g))
    keep_eqs = Set{Equation}()
    for eq in inst.pres.eqs
        if !_term_references_any(eq.lhs, removed) && !_term_references_any(eq.rhs, removed)
            push!(keep_eqs, eq)
        end
    end

    # Keep skolems that aren't referenced by removed generators
    keep_sks = copy(inst.pres.sks)

    keep_gen_order2 = Symbol[g for g in inst.pres.gen_order if haskey(current_gens, g)]
    new_pres = Presentation(current_gens, keep_sks, keep_eqs, keep_gen_order2)
    col = presentation_to_collage(sch, new_pres)
    prover = create_prover(col, opts)
    dp_fn = eq -> prover(Ctx(), eq)
    initial_instance(new_pres, dp_fn, sch)
end

# ============================================================================
# Spanify: convert relational schema to RDF span representation
# ============================================================================

const RDF_TYPE_PREDICATE = Symbol("http://www.w3.org/1999/02/22-rdf-syntax-ns#type")

"""Build spanified schema from a relational schema on the RDF typeside.

For each entity E: creates entity E with subject : E → Dom
For each FK f: A → B: creates entity f_A_B with FKs subject → A, object → B
For each att a: E → Dom: creates entity a_E with FK subject → E, attribute object → Dom"""
function _eval_schema_spanify(sch::CQLSchema)::CQLSchema
    ts = sch.typeside
    span_ens = Set{Symbol}()
    span_fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    span_atts = Dict{Symbol, Tuple{Symbol, Symbol}}()

    # For each entity: create entity with subject attribute
    for en in sch.ens
        push!(span_ens, en)
        # Qualify attribute: Entity__subject
        att_name = Symbol(en, :__, :subject)
        span_atts[att_name] = (en, :Dom)
    end

    # For each FK: create reified entity with subject/object FKs
    for (fk, (src, tgt)) in sch.fks
        fk_en = Symbol(fk, :_, src, :_, tgt)
        push!(span_ens, fk_en)
        # subject FK: fk_entity → source entity
        subj_fk = Symbol(fk_en, :__, :subject)
        span_fks[subj_fk] = (fk_en, src)
        # object FK: fk_entity → target entity
        obj_fk = Symbol(fk_en, :__, :object)
        span_fks[obj_fk] = (fk_en, tgt)
    end

    # For each attribute: create reified entity with subject FK and object attribute
    for (att, (src, ty)) in sch.atts
        att_en = Symbol(att, :_, src)
        push!(span_ens, att_en)
        # subject FK: att_entity → source entity
        subj_fk = Symbol(att_en, :__, :subject)
        span_fks[subj_fk] = (att_en, src)
        # object attribute: att_entity → Dom
        obj_att = Symbol(att_en, :__, :object)
        span_atts[obj_att] = (att_en, :Dom)
    end

    # Build name resolution maps
    fk_by_name = Dict{Symbol, Vector{Symbol}}()
    for fk_name in keys(span_fks)
        s = string(fk_name)
        idx = findfirst("__", s)
        if idx !== nothing
            plain = Symbol(s[last(idx)+1:end])
            if !haskey(fk_by_name, plain)
                fk_by_name[plain] = Symbol[]
            end
            push!(fk_by_name[plain], fk_name)
        end
    end
    att_by_name = Dict{Symbol, Vector{Symbol}}()
    for att_name in keys(span_atts)
        s = string(att_name)
        idx = findfirst("__", s)
        if idx !== nothing
            plain = Symbol(s[last(idx)+1:end])
            if !haskey(att_by_name, plain)
                att_by_name[plain] = Symbol[]
            end
            push!(att_by_name[plain], att_name)
        end
    end

    eq_fn = (en, eq) -> eq.lhs == eq.rhs
    CQLSchema(ts, span_ens, span_fks, span_atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(), eq_fn,
        fk_by_name, att_by_name, collect(keys(span_fks)))
end

"""Build spanify query: rdf → spanify(S).

The query extracts structured instances from RDF data."""
function _eval_query_spanify(sch::CQLSchema)::CQLQuery
    rdf_sch = _get_rdf_schema(sch.typeside)
    span_sch = _eval_schema_spanify(sch)

    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}()
    fks = Dict{Symbol, Dict{Symbol, CQLTerm}}()
    atts = Dict{Symbol, CQLTerm}()

    # For each entity E: query block with c:R, predicate(c)="type", object(c)="E"
    for en in sch.ens
        ctx = Dict{Symbol,Symbol}(:c => :R)
        where_eqs = Set{Equation}([
            Equation(CQLAtt(:predicate, CQLVar(:c)),
                     CQLSym(RDF_TYPE_PREDICATE, CQLTerm[])),
            Equation(CQLAtt(:object, CQLVar(:c)),
                     CQLSym(en, CQLTerm[]))
        ])
        ens[en] = (ctx, where_eqs)
        # Attribute mapping: en.subject → c.subject
        att_name = Symbol(en, :__, :subject)
        atts[att_name] = CQLAtt(:subject, CQLVar(:c))
    end

    # For each FK f: A → B: query block with r,rs,rt:R
    for (fk, (src, tgt)) in sch.fks
        fk_en = Symbol(fk, :_, src, :_, tgt)
        ctx = Dict{Symbol,Symbol}(:r => :R, :rs => :R, :rt => :R)
        where_eqs = Set{Equation}([
            Equation(CQLAtt(:predicate, CQLVar(:r)),
                     CQLSym(fk, CQLTerm[])),
            Equation(CQLAtt(:predicate, CQLVar(:rs)),
                     CQLSym(RDF_TYPE_PREDICATE, CQLTerm[])),
            Equation(CQLAtt(:object, CQLVar(:rs)),
                     CQLSym(src, CQLTerm[])),
            Equation(CQLAtt(:predicate, CQLVar(:rt)),
                     CQLSym(RDF_TYPE_PREDICATE, CQLTerm[])),
            Equation(CQLAtt(:object, CQLVar(:rt)),
                     CQLSym(tgt, CQLTerm[])),
            Equation(CQLAtt(:subject, CQLVar(:r)),
                     CQLAtt(:subject, CQLVar(:rs))),
            Equation(CQLAtt(:object, CQLVar(:r)),
                     CQLAtt(:subject, CQLVar(:rt)))
        ])
        ens[fk_en] = (ctx, where_eqs)
        # FK mappings: subject → rs, object → rt
        subj_fk = Symbol(fk_en, :__, :subject)
        obj_fk = Symbol(fk_en, :__, :object)
        fks[subj_fk] = Dict(:c => CQLVar(:rs))
        fks[obj_fk] = Dict(:c => CQLVar(:rt))
    end

    # For each attribute a: E → Dom: query block with r,rs:R
    for (att, (src, _)) in sch.atts
        att_en = Symbol(att, :_, src)
        ctx = Dict{Symbol,Symbol}(:r => :R, :rs => :R)
        where_eqs = Set{Equation}([
            Equation(CQLAtt(:predicate, CQLVar(:r)),
                     CQLSym(att, CQLTerm[])),
            Equation(CQLAtt(:predicate, CQLVar(:rs)),
                     CQLSym(RDF_TYPE_PREDICATE, CQLTerm[])),
            Equation(CQLAtt(:object, CQLVar(:rs)),
                     CQLSym(src, CQLTerm[])),
            Equation(CQLAtt(:subject, CQLVar(:r)),
                     CQLAtt(:subject, CQLVar(:rs)))
        ])
        ens[att_en] = (ctx, where_eqs)
        # FK mapping: subject → rs
        subj_fk = Symbol(att_en, :__, :subject)
        fks[subj_fk] = Dict(:c => CQLVar(:rs))
        # Attribute mapping: object → r.object
        obj_att = Symbol(att_en, :__, :object)
        atts[obj_att] = CQLAtt(:object, CQLVar(:r))
    end

    CQLQuery(rdf_sch, span_sch, ens, fks, atts)
end

"""Build spanify_mapping query: spanify(T) → spanify(S) from mapping M: S → T."""
function _eval_query_spanify_mapping(m::CQLMapping)::CQLQuery
    src_sch = m.src
    tgt_sch = m.dst
    span_src = _eval_schema_spanify(src_sch)
    span_tgt = _eval_schema_spanify(tgt_sch)

    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}()
    fks = Dict{Symbol, Dict{Symbol, CQLTerm}}()
    atts = Dict{Symbol, CQLTerm}()

    # For each entity E_src that maps to E_tgt:
    for (src_en, tgt_en) in m.ens
        ctx = Dict{Symbol,Symbol}(:c => tgt_en)
        ens[src_en] = (ctx, Set{Equation}())
        # subject attribute maps through
        src_att = Symbol(src_en, :__, :subject)
        tgt_att = Symbol(tgt_en, :__, :subject)
        atts[src_att] = CQLAtt(tgt_att, CQLVar(:c))
    end

    # For each FK f_src: A_src → B_src that maps through the mapping:
    for (src_fk, fk_term) in m.fks
        (src_a, src_b) = src_sch.fks[src_fk]
        tgt_a = m.ens[src_a]
        tgt_b = m.ens[src_b]
        src_fk_en = Symbol(src_fk, :_, src_a, :_, src_b)

        # Trace the FK path through the target schema
        fk_path = _extract_fk_path(fk_term)

        if length(fk_path) == 1
            # Simple case: f_src maps to single FK f_tgt
            tgt_fk = fk_path[1]
            (tgt_fk_src, tgt_fk_tgt) = tgt_sch.fks[tgt_fk]
            tgt_fk_en = Symbol(tgt_fk, :_, tgt_fk_src, :_, tgt_fk_tgt)
            ctx = Dict{Symbol,Symbol}(:r => tgt_fk_en)
            ens[src_fk_en] = (ctx, Set{Equation}())
            # subject and object FK mappings
            src_subj = Symbol(src_fk_en, :__, :subject)
            src_obj = Symbol(src_fk_en, :__, :object)
            tgt_subj = Symbol(tgt_fk_en, :__, :subject)
            tgt_obj = Symbol(tgt_fk_en, :__, :object)
            fks[src_subj] = Dict(:c => CQLFk(tgt_subj, CQLVar(:r)))
            fks[src_obj] = Dict(:c => CQLFk(tgt_obj, CQLVar(:r)))
        elseif fk_term == CQLVar(:_unit)
            # Identity FK mapping: f -> identity (empty FK path)
            # Match Java: always create rs:M(src), rt:M(tgt) from-vars
            src_subj = Symbol(src_fk_en, :__, :subject)
            src_obj = Symbol(src_fk_en, :__, :object)
            ctx = Dict{Symbol,Symbol}(:rs => tgt_a, :rt => tgt_b)
            ens[src_fk_en] = (ctx, Set{Equation}())
            fks[src_subj] = Dict(:c => CQLVar(:rs))
            fks[src_obj] = Dict(:c => CQLVar(:rt))
        else
            # Multi-hop FK path: f maps to g.h.i (chain of FKs)
            # Match Java: create rs:src_entity, rt:tgt_entity from-vars
            # plus r0..rN for each intermediate FK entity
            ctx = Dict{Symbol,Symbol}()
            where_eqs = Set{Equation}()
            ctx[:rs] = tgt_a
            ctx[:rt] = tgt_b
            var_names = Symbol[]
            for (idx, tgt_fk) in enumerate(fk_path)
                v = Symbol("r", idx - 1)
                push!(var_names, v)
                (tgt_fk_src, tgt_fk_tgt) = tgt_sch.fks[tgt_fk]
                tgt_fk_en = Symbol(tgt_fk, :_, tgt_fk_src, :_, tgt_fk_tgt)
                ctx[v] = tgt_fk_en
            end
            # WHERE: chain object(r_i) = subject(r_{i+1})
            for (idx, tgt_fk) in enumerate(fk_path)
                (tgt_fk_src, tgt_fk_tgt) = tgt_sch.fks[tgt_fk]
                tgt_fk_en = Symbol(tgt_fk, :_, tgt_fk_src, :_, tgt_fk_tgt)
                if idx < length(fk_path)
                    next_tgt_fk = fk_path[idx + 1]
                    (next_src, next_tgt) = tgt_sch.fks[next_tgt_fk]
                    next_fk_en = Symbol(next_tgt_fk, :_, next_src, :_, next_tgt)
                    obj_fk = Symbol(tgt_fk_en, :__, :object)
                    next_subj_fk = Symbol(next_fk_en, :__, :subject)
                    push!(where_eqs, Equation(
                        CQLFk(obj_fk, CQLVar(var_names[idx])),
                        CQLFk(next_subj_fk, CQLVar(var_names[idx + 1]))
                    ))
                end
            end
            # WHERE: first FK subject = rs, last FK object = rt
            first_fk = fk_path[1]
            (first_src, first_tgt) = tgt_sch.fks[first_fk]
            first_fk_en = Symbol(first_fk, :_, first_src, :_, first_tgt)
            first_subj = Symbol(first_fk_en, :__, :subject)
            push!(where_eqs, Equation(
                CQLFk(first_subj, CQLVar(var_names[1])),
                CQLVar(:rs)
            ))
            last_fk = fk_path[end]
            (last_src, last_tgt) = tgt_sch.fks[last_fk]
            last_fk_en = Symbol(last_fk, :_, last_src, :_, last_tgt)
            last_obj = Symbol(last_fk_en, :__, :object)
            push!(where_eqs, Equation(
                CQLFk(last_obj, CQLVar(var_names[end])),
                CQLVar(:rt)
            ))
            ens[src_fk_en] = (ctx, where_eqs)
            # FK subject/object mappings use rs/rt directly
            src_subj = Symbol(src_fk_en, :__, :subject)
            src_obj = Symbol(src_fk_en, :__, :object)
            fks[src_subj] = Dict(:c => CQLVar(:rs))
            fks[src_obj] = Dict(:c => CQLVar(:rt))
        end
    end

    # For each attribute a_src: E_src → Dom that maps through:
    for (src_att, att_term) in m.atts
        (src_en, _) = src_sch.atts[src_att]
        src_att_en = Symbol(src_att, :_, src_en)
        tgt_en = m.ens[src_en]

        # Extract the path: the att_term is like att_tgt(fk_path(x))
        (tgt_fk_path, tgt_att_name) = _extract_att_path(att_term)

        if isempty(tgt_fk_path) && tgt_att_name !== nothing
            # Simple: src att maps directly to tgt att
            # Match Java: from rs:tgt_entity, rt:tgt_att_entity
            tgt_att_en = Symbol(tgt_att_name, :_, tgt_en)
            ctx = Dict{Symbol,Symbol}(:rs => tgt_en, :rt => tgt_att_en)
            ens[src_att_en] = (ctx, Set{Equation}())
            src_subj = Symbol(src_att_en, :__, :subject)
            fks[src_subj] = Dict(:c => CQLVar(:rs))
            src_obj = Symbol(src_att_en, :__, :object)
            tgt_obj = Symbol(tgt_att_en, :__, :object)
            atts[src_obj] = CQLAtt(tgt_obj, CQLVar(:rt))
        else
            # att with FK path: src_att maps to att_tgt(fk1.fk2...fkn(x))
            if tgt_att_name !== nothing
                tgt_att_en_name = Symbol(tgt_att_name, :_, tgt_en)
                ctx = Dict{Symbol,Symbol}()
                where_eqs = Set{Equation}()
                ctx[:rs] = tgt_en
                ctx[:rt] = tgt_att_en_name
                var_names = Symbol[]
                for (idx, tgt_fk) in enumerate(tgt_fk_path)
                    v = Symbol("r", idx - 1)
                    push!(var_names, v)
                    (fk_src, fk_tgt) = tgt_sch.fks[tgt_fk]
                    fk_en = Symbol(tgt_fk, :_, fk_src, :_, fk_tgt)
                    ctx[v] = fk_en
                end
                # WHERE: chain object(r_i) = subject(r_{i+1})
                for (idx, tgt_fk) in enumerate(tgt_fk_path)
                    (fk_src, fk_tgt) = tgt_sch.fks[tgt_fk]
                    fk_en = Symbol(tgt_fk, :_, fk_src, :_, fk_tgt)
                    if idx < length(tgt_fk_path)
                        next_fk = tgt_fk_path[idx + 1]
                        (ns, nt) = tgt_sch.fks[next_fk]
                        next_en = Symbol(next_fk, :_, ns, :_, nt)
                        push!(where_eqs, Equation(
                            CQLFk(Symbol(fk_en, :__, :object), CQLVar(var_names[idx])),
                            CQLFk(Symbol(next_en, :__, :subject), CQLVar(var_names[idx + 1]))
                        ))
                    end
                end
                if !isempty(tgt_fk_path)
                    first_fk = tgt_fk_path[1]
                    (fs, ft) = tgt_sch.fks[first_fk]
                    first_en = Symbol(first_fk, :_, fs, :_, ft)
                    push!(where_eqs, Equation(
                        CQLFk(Symbol(first_en, :__, :subject), CQLVar(var_names[1])),
                        CQLVar(:rs)
                    ))
                    last_fk = tgt_fk_path[end]
                    (ls, lt) = tgt_sch.fks[last_fk]
                    last_en = Symbol(last_fk, :_, ls, :_, lt)
                    push!(where_eqs, Equation(
                        CQLFk(Symbol(last_en, :__, :object), CQLVar(var_names[end])),
                        CQLVar(:rt)
                    ))
                end
                ens[src_att_en] = (ctx, where_eqs)
                src_subj = Symbol(src_att_en, :__, :subject)
                fks[src_subj] = Dict(:c => CQLVar(:rs))
                src_obj = Symbol(src_att_en, :__, :object)
                tgt_obj = Symbol(tgt_att_en_name, :__, :object)
                atts[src_obj] = CQLAtt(tgt_obj, CQLVar(:rt))
            end
        end
    end

    CQLQuery(span_tgt, span_src, ens, fks, atts)
end

"""Get the RDF schema."""
function _get_rdf_schema(ts::Typeside)::CQLSchema
    ens = Set{Symbol}([:R])
    fks = Dict{Symbol,Tuple{Symbol,Symbol}}()
    atts = Dict{Symbol,Tuple{Symbol,Symbol}}(
        :subject => (:R, :Dom),
        :predicate => (:R, :Dom),
        :object => (:R, :Dom),
    )
    CQLSchema(ts, ens, fks, atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(),
        (en, eq) -> eq.lhs == eq.rhs)
end

"""Extract FK path from a mapping FK term like fk3(fk2(fk1(_unit)))."""
function _extract_fk_path(t::CQLTerm)::Vector{Symbol}
    path = Symbol[]
    current = t
    while current isa CQLFk
        pushfirst!(path, current.fk)
        current = current.arg
    end
    path
end

"""Extract FK path and final attribute from a mapping attribute term like att(fk2(fk1(_unit)))."""
function _extract_att_path(t::CQLTerm)::Tuple{Vector{Symbol}, Union{Symbol, Nothing}}
    if t isa CQLAtt
        fk_path = _extract_fk_path(t.arg)
        return (fk_path, t.att)
    elseif t isa CQLFk
        # Shouldn't happen for attribute terms
        return (_extract_fk_path(t), nothing)
    else
        return (Symbol[], nothing)
    end
end

"""Replace CQLGen(g) with CQLVar(rename[g]) in a term."""
function _gens_to_vars(t::CQLTerm, rename::Dict{Symbol,Symbol})::CQLTerm
    if t isa CQLGen
        haskey(rename, t.gen) ? CQLVar(rename[t.gen]) : t
    elseif t isa CQLFk
        CQLFk(t.fk, _gens_to_vars(t.arg, rename))
    elseif t isa CQLAtt
        CQLAtt(t.att, _gens_to_vars(t.arg, rename))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_gens_to_vars(a, rename) for a in t.args])
    else
        t
    end
end

"""Compute rext(q1, q2) — right extension.

Given q1: A→B and q2: A→C, produces a query B→C.

Algorithm: For each entity c in C, evaluate Q1 on Q2's frozen instance at c.
The eval result's generators become from-variables, equations become where-clause.
FK mappings are derived by evaluating Q1 on Q2's FK transforms."""
function _eval_rext(q1::CQLQuery, q2::CQLQuery, opts::CQLOptions)::CQLQuery
    ens = Dict{Symbol, Tuple{Dict{Symbol,Symbol}, Set{Equation}}}()
    fks = Dict{Symbol, Dict{Symbol, CQLTerm}}()
    atts = Dict{Symbol, CQLTerm}()

    counter = Ref(0)
    entity_data = Dict{Symbol, Any}()

    # Step 1: Build entity blocks
    for c_en in q2.dst.ens
        # Frozen instance of Q2 at c_en (instance on A = q2.src)
        frozen_c = _eval_frozen_instance(q2, c_en, opts)

        # Evaluate Q1 on frozen instance (instance on B = q1.dst)
        eval_inst = eval_query_instance(q1, frozen_c, opts)

        # Create unique variable names for eval generators
        rename = Dict{Symbol, Symbol}()
        from_ctx = Dict{Symbol, Symbol}()
        for (g, en) in eval_inst.pres.gens
            counter[] += 1
            new_name = Symbol("v_", counter[])
            rename[g] = new_name
            from_ctx[new_name] = en
        end

        # Convert equations: CQLGen → CQLVar
        where_eqs = Set{Equation}()
        for eq in eval_inst.pres.eqs
            lhs = _gens_to_vars(eq.lhs, rename)
            rhs = _gens_to_vars(eq.rhs, rename)
            push!(where_eqs, Equation(lhs, rhs))
        end

        ens[c_en] = (from_ctx, where_eqs)
        entity_data[c_en] = (frozen=frozen_c, eval_inst=eval_inst, rename=rename)
    end

    # Step 2: FK mappings
    for (fk_name, (fk_src_en, fk_tgt_en)) in q2.dst.fks
        fk_var_mapping = q2.fks[fk_name]

        frozen_src = entity_data[fk_src_en].frozen
        frozen_tgt = entity_data[fk_tgt_en].frozen
        rename_src = entity_data[fk_src_en].rename
        rename_tgt = entity_data[fk_tgt_en].rename

        # Build transform: frozen_tgt → frozen_src
        # Q2.fks[fk] maps tgt entity's from-vars to src entity's terms
        tr_gens = Dict{Symbol, CQLTerm}()
        for (v, _) in frozen_tgt.pres.gens
            if haskey(fk_var_mapping, v)
                tr_gens[v] = _vars_to_gens_sks(fk_var_mapping[v],
                    frozen_src.pres.gens, frozen_src.pres.sks)
            end
        end
        tr_sks = Dict{Symbol, CQLTerm}()
        for (sk, _) in frozen_tgt.pres.sks
            if haskey(fk_var_mapping, sk)
                tr_sks[sk] = _vars_to_gens_sks(fk_var_mapping[sk],
                    frozen_src.pres.gens, frozen_src.pres.sks)
            end
        end
        tr = CQLTransform(frozen_tgt, frozen_src, tr_gens, tr_sks)

        # Evaluate Q1 on this transform
        eval_tr = eval_query_transform(q1, tr, opts)

        # Extract FK mapping: maps tgt entity's rext vars to src entity's rext terms
        fk_mapping = Dict{Symbol, CQLTerm}()
        for (g_tgt, mapped_term) in eval_tr.gens
            if haskey(rename_tgt, g_tgt)
                new_tgt_var = rename_tgt[g_tgt]
                new_term = _gens_to_vars(mapped_term, rename_src)
                fk_mapping[new_tgt_var] = new_term
            end
        end
        fks[fk_name] = fk_mapping
    end

    # Step 3: Attribute mappings
    # For now, handle identity-like cases where Q1 is identity
    # (general case requires EvalTransform-like attribute composition)
    if !isempty(q2.dst.atts) && _is_identity_mapping_query(q1)
        # For identity Q1: frozen gens map 1-to-1 to eval gens
        # Build mapping from frozen gen name to rext var name
        for (att_name, (att_en, att_ty)) in q2.dst.atts
            att_term = q2.atts[att_name]
            rename = entity_data[att_en].rename
            frozen_c = entity_data[att_en].frozen
            eval_inst = entity_data[att_en].eval_inst

            # Build frozen gen → rext var mapping
            frozen_to_rext = Dict{Symbol, Symbol}()
            for (g, en) in frozen_c.pres.gens
                # For identity Q1: gen q_{en}_1 has tuple {x => g_elem}
                # Find the eval gen of entity en
                for (eg, ee) in eval_inst.pres.gens
                    if ee == en
                        elem = eval_inst.algebra.gen[eg]
                        repr = repr_x(eval_inst.algebra, elem)
                        if repr isa CQLGen && repr.gen == eg
                            # Check if this eval gen's tuple maps to frozen gen g
                            felem = frozen_c.algebra.gen[g]
                            if haskey(eval_inst.algebra.gen, eg)
                                frozen_to_rext[g] = rename[eg]
                                break
                            end
                        end
                    end
                end
            end

            # Substitute Q2 att term: CQLVar(w) → CQLVar(frozen_to_rext[w])
            atts[att_name] = _subst_frozen_vars(att_term, frozen_to_rext)
        end
    elseif !isempty(q2.dst.atts)
        throw(CQLException("rext with attributes for non-identity Q1 is not yet supported"))
    end

    CQLQuery(q1.dst, q2.dst, ens, fks, atts)
end

"""Check if a query is essentially the identity query."""
function _is_identity_mapping_query(q::CQLQuery)::Bool
    q.src == q.dst || return false
    for (en, (ctx, wheres)) in q.ens
        length(ctx) == 1 || return false
        isempty(wheres) || return false
        first(values(ctx)) == en || return false
    end
    return true
end

"""Substitute CQLVar(v) with CQLVar(mapping[v]) in a term."""
function _subst_frozen_vars(t::CQLTerm, mapping::Dict{Symbol,Symbol})::CQLTerm
    if t isa CQLVar
        haskey(mapping, t.name) ? CQLVar(mapping[t.name]) : t
    elseif t isa CQLFk
        CQLFk(t.fk, _subst_frozen_vars(t.arg, mapping))
    elseif t isa CQLAtt
        CQLAtt(t.att, _subst_frozen_vars(t.arg, mapping))
    elseif t isa CQLSym
        CQLSym(t.sym, CQLTerm[_subst_frozen_vars(a, mapping) for a in t.args])
    else
        t
    end
end

