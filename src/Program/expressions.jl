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
