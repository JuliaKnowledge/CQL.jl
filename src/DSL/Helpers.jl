# ─── Helper functions for DSL macro evaluation ──────────────────────────────
#
# These create Env structs pre-loaded with existing CQL objects,
# then evaluate a CQL source fragment in that context.

"""Create an Env with a single typeside pre-loaded."""
function _make_env_with_typeside(name::String, ts::Typeside)
    env = Env(default_options())
    env.typesides[name] = ts
    env
end

"""Create an Env with a schema (and its typeside) pre-loaded."""
function _make_env_with_schema(name::String, sch::CQLSchema)
    env = Env(default_options())
    env.typesides["_TS"] = sch.typeside
    env.schemas[name] = sch
    env
end

"""Create an Env with two schemas (and their typesides) pre-loaded."""
function _make_env_with_schemas(src_name::String, src::CQLSchema, dst_name::String, dst::CQLSchema)
    env = Env(default_options())
    env.typesides["_TS"] = src.typeside
    env.schemas[src_name] = src
    env.schemas[dst_name] = dst
    env
end

"""Create an Env with two instances (and their schema/typeside) pre-loaded."""
function _make_env_with_instances(src_name::String, src::CQLInstance, dst_name::String, dst::CQLInstance)
    env = Env(default_options())
    env.typesides["_TS"] = src.schema.typeside
    env.schemas["_S"] = src.schema
    env.instances[src_name] = src
    env.instances[dst_name] = dst
    env
end

"""Add a schema to an existing Env."""
function _add_schema!(env::Env, name::String, sch::CQLSchema)
    env.schemas[name] = sch
end

"""Build a CQL mapping from name→name pairs, classifying by source schema."""
function _build_mapping_from_pairs(src::CQLSchema, dst::CQLSchema,
                                    pairs::Vector{Tuple{String,String}},
                                    opts::Vector{Tuple{String,String}}=Tuple{String,String}[])
    src_ens = Set(string(e) for e in src.ens)
    # Collect qualified and display FK/att names
    src_fk_names = Set{String}()
    for k in keys(src.fks)
        push!(src_fk_names, string(k))
    end
    for (name, qnames) in src.fk_by_name
        push!(src_fk_names, string(name))
    end
    src_att_names = Set{String}()
    for k in keys(src.atts)
        push!(src_att_names, string(k))
    end
    for (name, qnames) in src.att_by_name
        push!(src_att_names, string(name))
    end

    en_maps = Tuple{String,String}[]
    fk_maps = Tuple{String,String}[]
    att_maps = Tuple{String,String}[]

    for (lhs, rhs) in pairs
        if lhs in src_ens
            push!(en_maps, (lhs, rhs))
        elseif lhs in src_fk_names
            push!(fk_maps, (lhs, rhs))
        elseif lhs in src_att_names
            push!(att_maps, (lhs, rhs))
        else
            # Default: try as entity, then fk, then att
            push!(en_maps, (lhs, rhs))
        end
    end

    # Generate proper CQL mapping source
    lines = String["mapping _M = literal : _SRC -> _DST {"]
    for (lhs, rhs) in en_maps
        push!(lines, "    entity $lhs -> $rhs")
    end
    if !isempty(fk_maps)
        push!(lines, "    foreign_keys")
        for (lhs, rhs) in fk_maps
            push!(lines, "        $lhs -> $rhs")
        end
    end
    if !isempty(att_maps)
        push!(lines, "    attributes")
        for (lhs, rhs) in att_maps
            push!(lines, "        $lhs -> $rhs")
        end
    end
    if !isempty(opts)
        push!(lines, "    options")
        for (k, v) in opts
            push!(lines, "        $k = $v")
        end
    end
    push!(lines, "}")

    env = _make_env_with_schemas("_SRC", src, "_DST", dst)
    _eval_fragment(env, join(lines, "\n")).mappings["_M"]
end

"""
Evaluate a CQL source fragment in the context of an existing Env.
The fragment can reference objects already in the Env by name.
Returns the updated Env.
"""
function _eval_fragment(env::Env, source::String)
    prog = parse_program(source)

    # Merge global options if present
    opts = isempty(prog.options) ? env.options : to_options(env.options, prog.options)
    env.options = opts

    # Find evaluation order
    order = find_order(prog)

    # Build name -> Exp lookup
    exp_map = Dict{String, Exp}()
    for e in prog.exps
        exp_map[e.name] = e
    end

    # Evaluate new declarations in dependency order, skipping pre-loaded ones
    for (name, kind) in order
        if haskey(exp_map, name)
            # Skip if already loaded in env
            already = if kind == TYPESIDE
                haskey(env.typesides, name)
            elseif kind == SCHEMA
                haskey(env.schemas, name)
            elseif kind == INSTANCE
                haskey(env.instances, name)
            elseif kind == MAPPING
                haskey(env.mappings, name)
            elseif kind == QUERY
                haskey(env.queries, name)
            elseif kind == TRANSFORM
                haskey(env.transforms, name)
            else
                false
            end
            already && continue

            e = exp_map[name]
            exp_opts = get_exp_options(e)
            if !isempty(exp_opts)
                env.options = to_options(opts, exp_opts)
            end
            eval_exp!(env, e)
            env.options = opts
        end
    end

    env
end
