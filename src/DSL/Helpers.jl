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
