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
