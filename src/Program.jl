"""
Program evaluation: dependency resolution and eval pipeline.

A CQL program consists of named declarations (typesides, schemas, instances,
mappings, transforms, queries) that are evaluated in dependency order.
"""

include("Program/environment.jl")
include("Program/expressions.jl")
include("Program/imports.jl")
include("Program/queries.jl")
include("Program/runtime.jl")
include("Program/pivot.jl")
include("Program/transforms.jl")
include("Program/constraints_queries.jl")
include("Program/advanced_queries.jl")
