using Test
using CQL

@testset "CQL.jl" begin
    include("test_term.jl")
    include("test_collage.jl")
    include("test_prover.jl")
    include("test_kb_completion.jl")
    include("test_typeside.jl")
    include("test_options.jl")
    include("test_schema.jl")
    include("test_instance.jl")
    include("test_mapping.jl")
    include("test_transform.jl")
    include("test_query.jl")
    include("test_datamigration.jl")
    include("test_parser.jl")
    include("test_program.jl")
    include("test_optional_loading.jl")
    include("test_constraints.jl")
    include("test_coproduct.jl")
    include("test_dsl.jl")
    include("test_integration.jl")
    include("test_schema_colimit.jl")
    include("test_catlab_interop.jl")
end
