using Test
using CQL
using Catlab

@testset "Catlab Interop" begin
    @testset "Schema conversion" begin
        ts_raw = CQL.TypesideRaw(["string"], [], [], [], [], [], [])
        ts = CQL.eval_typeside_raw(default_options(), ts_raw)
        sch_raw = CQL.SchemaRaw(
            nothing,
            ["Person", "Dept"],
            [("worksIn", ("Person", "Dept"))],
            [("name", ("Person", "string"))],
            [], [], [], [],
        )
        sch = CQL.eval_schema_raw(default_options(), ts, sch_raw)

        catlab_info = CQL.cql_schema_to_catlab(sch)
        @test catlab_info.schema isa BasicSchema
    end
end
