using Test
using CQL

@testset "Query" begin
    @testset "Identity query" begin
        ts_raw = CQL.TypesideRaw(["string"], [], [], [], [], [], [])
        ts = CQL.eval_typeside_raw(default_options(), ts_raw)
        sch_raw = CQL.SchemaRaw(
            nothing,
            ["E"],
            [("f", ("E", "E"))],
            [("a", ("E", "string"))],
            [], [], [], [],
        )
        sch = CQL.eval_schema_raw(default_options(), ts, sch_raw)

        q = CQL.identity_query(sch)
        @test q.src === sch
        @test q.dst === sch
        @test haskey(q.ens, :E)
        @test haskey(q.fks, :f)
        @test haskey(q.atts, :a)
    end
end
