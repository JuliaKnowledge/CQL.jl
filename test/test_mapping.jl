using Test
using CQL

@testset "Mapping" begin
    @testset "Identity mapping" begin
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

        m = CQL.identity_mapping(sch)
        @test m.ens[:E] == :E
        @test haskey(m.fks, :f)
        @test haskey(m.atts, :a)
    end

    @testset "Mapping composition" begin
        ts_raw = CQL.TypesideRaw(["string"], [], [], [], [], [], [])
        ts = CQL.eval_typeside_raw(default_options(), ts_raw)
        sch_raw = CQL.SchemaRaw(
            nothing, ["E"], [], [], [], [], [], [],
        )
        sch = CQL.eval_schema_raw(default_options(), ts, sch_raw)

        m1 = CQL.identity_mapping(sch)
        m2 = CQL.identity_mapping(sch)
        composed = CQL.compose_mapping(m1, m2)
        @test composed.ens[:E] == :E
    end
end
