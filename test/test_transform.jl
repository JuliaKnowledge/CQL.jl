using Test
using CQL

@testset "Transform" begin
    @testset "Identity transform" begin
        ts_raw = CQL.TypesideRaw(["string"], [], [], [], [], [], [])
        ts = CQL.eval_typeside_raw(default_options(), ts_raw)
        sch_raw = CQL.SchemaRaw(
            nothing,
            ["Person"],
            [],
            [("name", ("Person", "string"))],
            [], [], [], [],
        )
        sch = CQL.eval_schema_raw(default_options(), ts, sch_raw)
        inst_raw = CQL.InstExpRaw(nothing, [("alice", "Person")], [], [], [])
        inst = CQL.eval_instance_raw(default_options(), sch, inst_raw)

        tr = CQL.identity_transform(inst)
        @test tr.src === inst
        @test tr.dst === inst
        @test haskey(tr.gens, :alice)
        @test tr.gens[:alice] == CQLGen(:alice)
    end
end
