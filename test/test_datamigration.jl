using Test
using CQL

@testset "Data Migration" begin
    # We test sigma with identity mapping, which should be a no-op
    @testset "Sigma with identity" begin
        ts_raw = CQL.TypesideRaw(["string"], [], [], [], [], [], [])
        ts = CQL.eval_typeside_raw(default_options(), ts_raw)
        sch_raw = CQL.SchemaRaw(
            nothing,
            ["Person"],
            [],
            [],
            [], [], [], [],
        )
        sch = CQL.eval_schema_raw(default_options(), ts, sch_raw)
        inst_raw = CQL.InstExpRaw(nothing, [("alice", "Person"), ("bob", "Person")], [], [], [])
        inst = CQL.eval_instance_raw(default_options(), sch, inst_raw)

        m = CQL.identity_mapping(sch)
        sigma_inst = CQL.eval_sigma_instance(m, inst, default_options())
        @test length(carrier(sigma_inst.algebra, :Person)) == 2
    end
end
