using Test
using CQL

@testset "Instance" begin
    @testset "Empty instance" begin
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
        inst = CQL.empty_instance(sch)
        @test isempty(carrier(inst.algebra, :Person))
    end

    @testset "Raw instance with generators" begin
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

        inst_raw = CQL.InstExpRaw(
            nothing,
            [("alice", "Person"), ("bob", "Person")],
            [],
            [],
            [],
        )
        inst = CQL.eval_instance_raw(default_options(), sch, inst_raw)
        @test length(carrier(inst.algebra, :Person)) == 2
    end
end
