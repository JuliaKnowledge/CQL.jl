using Test
using CQL

@testset "Schema" begin
    @testset "Schema construction" begin
        ts = CQL.initial_typeside()
        sch = CQL.typeside_to_schema(ts)
        @test isempty(sch.ens)
        @test isempty(sch.fks)
        @test isempty(sch.atts)
    end

    @testset "Raw schema evaluation" begin
        ts_raw = CQL.TypesideRaw(
            ["string"],
            [],
            [],
            [],
            [],
            [],
            [],
        )
        ts = CQL.eval_typeside_raw(default_options(), ts_raw)

        sch_raw = CQL.SchemaRaw(
            nothing,
            ["Employee", "Department"],
            [("manager", ("Employee", "Employee")),
             ("worksIn", ("Employee", "Department"))],
            [("name", ("Employee", "string"))],
            [],
            [],
            [],
            [],
        )
        sch = CQL.eval_schema_raw(default_options(), ts, sch_raw)
        @test :Employee in sch.ens
        @test :Department in sch.ens
        @test haskey(sch.fks, :manager)
        @test haskey(sch.fks, :worksIn)
        @test haskey(sch.atts, :name)
        @test sch.fks[:manager] == (:Employee, :Employee)
        @test sch.fks[:worksIn] == (:Employee, :Department)
    end
end
