using Test
using CQL

@testset "Typeside" begin
    @testset "Initial typeside" begin
        ts = CQL.initial_typeside()
        @test isempty(ts.tys)
        @test isempty(ts.syms)
        @test isempty(ts.eqs)
    end

    @testset "SQL typeside" begin
        ts = CQL.sql_typeside()
        @test :String in ts.tys
        @test :Integer in ts.tys
        @test :Boolean in ts.tys
        @test :Varchar in ts.tys
    end

    @testset "Raw typeside evaluation" begin
        raw = CQL.TypesideRaw(
            ["string", "nat"],
            [("zero", (String[], "nat")), ("succ", (["nat"], "nat"))],
            [],
            [],
            [],
            [],
            [],
        )
        ts = CQL.eval_typeside_raw(default_options(), raw)
        @test :string in ts.tys
        @test :nat in ts.tys
        @test haskey(ts.syms, :zero)
        @test haskey(ts.syms, :succ)
        @test ts.syms[:zero] == (Symbol[], :nat)
        @test ts.syms[:succ] == ([:nat], :nat)
    end
end
