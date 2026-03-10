using Test
using CQL

@testset "Term" begin
    @testset "Construction" begin
        v = CQLVar(:x)
        @test v.name == :x

        g = CQLGen(:a)
        @test g.gen == :a

        sk = CQLSk(:s)
        @test sk.sk == :s

        fk = CQLFk(:f, CQLGen(:a))
        @test fk.fk == :f
        @test fk.arg == CQLGen(:a)

        att = CQLAtt(:att1, CQLVar(:x))
        @test att.att == :att1

        sym = CQLSym(:plus, CQLTerm[CQLVar(:x), CQLVar(:y)])
        @test sym.sym == :plus
        @test length(sym.args) == 2
    end

    @testset "Equality" begin
        @test CQLVar(:x) == CQLVar(:x)
        @test CQLVar(:x) != CQLVar(:y)
        @test CQLGen(:a) == CQLGen(:a)
        @test CQLFk(:f, CQLGen(:a)) == CQLFk(:f, CQLGen(:a))
        @test CQLSym(:plus, CQLTerm[CQLVar(:x)]) == CQLSym(:plus, CQLTerm[CQLVar(:x)])
    end

    @testset "Equation" begin
        eq = Equation(CQLVar(:x), CQLVar(:y))
        @test eq.lhs == CQLVar(:x)
        @test eq.rhs == CQLVar(:y)
    end

    @testset "RawTerm" begin
        r = RawTerm("f", RawTerm[RawTerm("x", RawTerm[])])
        @test r.head == "f"
        @test length(r.args) == 1
    end

    @testset "map_term" begin
        t = CQLFk(:f, CQLGen(:a))
        mapped = CQL.map_term(t, on_fk=f -> Symbol("new_", f))
        @test mapped == CQLFk(:new_f, CQLGen(:a))
    end

    @testset "subst_term" begin
        t = CQLFk(:f, CQLVar(:x))
        result = CQL.subst_term(t, CQLGen(:a))
        @test result == CQLFk(:f, CQLGen(:a))
    end
end
