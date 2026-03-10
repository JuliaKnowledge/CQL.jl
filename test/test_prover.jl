using Test
using CQL

@testset "Provers" begin
    @testset "Free prover" begin
        col = CQL.Collage(
            Set{Tuple{CQL.Ctx, Equation}}(),
            Set{Symbol}([:Int]),
            Set{Symbol}(),
            Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}(:zero => (Symbol[], :Int)),
            Dict{Symbol, Tuple{Symbol, Symbol}}(),
            Dict{Symbol, Tuple{Symbol, Symbol}}(),
            Dict{Symbol, Symbol}(),
            Dict{Symbol, Symbol}(),
        )
        prover = CQL.free_prover(col)
        ctx = CQL.Ctx()
        @test prover(ctx, Equation(CQLSym(:zero, CQLTerm[]), CQLSym(:zero, CQLTerm[])))
        @test !prover(ctx, Equation(CQLVar(:x), CQLVar(:y)))
    end

    @testset "Congruence prover" begin
        col = CQL.Collage(
            Set{Tuple{CQL.Ctx, Equation}}(),
            Set{Symbol}(),
            Set{Symbol}([:E]),
            Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}(),
            Dict{Symbol, Tuple{Symbol, Symbol}}(:f => (:E, :E)),
            Dict{Symbol, Tuple{Symbol, Symbol}}(),
            Dict{Symbol, Symbol}(:a => :E, :b => :E),
            Dict{Symbol, Symbol}(),
        )
        # Add equation: a = b
        eq_col = CQL.Collage(
            Set{Tuple{CQL.Ctx, Equation}}([(CQL.Ctx(), Equation(CQLGen(:a), CQLGen(:b)))]),
            col.ctys, col.cens, col.csyms, col.cfks, col.catts, col.cgens, col.csks,
        )
        prover, canonical = CQL.congruence_prover(eq_col)
        ctx = CQL.Ctx()
        @test prover(ctx, Equation(CQLGen(:a), CQLGen(:b)))
        # By congruence: f(a) = f(b)
        @test prover(ctx, Equation(CQLFk(:f, CQLGen(:a)), CQLFk(:f, CQLGen(:b))))
    end
end
