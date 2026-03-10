using Test
using CQL

@testset "Collage" begin
    @testset "Construction" begin
        col = CQL.Collage(
            Set{Tuple{CQL.Ctx, Equation}}(),
            Set{Symbol}([:String, :Int]),
            Set{Symbol}([:Employee]),
            Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}(:plus => ([:Int, :Int], :Int)),
            Dict{Symbol, Tuple{Symbol, Symbol}}(:manager => (:Employee, :Employee)),
            Dict{Symbol, Tuple{Symbol, Symbol}}(:name => (:Employee, :String)),
            Dict{Symbol, Symbol}(:a => :Employee),
            Dict{Symbol, Symbol}(:sk1 => :String),
        )
        @test :String in col.ctys
        @test :Employee in col.cens
        @test haskey(col.cfks, :manager)
    end

    @testset "type_of_term" begin
        col = CQL.Collage(
            Set{Tuple{CQL.Ctx, Equation}}(),
            Set{Symbol}([:String]),
            Set{Symbol}([:Employee]),
            Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}(),
            Dict{Symbol, Tuple{Symbol, Symbol}}(:manager => (:Employee, :Employee)),
            Dict{Symbol, Tuple{Symbol, Symbol}}(:name => (:Employee, :String)),
            Dict{Symbol, Symbol}(:a => :Employee),
            Dict{Symbol, Symbol}(),
        )
        ctx = CQL.Ctx()
        # Gen should type to Right(entity)
        ty = CQL.type_of_term(col, ctx, CQLGen(:a))
        @test CQL.is_right(ty)
        @test CQL.get_right(ty) == :Employee

        # FK of gen
        ty2 = CQL.type_of_term(col, ctx, CQLFk(:manager, CQLGen(:a)))
        @test CQL.is_right(ty2)
        @test CQL.get_right(ty2) == :Employee

        # Att of gen
        ty3 = CQL.type_of_term(col, ctx, CQLAtt(:name, CQLGen(:a)))
        @test CQL.is_left(ty3)
        @test CQL.get_left(ty3) == :String
    end
end
