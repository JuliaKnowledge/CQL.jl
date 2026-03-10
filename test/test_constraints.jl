using Test
using CQL

@testset "Constraints and Chase" begin

@testset "Basic EGD chase" begin
    env = cql"""
    typeside Ty = literal {
        types Str
        constants hello world : Str
    }

    schema S = literal : Ty {
        entities A B
        foreign_keys f : A -> B
        attributes
            x : A -> Str
            y : B -> Str
    }

    instance I = literal : S {
        generators a1 : A  b1 : B
        equations
            f(a1) = b1
            x(a1) = hello
    }

    constraints C = literal : S {
        forall a:A
        -> where y(f(a)) = x(a)
    }

    instance Chased = chase C I
    """

    alg = env.Chased.algebra
    @test length(carrier(alg, :A)) == 1
    @test length(carrier(alg, :B)) == 1
    # The chase should have propagated: y(b1) = hello
    for b in carrier(alg, :B)
        yval = eval_att(alg, :y, b)
        @test yval == CQLSym(:hello, CQLTerm[])
    end
end

@testset "Chase with no violations (convergence on first iter)" begin
    env = cql"""
    typeside Ty = literal {
        types Str
        constants v1 v2 : Str
    }

    schema S = literal : Ty {
        entities E
        attributes a : E -> Str
    }

    instance I = literal : S {
        generators e1 : E
        equations a(e1) = v1
    }

    constraints C = literal : S {
        forall x:E
        -> where a(x) = a(x)
    }

    instance Chased = chase C I
    """

    alg = env.Chased.algebra
    @test length(carrier(alg, :E)) == 1
end

end
