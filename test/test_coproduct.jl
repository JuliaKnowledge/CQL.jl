using Test
using CQL

@testset "Instance Coproduct" begin

@testset "Basic coproduct" begin
    env = cql"""
    typeside Ty = literal {
        types Str
        constants a b c d : Str
    }

    schema S = literal : Ty {
        entities E
        attributes name : E -> Str
    }

    instance I1 = literal : S {
        generators x1 : E
        equations name(x1) = a
    }

    instance I2 = literal : S {
        generators x2 : E
        equations name(x2) = b
    }

    instance Merged = coproduct I1 + I2 : S
    """

    alg = env.Merged.algebra
    @test length(carrier(alg, :E)) == 2
end

@testset "Three-way coproduct" begin
    env = cql"""
    typeside Ty = literal {
        types Str
        constants a b c : Str
    }

    schema S = literal : Ty {
        entities E
        attributes name : E -> Str
    }

    instance I1 = literal : S {
        generators x : E
        equations name(x) = a
    }

    instance I2 = literal : S {
        generators y : E
        equations name(y) = b
    }

    instance I3 = literal : S {
        generators z : E
        equations name(z) = c
    }

    instance Merged = coproduct I1 + I2 + I3 : S
    """

    alg = env.Merged.algebra
    @test length(carrier(alg, :E)) == 3
end

end
