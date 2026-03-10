using Test
using CQL

@testset "Schema Colimit" begin

@testset "Basic quotient colimit" begin
    env = cql"""
    typeside Ty = literal {
        types Str
    }

    schema A = literal : Ty {
        entities X
        attributes name : X -> Str
    }

    schema B = literal : Ty {
        entities Y
        attributes label : Y -> Str
    }

    schema_colimit C = quotient A + B : Ty {
        entity_equations
            A.X = B.Y
    }

    schema Combined = getSchema C
    mapping MA = getMapping C A
    mapping MB = getMapping C B
    """

    combined = env.Combined
    @test length(combined.ens) == 1  # X and Y merged into one
    @test length(combined.atts) == 2  # A_name and B_label

    ma = env.MA
    @test length(ma.ens) == 1
    mb = env.MB
    @test length(mb.ens) == 1
    # Both map to the same canonical entity
    @test first(values(ma.ens)) == first(values(mb.ens))
end

@testset "Colimit with sigma" begin
    env = cql"""
    typeside Ty = literal {
        types Str
        constants hello world : Str
    }

    schema S1 = literal : Ty {
        entities E1
        attributes a1 : E1 -> Str
    }

    schema S2 = literal : Ty {
        entities E2
        attributes a2 : E2 -> Str
    }

    schema_colimit C = quotient S1 + S2 : Ty {
        entity_equations
            S1.E1 = S2.E2
    }

    schema Combined = getSchema C
    mapping M1 = getMapping C S1
    mapping M2 = getMapping C S2

    instance I1 = literal : S1 {
        generators g1 : E1
        equations a1(g1) = hello
    }

    instance I2 = literal : S2 {
        generators g2 : E2
        equations a2(g2) = world
    }

    instance J1 = sigma M1 I1
    instance J2 = sigma M2 I2
    """

    j1 = env.J1
    j2 = env.J2
    # Each sigma'd instance should have 1 entity element
    canonical_en = first(env.Combined.ens)
    @test length(carrier(j1.algebra, canonical_en)) == 1
    @test length(carrier(j2.algebra, canonical_en)) == 1
end

end
