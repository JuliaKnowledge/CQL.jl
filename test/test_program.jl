using Test
using CQL

@testset "Program" begin
    @testset "Parse simple program" begin
        src = """
        typeside T = literal {
            types
                string
        }

        schema S = literal : T {
            entities
                Person
            attributes
                name : Person -> string
        }

        instance I = literal : S {
            generators
                alice bob : Person
            equations
                name(alice) = name(bob)
        }
        """
        prog = CQL.parse_program(src)
        @test length(prog.exps) == 3
        @test prog.exps[1].kind == CQL.TYPESIDE
        @test prog.exps[1].name == "T"
        @test prog.exps[2].kind == CQL.SCHEMA
        @test prog.exps[2].name == "S"
        @test prog.exps[3].kind == CQL.INSTANCE
        @test prog.exps[3].name == "I"
    end

    @testset "Parse program with options" begin
        src = """
        options
            allow_empty_sorts_unsafe = true

        typeside T = sql
        """
        prog = CQL.parse_program(src)
        @test length(prog.options) == 1
        @test prog.options[1] == ("allow_empty_sorts_unsafe", "true")
        @test length(prog.exps) == 1
    end

    @testset "Duplicate detection" begin
        src = """
        typeside T = sql
        typeside T = empty
        """
        @test_throws CQLException CQL.parse_program(src)
    end

    @testset "Run simple program" begin
        src = """
        typeside T = literal {
            types
                string
        }

        schema S = literal : T {
            entities
                Person
            attributes
                name : Person -> string
        }

        instance I = literal : S {
            generators
                alice bob : Person
        }
        """
        env = run_program(src)
        @test haskey(env.typesides, "T")
        @test haskey(env.schemas, "S")
        @test haskey(env.instances, "I")
        @test :string in env.typesides["T"].tys
        @test :Person in env.schemas["S"].ens
        @test length(carrier(env.instances["I"].algebra, :Person)) == 2
    end

    @testset "Run with empty instance" begin
        src = """
        typeside T = literal {
            types
                string
        }
        schema S = literal : T {
            entities
                E
        }
        instance I = empty : S
        """
        env = run_program(src)
        @test haskey(env.instances, "I")
        @test isempty(carrier(env.instances["I"].algebra, :E))
    end
end
