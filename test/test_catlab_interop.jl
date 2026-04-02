using Test
using CQL
using Catlab

@testset "Catlab Interop" begin
    @testset "Schema conversion" begin
        ts_raw = CQL.TypesideRaw(["string", "Integer", "Boolean"], [], [], [], [], [], [])
        ts = CQL.eval_typeside_raw(default_options(), ts_raw)
        sch_raw = CQL.SchemaRaw(
            nothing,
            ["Person", "Dept"],
            [("worksIn", ("Person", "Dept"))],
            [("name", ("Person", "string")), ("age", ("Person", "Integer")), ("active", ("Person", "Boolean"))],
            [], [], [], [],
        )
        sch = CQL.eval_schema_raw(default_options(), ts, sch_raw)

        catlab_info = CQL.cql_schema_to_catlab(sch)
        @test catlab_info.schema isa BasicSchema
        @test catlab_info.type_assignment[:string] === String
        @test catlab_info.type_assignment[:Integer] === Int
        @test catlab_info.type_assignment[:Boolean] === Bool
    end

    @testset "Instance conversion preserves scalar values" begin
        env = cql"""
        typeside Ty = literal {
            types String Integer Boolean
            constants Alice : String
            constants 42 : Integer
            constants true : Boolean
        }

        schema S = literal : Ty {
            entities Person
            attributes
                name : Person -> String
                age : Person -> Integer
                active : Person -> Boolean
        }

        instance I = literal : S {
            generators p : Person
            equations
                name(p) = Alice
                age(p) = 42
                active(p) = true
        }
        """

        acs = CQL.cql_instance_to_acset(env.I)
        @test acs[1, :name] === "Alice"
        @test acs[1, :age] === 42
        @test acs[1, :active] === true
    end
end
