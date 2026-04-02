using Test
using CQL

@testset "Query" begin
    @testset "Identity query" begin
        ts_raw = CQL.TypesideRaw(["string"], [], [], [], [], [], [])
        ts = CQL.eval_typeside_raw(default_options(), ts_raw)
        sch_raw = CQL.SchemaRaw(
            nothing,
            ["E"],
            [("f", ("E", "E"))],
            [("a", ("E", "string"))],
            [], [], [], [],
        )
        sch = CQL.eval_schema_raw(default_options(), ts, sch_raw)

        q = CQL.identity_query(sch)
        @test q.src === sch
        @test q.dst === sch
        @test haskey(q.ens, :E)
        @test haskey(q.fks, :f)
        @test haskey(q.atts, :a)
    end

    @testset "Unsupported rext attribute case fails explicitly" begin
        src = """
        typeside T = literal {
            types String
            constants Alice : String
        }

        schema A = literal : T {
            entities Person
            attributes name : Person -> String
        }

        schema B = literal : T {
            entities PersonB
        }

        schema C = literal : T {
            entities PersonC
            attributes display : PersonC -> String
        }

        query Q1 = literal : A -> B {
            entity PersonB -> {
                from p:Person
            }
        }

        query Q2 = literal : A -> C {
            entity PersonC -> {
                from p:Person
                attributes
                    display -> name(p)
            }
        }

        query QR = rext Q1 Q2
        """

        err = try
            run_program(src)
            nothing
        catch e
            e
        end
        @test err isa CQLException
        @test occursin("rext with attributes for non-identity Q1 is not yet supported",
                       sprint(showerror, err))
    end
end
