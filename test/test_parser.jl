using Test
using CQL

@testset "Parser" begin
    @testset "Lexer basics" begin
        ps = CQL.ParseState("hello world")
        @test !CQL.at_end(ps)
        @test CQL.peek_char(ps) == 'h'
        CQL.advance!(ps)
        @test CQL.peek_char(ps) == 'e'
    end

    @testset "skip whitespace and comments" begin
        ps = CQL.ParseState("  // comment\nhello")
        CQL.skip_ws!(ps)
        @test CQL.peek_char(ps) == 'h'

        ps2 = CQL.ParseState("  /* block */ hello")
        CQL.skip_ws!(ps2)
        @test CQL.peek_char(ps2) == 'h'

        ps3 = CQL.ParseState("  (* block *) hello")
        CQL.skip_ws!(ps3)
        @test CQL.peek_char(ps3) == 'h'
    end

    @testset "read_identifier!" begin
        ps = CQL.ParseState("  foo bar")
        id = CQL.read_identifier!(ps)
        @test id == "foo"

        # Quoted identifier
        ps2 = CQL.ParseState("\"hello world\"")
        id2 = CQL.read_identifier!(ps2)
        @test id2 == "hello world"
    end

    @testset "expect! and try_expect!" begin
        ps = CQL.ParseState("hello world")
        CQL.expect!(ps, "hello")
        @test CQL.peek_char(ps) == 'w'

        @test CQL.try_expect!(ps, "world")
        @test CQL.at_end(ps)
    end

    @testset "Raw term parsing" begin
        ps = CQL.ParseState("f(x, y)")
        t = CQL.parse_raw_term!(ps)
        @test t.head == "f"
        @test length(t.args) == 2
        @test t.args[1].head == "x"
        @test t.args[2].head == "y"
    end

    @testset "Dot notation parsing" begin
        ps = CQL.ParseState("a.b.c ")
        t = CQL.parse_raw_term!(ps)
        # a.b.c => c(b(a))
        @test t.head == "c"
        @test length(t.args) == 1
        @test t.args[1].head == "b"
        @test t.args[1].args[1].head == "a"
    end

    @testset "Parse typeside expression" begin
        ps = CQL.ParseState("sql")
        e = CQL.parse_typeside_exp!(ps)
        @test e isa CQL.TypesideSql

        ps2 = CQL.ParseState("empty")
        e2 = CQL.parse_typeside_exp!(ps2)
        @test e2 isa CQL.TypesideInitial

        ps3 = CQL.ParseState("literal { types string nat }")
        e3 = CQL.parse_typeside_exp!(ps3)
        @test e3 isa CQL.TypesideRawExp
        @test length(e3.raw.tys) == 2
    end

    @testset "Parse schema expression" begin
        src = """literal : T {
            entities
                Employee
                Department
            foreign_keys
                manager : Employee -> Employee
            attributes
                name : Employee -> string
        }"""
        ps = CQL.ParseState(src)
        # Need T to be defined - use variable ref
        # Actually this will parse T as a TypesideVar
        e = CQL.parse_schema_exp!(ps)
        @test e isa CQL.SchemaRawExp
        @test length(e.raw.ens) == 2
        @test length(e.raw.fks) == 1
        @test length(e.raw.atts) == 1
    end

    @testset "Parse instance expression" begin
        src = """literal : S {
            generators
                a b : Employee
            equations
                a.manager = a
        }"""
        ps = CQL.ParseState(src)
        e = CQL.parse_instance_exp!(ps)
        @test e isa CQL.InstanceRawExp
        @test length(e.raw.gens) == 2
        @test length(e.raw.eqs) == 1
    end

    @testset "Parse mapping expression" begin
        ps = CQL.ParseState("identity S")
        e = CQL.parse_mapping_exp!(ps)
        @test e isa CQL.MappingId
    end
end
