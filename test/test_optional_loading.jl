using Test
using CQL

@testset "Optional integrations load lazily" begin
    @test !isdefined(CQL, :JavaCall)
    @test !isdefined(CQL, :JDBC)
    @test !isdefined(CQL, :ODBC)
end
