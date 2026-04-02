using Test
using CQL

@testset "Options" begin
    @testset "Unknown options warn" begin
        empty!(CQL.WARNED_UNKNOWN_OPTIONS)
        @test_logs (:warn, r"Unrecognized CQL option: totally_unknown_option") CQL.to_options(
            default_options(),
            [("totally_unknown_option", "x"), ("totally_unknown_option", "y")],
        )
    end

    @testset "Recognized passthrough options stay quiet" begin
        logger = Test.TestLogger(min_level=Base.CoreLogging.Warn)
        Base.CoreLogging.with_logger(logger) do
            CQL.to_options(default_options(), [("simplify_names", "true")])
        end
        @test isempty(logger.logs)
    end
end
