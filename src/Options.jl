"""
CQL configuration options.
"""

@enum BoolOption begin
    REQUIRE_CONSISTENCY
    DONT_VALIDATE_UNSAFE
    PROGRAM_ALLOW_NONCONFLUENCE_UNSAFE
    INTERPRET_AS_ALGEBRA
    PROGRAM_ALLOW_NONTERMINATION_UNSAFE
    ALLOW_EMPTY_SORTS_UNSAFE
    PREPEND_ENTITY_ON_IDS
    ALLOW_SQL_IMPORT_ALL_UNSAFE
end

@enum StringOption begin
    PROVER
    COMPLETION_PRECEDENCE
    JDBC_DEFAULT_STRING
    JDBC_QUOTE_CHAR
    ID_COLUMN_NAME
end

@enum IntOption begin
    TIMEOUT
    START_IDS_AT
    VARCHAR_LENGTH
end

"""Default values for boolean options."""
const BOOL_DEFAULTS = Dict{BoolOption,Bool}(
    PROGRAM_ALLOW_NONTERMINATION_UNSAFE => false,
    ALLOW_EMPTY_SORTS_UNSAFE => false,
    PROGRAM_ALLOW_NONCONFLUENCE_UNSAFE => false,
    DONT_VALIDATE_UNSAFE => false,
    INTERPRET_AS_ALGEBRA => false,
    REQUIRE_CONSISTENCY => true,
    PREPEND_ENTITY_ON_IDS => true,
    ALLOW_SQL_IMPORT_ALL_UNSAFE => false,
)

"""Default values for integer options."""
const INT_DEFAULTS = Dict{IntOption,Int}(
    TIMEOUT => 30,
    START_IDS_AT => 0,
    VARCHAR_LENGTH => 64,
)

"""Default values for string options."""
const STRING_DEFAULTS = Dict{StringOption,String}(
    PROVER => "auto",
    COMPLETION_PRECEDENCE => "",
    JDBC_DEFAULT_STRING => "jdbc:h2:mem:db1;DB_CLOSE_DELAY=-1",
    JDBC_QUOTE_CHAR => "",
    ID_COLUMN_NAME => "id",
)

"""CQL options container."""
struct CQLOptions
    int_ops::Dict{IntOption,Int}
    bool_ops::Dict{BoolOption,Bool}
    str_ops::Dict{StringOption,String}
end

"""Create default options."""
function default_options()
    CQLOptions(
        copy(INT_DEFAULTS),
        copy(BOOL_DEFAULTS),
        copy(STRING_DEFAULTS),
    )
end

"""Get an integer option."""
get_int(opts::CQLOptions, o::IntOption) = get(opts.int_ops, o, INT_DEFAULTS[o])

"""Get a boolean option."""
get_bool(opts::CQLOptions, o::BoolOption) = get(opts.bool_ops, o, BOOL_DEFAULTS[o])

"""Get a string option."""
get_str(opts::CQLOptions, o::StringOption) = get(opts.str_ops, o, STRING_DEFAULTS[o])

# Maps from lowercase names to option enums
const BOOL_OPTION_NAMES = Dict{String,BoolOption}(
    lowercase(string(o)) => o for o in instances(BoolOption)
)
const INT_OPTION_NAMES = Dict{String,IntOption}(
    lowercase(string(o)) => o for o in instances(IntOption)
)
const STRING_OPTION_NAMES = Dict{String,StringOption}(
    lowercase(string(o)) => o for o in instances(StringOption)
)

"""Parse key-value option pairs into a CQLOptions, starting from base options."""
function to_options(base::CQLOptions, pairs::Vector{Tuple{String,String}})
    opts = CQLOptions(copy(base.int_ops), copy(base.bool_ops), copy(base.str_ops))
    for (k, v) in pairs
        kl = lowercase(k)
        if haskey(INT_OPTION_NAMES, kl)
            val = tryparse(Int, v)
            val === nothing && throw(CQLException("Not an int: $v"))
            opts.int_ops[INT_OPTION_NAMES[kl]] = val
        elseif haskey(BOOL_OPTION_NAMES, kl)
            if v == "true"
                opts.bool_ops[BOOL_OPTION_NAMES[kl]] = true
            elseif v == "false"
                opts.bool_ops[BOOL_OPTION_NAMES[kl]] = false
            else
                throw(CQLException("Not a bool: $v"))
            end
        elseif haskey(STRING_OPTION_NAMES, kl)
            opts.str_ops[STRING_OPTION_NAMES[kl]] = v
        else
            # Silently ignore unknown options (Java CQL has many IDE-specific options)
        end
    end
    opts
end

function to_options(base::CQLOptions, pairs::Vector{<:Pair{String,String}})
    to_options(base, [(k, v) for (k, v) in pairs])
end

function to_options(base::CQLOptions, pairs::AbstractVector)
    to_options(base, Tuple{String,String}[(string(k), string(v)) for (k, v) in pairs])
end
