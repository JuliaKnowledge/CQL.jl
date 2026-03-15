using Documenter
using CQL

makedocs(;
    sitename = "CQL.jl",
    authors = "Simon Frost",
    modules = [CQL],
    format = Documenter.HTML(;
        prettyurls = get(ENV, "CI", nothing) == "true",
        canonical = "https://JuliaKnowledge.github.io/CQL.jl",
    ),
    pages = [
        "Home" => "index.md",
        "Tutorial" => "tutorial.md",
        "Vignettes" => "vignettes.md",
        "API Reference" => [
            "Core Types" => "api/types.md",
            "Parsing & Evaluation" => "api/evaluation.md",
            "Data Migration" => "api/migration.md",
            "Queries" => "api/queries.md",
            "Utilities" => "api/utilities.md",
        ],
    ],
    warnonly = [:missing_docs],
)

deploydocs(;
    repo = "github.com/JuliaKnowledge/CQL.jl.git",
    devbranch = "main",
    push_preview = true,
)
