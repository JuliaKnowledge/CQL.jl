using CQL

const EXAMPLES_DIR = joinpath(@__DIR__, "examples")

function run_java_examples()
    files = sort(filter(f -> endswith(f, ".cql"), readdir(EXAMPLES_DIR)))
    total = length(files)
    println("Running $total Java CQL examples...\n")

    passed = 0
    failed = 0
    errors = Dict{String,String}()

    for f in files
        name = f[1:end-4]
        path = joinpath(EXAMPLES_DIR, f)
        print("  $name... ")
        flush(stdout)

        try
            t1 = time()
            run_program(read(path, String))
            t2 = time()
            println("PASS ($(round(t2-t1, digits=2))s)")
            passed += 1
        catch e
            msg = sprint(showerror, e; context=:limit=>true)
            if length(msg) > 200
                msg = msg[1:200] * "..."
            end
            println("FAIL: $msg")
            errors[name] = msg
            failed += 1
        end
        flush(stdout)
    end

    println("\n" * "="^60)
    println("Results: $passed passed, $failed failed (of $total)")
    println("="^60)

    if !isempty(errors)
        ext_types = String[]
        parse_errors = String[]
        eval_errors = String[]
        unsupported_decl = String[]
        other = String[]

        for (name, msg) in sort(collect(errors))
            if occursin("external_types", msg)
                push!(ext_types, name)
            elseif occursin("Expected declaration", msg)
                push!(unsupported_decl, name)
            elseif occursin("Parse error", msg)
                push!(parse_errors, name)
            elseif occursin("Error evaluating", msg)
                push!(eval_errors, name)
            else
                push!(other, name)
            end
        end

        println("\nFailure breakdown:")
        if !isempty(ext_types)
            println("  external_types (Java interop, expected) [$(length(ext_types))]: $(join(ext_types, ", "))")
        end
        if !isempty(unsupported_decl)
            println("  Unsupported declarations [$(length(unsupported_decl))]: $(join(unsupported_decl, ", "))")
        end
        if !isempty(parse_errors)
            println("  Parse errors [$(length(parse_errors))]:")
            for name in parse_errors
                println("    $name: $(errors[name])")
            end
        end
        if !isempty(eval_errors)
            println("  Eval errors [$(length(eval_errors))]:")
            for name in eval_errors
                println("    $name: $(errors[name])")
            end
        end
        if !isempty(other)
            println("  Other [$(length(other))]:")
            for name in other
                println("    $name: $(errors[name])")
            end
        end
    end
end

run_java_examples()
