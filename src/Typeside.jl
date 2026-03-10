"""
Typesides: type systems with equational theories.

A typeside defines the types (e.g., String, Int) and function symbols
(e.g., plus : Int, Int -> Int) available, along with equations between terms.
"""

"""A CQL typeside."""
struct Typeside
    tys::Set{Symbol}
    syms::Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}  # sym -> ([arg types], ret type)
    eqs::Set{Tuple{Dict{Symbol,Symbol}, Equation}}      # (var->type ctx, equation)
    eq::Function  # (ctx::Dict{Symbol,Symbol}, eq::Equation) -> Bool
    java_fns::Dict{Symbol, Function}       # sym -> Julia evaluator function
    java_parsers::Dict{Symbol, Function}   # type -> string parser function
end

function Base.:(==)(a::Typeside, b::Typeside)
    a.tys == b.tys && a.syms == b.syms && a.eqs == b.eqs
end

function Base.show(io::IO, ts::Typeside)
    println(io, "typeside {")
    println(io, "  types")
    for ty in ts.tys
        println(io, "    ", ty)
    end
    println(io, "  functions")
    for (s, (args, ret)) in ts.syms
        println(io, "    ", s, " : ", join(args, ", "), " -> ", ret)
    end
    println(io, "  equations")
    for (ctx, eq) in ts.eqs
        ctx_str = join(["$v : $t" for (v, t) in ctx], ", ")
        println(io, "    forall ", ctx_str, " . ", eq)
    end
    println(io, "}")
end

"""Convert a typeside to a collage for type-checking."""
function typeside_to_collage(ts::Typeside)::Collage
    ceqs = Set{Tuple{Ctx, Equation}}()
    for (ctx, eq) in ts.eqs
        # Convert ctx from Dict{Symbol,Symbol} to Ctx (Dict{Symbol, Either})
        new_ctx = Ctx(v => Left(ty) for (v, ty) in ctx)
        push!(ceqs, (new_ctx, eq))
    end
    Collage(ceqs, ts.tys, Set{Symbol}(), ts.syms,
            Dict{Symbol,Tuple{Symbol,Symbol}}(),
            Dict{Symbol,Tuple{Symbol,Symbol}}(),
            Dict{Symbol,Symbol}(),
            Dict{Symbol,Symbol}())
end

"""Typecheck a typeside."""
function typecheck_typeside(ts::Typeside)
    typecheck_collage(typeside_to_collage(ts))
end

# ============================================================================
# Standard typesides
# ============================================================================

"""The initial (empty) typeside."""
function initial_typeside()
    Typeside(
        Set{Symbol}(),
        Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}(),
        Set{Tuple{Dict{Symbol,Symbol}, Equation}}(),
        (ctx, eq) -> error("Impossible: initial typeside has no equations"),
        Dict{Symbol, Function}(),
        Dict{Symbol, Function}(),
    )
end

"""RDF typeside with a single type Dom."""
function rdf_typeside()
    Typeside(
        Set{Symbol}([:Dom]),
        Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}(),
        Set{Tuple{Dict{Symbol,Symbol}, Equation}}(),
        (ctx, eq) -> eq.lhs == eq.rhs,
        Dict{Symbol, Function}(),
        Dict{Symbol, Function}(:Dom => identity),
    )
end

"""SQL typeside with standard SQL type names."""
function sql_typeside()
    sql_types = Set{Symbol}([
        :Bigint, :Binary, :Bit, :Blob, :Bool, :Boolean,
        :Char, :Clob, :Custom,
        :Date, :Decimal, :Dom, :Double, :Doubleprecision,
        :Float,
        :Int, :Integer,
        :Longvarbinary, :Longvarchar,
        :Numeric, :Nvarchar,
        :Other,
        :Real,
        :Smallint, :String,
        :Text, :Time, :Timestamp, :Tinyint,
        :Varbinary, :Varchar,
    ])
    Typeside(
        sql_types,
        Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}(),
        Set{Tuple{Dict{Symbol,Symbol}, Equation}}(),
        (ctx, eq) -> eq.lhs == eq.rhs,
        Dict{Symbol, Function}(),
        Dict{Symbol, Function}(),
    )
end

# ============================================================================
# Raw typeside evaluation
# ============================================================================

"""Raw typeside data from parsing."""
struct TypesideRaw
    tys::Vector{String}
    syms::Vector{Tuple{String, Tuple{Vector{String}, String}}}
    eqs::Vector{Tuple{Vector{Tuple{String, Union{Nothing,String}}}, RawTerm, RawTerm}}
    options::Vector{Tuple{String, String}}
    imports::Vector{Any}  # TypesideExp references
    ext_fns::Vector{Tuple{String, Tuple{Vector{String}, String}, String}}  # (name, sig, js_code)
    ext_parsers::Vector{Tuple{String, String}}  # (type_name, js_code)
end

"""Evaluate a raw typeside into a Typeside."""
function eval_typeside_raw(opts::CQLOptions, raw::TypesideRaw, imports::Vector{Typeside}=Typeside[])
    # Merge imports
    imported_tys = Set{Symbol}()
    imported_syms = Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}()
    imported_eqs = Set{Tuple{Dict{Symbol,Symbol}, Equation}}()
    for imp in imports
        union!(imported_tys, imp.tys)
        merge!(imported_syms, imp.syms)
        union!(imported_eqs, imp.eqs)
    end

    tys = union(imported_tys, Set{Symbol}(Symbol(t) for t in raw.tys))
    syms = copy(imported_syms)
    for (name, (arg_tys, ret_ty)) in raw.syms
        syms[Symbol(name)] = (Symbol.(arg_tys), Symbol(ret_ty))
    end

    eqs = copy(imported_eqs)
    for (ctx_raw, lhs_raw, rhs_raw) in raw.eqs
        ctx = Dict{Symbol,Symbol}()
        for (v, t) in ctx_raw
            if t !== nothing
                ctx[Symbol(v)] = Symbol(t)
            else
                # Type inference needed - try to infer from term usage
                inferred = _infer_var_type(v, syms, lhs_raw, rhs_raw)
                ctx[Symbol(v)] = inferred
            end
        end
        lhs = _eval_ts_term(syms, ctx, lhs_raw)
        rhs = _eval_ts_term(syms, ctx, rhs_raw)
        push!(eqs, (ctx, Equation(lhs, rhs)))
    end

    ts_no_prover = Typeside(tys, syms, eqs,
        (ctx, eq) -> error("Prover not yet initialized"),
        Dict{Symbol, Function}(), Dict{Symbol, Function}())

    # Create prover
    local_opts = isempty(raw.options) ? opts : to_options(opts, raw.options)
    col = typeside_to_collage(ts_no_prover)
    prover = create_prover(col, local_opts)

    eq_fn = (ctx, eq) -> begin
        new_ctx = Ctx(v => Left(ty) for (v, ty) in ctx)
        prover(new_ctx, eq)
    end

    # Build external function evaluators and parsers
    java_fns = Dict{Symbol, Function}()
    # Merge imported java_fns
    for imp in imports
        merge!(java_fns, imp.java_fns)
    end
    for (name, sig, code) in raw.ext_fns
        fn = _compile_js_function(name, sig, code)
        if fn !== nothing
            java_fns[Symbol(name)] = fn
        end
    end

    java_parsers = Dict{Symbol, Function}()
    for imp in imports
        merge!(java_parsers, imp.java_parsers)
    end
    for (ty_name, code) in raw.ext_parsers
        parser = _compile_js_parser(ty_name, code)
        if parser !== nothing
            java_parsers[Symbol(ty_name)] = parser
        end
    end

    Typeside(tys, syms, eqs, eq_fn, java_fns, java_parsers)
end

"""Evaluate a raw term in the typeside context."""
function _eval_ts_term(syms::Dict, ctx::Dict, raw::RawTerm)::CQLTerm
    if isempty(raw.args) && haskey(ctx, Symbol(raw.head))
        return CQLVar(Symbol(raw.head))
    end
    CQLSym(Symbol(raw.head), CQLTerm[_eval_ts_term(syms, ctx, a) for a in raw.args])
end

"""Infer variable type from usage in terms."""
function _infer_var_type(var::String, syms::Dict, lhs::RawTerm, rhs::RawTerm)::Symbol
    types_l = _types_of_var(var, syms, lhs)
    types_r = _types_of_var(var, syms, rhs)
    all_types = unique(vcat(types_l, types_r))
    length(all_types) == 1 || throw(CQLException("Ambiguous or conflicting types for variable $var"))
    all_types[1]
end

function _types_of_var(var::String, syms::Dict, t::RawTerm)::Vector{Symbol}
    result = Symbol[]
    if !isempty(t.args) && haskey(syms, Symbol(t.head))
        (arg_tys, _) = syms[Symbol(t.head)]
        for (a, ty) in zip(t.args, arg_tys)
            if a.head == var && isempty(a.args)
                push!(result, ty)
            else
                append!(result, _types_of_var(var, syms, a))
            end
        end
    end
    result
end

# ============================================================================
# JavaScript-to-Julia function compilation
# ============================================================================

"""Compile a JavaScript lambda into a Julia function.
Handles common patterns from CQL external_functions."""
function _compile_js_function(name::String, sig::Tuple{Vector{String}, String},
                               code::String)::Union{Function, Nothing}
    (arg_types, ret_type) = sig
    nargs = length(arg_types)
    code = strip(code)

    # Pattern: "(x, y) => x + y" or "x => x + 1" or "() => value"
    m = match(r"^\(?\s*([\w,\s]*?)\s*\)?\s*=>\s*(.+)$"s, code)
    m === nothing && return nothing

    params_str = strip(m[1])
    body = strip(m[2])
    params = isempty(params_str) ? String[] : [strip(p) for p in split(params_str, ",")]

    # Try exact pattern matches first (fast path)
    fn = _try_exact_js_pattern(body, params, ret_type)
    fn !== nothing && return fn

    # Try generic JS expression compilation
    fn = _compile_js_expr(body, params, ret_type)
    fn !== nothing && return fn

    # Zero-arg constant
    if nargs == 0
        val = _try_parse_js_constant(body)
        val !== nothing && return (args...) -> val
    end

    nothing
end

"""Try exact pattern matching for common JS function bodies."""
function _try_exact_js_pattern(body::AbstractString, params::Vector,
                                ret_type::AbstractString)::Union{Function, Nothing}
    # Arithmetic with coercion prefix
    if body == "0.0 + x + y" || body == "0 + x + y"
        return (args...) -> args[1] + args[2]
    # String methods
    elseif body == "x.toUpperCase()" || body == "x.toUpperCase"
        return (args...) -> uppercase(string(args[1]))
    elseif body == "x.toLowerCase()" || body == "x.toLowerCase"
        return (args...) -> lowercase(string(args[1]))
    elseif body == "x.length" || body == "x.length()"
        return (args...) -> length(string(args[1]))
    elseif body == "x.concat(y)" || body == "x + \"\" + y"
        return (args...) -> string(args[1]) * string(args[2])
    elseif body == "x.toString()" || body == "x.toString"
        return (args...) -> string(args[1])
    elseif body == "\"\" + x"
        return (args...) -> string(args[1])
    elseif body == "x.trim()"
        return (args...) -> strip(string(args[1]))
    elseif body == "x.add(y)"
        return (args...) -> args[1] + args[2]
    # Optional/Nullable
    elseif (occursin("Optional.empty()", body) || body == "null") && !occursin("parseInt", body) && !occursin("parseDouble", body)
        return (args...) -> nothing
    elseif occursin("Optional.of(x)", body)
        return (args...) -> args[1]
    # Optional toUpperCase pattern (Demo)
    elseif occursin("isPresent", body) && occursin("toUpperCase", body)
        return (args...) -> uppercase(string(args[1]))
    # parseInt / parseFloat
    elseif occursin("parseInt", body)
        return (args...) -> _safe_parse_int(args[1])
    elseif occursin("parseFloat", body) || occursin("Double.parseDouble", body)
        return (args...) -> _safe_parse_float(args[1])
    end
    nothing
end

"""Compile a JS expression body into a Julia function using a mini-evaluator.
Handles arithmetic expressions with constants and variables."""
function _compile_js_expr(body::AbstractString, params::Vector,
                           ret_type::AbstractString)::Union{Function, Nothing}
    # Strip outer parentheses
    stripped = _strip_parens(String(body))
    # Build parameter index map
    param_idx = Dict(String(p) => i for (i, p) in enumerate(params))
    # Try to compile the expression tree
    expr = _parse_js_expr(stripped, param_idx)
    expr === nothing && return nothing
    return (args...) -> _eval_js_expr(expr, args)
end

# Mini AST for JS expressions
struct JsConst; val::Any; end
struct JsParam; idx::Int; end
struct JsBinOp; op::Symbol; left::Any; right::Any; end
struct JsUnaryOp; op::Symbol; arg::Any; end
struct JsTernary; cond::Any; iftrue::Any; iffalse::Any; end

"""Strip balanced outer parentheses."""
function _strip_parens(s::AbstractString)::String
    s = strip(s)
    while startswith(s, "(") && endswith(s, ")")
        # Check if the parens are actually balanced around the whole expression
        depth = 0
        balanced = true
        for (i, c) in enumerate(s)
            c == '(' && (depth += 1)
            c == ')' && (depth -= 1)
            if depth == 0 && i < length(s)
                balanced = false
                break
            end
        end
        balanced || break
        s = strip(s[2:end-1])
    end
    s
end

"""Parse a JS expression into a mini AST."""
function _parse_js_expr(s::AbstractString, params::Dict{String,Int})
    s = strip(s)
    isempty(s) && return nothing

    # Try ternary: cond ? a : b (lowest precedence)
    result = _try_parse_ternary(s, params)
    result !== nothing && return result

    # Try comparison operators: ==, !=, <, <=, >, >=
    result = _try_parse_comparison(s, params)
    result !== nothing && return result

    # Try boolean: &&, ||
    result = _try_parse_boolean(s, params)
    result !== nothing && return result

    # Try additive: +, -
    result = _try_parse_additive(s, params)
    result !== nothing && return result

    # Try multiplicative: *, /
    result = _try_parse_multiplicative(s, params)
    result !== nothing && return result

    # Try power: ^, **
    result = _try_parse_power(s, params)
    result !== nothing && return result

    # Unary: -, !
    if startswith(s, "-")
        inner = _parse_js_expr(s[2:end], params)
        inner !== nothing && return JsUnaryOp(:neg, inner)
    elseif startswith(s, "!")
        inner = _parse_js_expr(s[2:end], params)
        inner !== nothing && return JsUnaryOp(:not, inner)
    end

    # Parenthesized expression
    if startswith(s, "(") && endswith(s, ")")
        inner = _strip_parens(s)
        inner != s && return _parse_js_expr(inner, params)
    end

    # Variable reference
    haskey(params, s) && return JsParam(params[s])

    # Boolean constants
    s == "true" && return JsConst(true)
    s == "false" && return JsConst(false)

    # Numeric constant
    n = tryparse(Float64, s)
    if n !== nothing
        return JsConst(n == floor(n) && !occursin(".", s) ? Int(n) : n)
    end

    # String constant
    if startswith(s, "\"") && endswith(s, "\"")
        return JsConst(s[2:end-1])
    end

    nothing
end

"""Find the position of a binary operator at the top level (not inside parens)."""
function _find_top_level_op(s::AbstractString, ops::Vector{String})::Union{Tuple{Int,String}, Nothing}
    depth = 0
    # Scan right-to-left for left-associative operators
    i = length(s)
    while i >= 1
        c = s[i]
        c == ')' && (depth += 1)
        c == '(' && (depth -= 1)
        if depth == 0
            for op in ops
                oplen = length(op)
                if i >= oplen && s[i-oplen+1:i] == op
                    # Don't match ** as * at position i-1
                    if op == "*" && i < length(s) && s[i+1] == '*'
                        continue
                    end
                    # Don't match != or <= or >= partially
                    if op in ("+", "-") && i > 1 && s[i-1] in ('=', '<', '>', '!')
                        continue
                    end
                    return (i - oplen + 1, op)
                end
            end
        end
        i -= 1
    end
    nothing
end

function _try_parse_binary(s::AbstractString, params::Dict{String,Int},
                            ops::Vector{String}, sym_map::Dict{String,Symbol})
    result = _find_top_level_op(s, ops)
    result === nothing && return nothing
    (pos, op) = result
    left_str = strip(s[1:pos-1])
    right_str = strip(s[pos+length(op):end])
    isempty(left_str) && return nothing
    isempty(right_str) && return nothing
    left = _parse_js_expr(left_str, params)
    right = _parse_js_expr(right_str, params)
    (left === nothing || right === nothing) && return nothing
    JsBinOp(sym_map[op], left, right)
end

function _try_parse_ternary(s::AbstractString, params::Dict{String,Int})
    depth = 0
    q_pos = 0
    for (i, c) in enumerate(s)
        c == '(' && (depth += 1)
        c == ')' && (depth -= 1)
        if depth == 0 && c == '?'
            q_pos = i
            break
        end
    end
    q_pos == 0 && return nothing
    # Find matching :
    depth = 0
    for i in (q_pos+1):length(s)
        c = s[i]
        c == '(' && (depth += 1)
        c == ')' && (depth -= 1)
        if depth == 0 && c == ':'
            cond = _parse_js_expr(strip(s[1:q_pos-1]), params)
            iftrue = _parse_js_expr(strip(s[q_pos+1:i-1]), params)
            iffalse = _parse_js_expr(strip(s[i+1:end]), params)
            (cond === nothing || iftrue === nothing || iffalse === nothing) && return nothing
            return JsTernary(cond, iftrue, iffalse)
        end
    end
    nothing
end

function _try_parse_comparison(s, params)
    _try_parse_binary(s, params, ["===", "!==", "==", "!=", "<=", ">=", "<", ">"],
        Dict("===" => :eq, "!==" => :ne, "==" => :eq, "!=" => :ne,
             "<=" => :le, ">=" => :ge, "<" => :lt, ">" => :gt))
end
function _try_parse_boolean(s, params)
    _try_parse_binary(s, params, ["&&", "||"],
        Dict("&&" => :and, "||" => :or))
end
function _try_parse_additive(s, params)
    _try_parse_binary(s, params, ["+", "-"],
        Dict("+" => :add, "-" => :sub))
end
function _try_parse_multiplicative(s, params)
    _try_parse_binary(s, params, ["*", "/"],
        Dict("*" => :mul, "/" => :div))
end
function _try_parse_power(s, params)
    # Right-to-left for power
    result = _find_top_level_op(s, ["**", "^"])
    result === nothing && return nothing
    (pos, op) = result
    left_str = strip(s[1:pos-1])
    right_str = strip(s[pos+length(op):end])
    (isempty(left_str) || isempty(right_str)) && return nothing
    left = _parse_js_expr(left_str, params)
    right = _parse_js_expr(right_str, params)
    (left === nothing || right === nothing) && return nothing
    JsBinOp(:pow, left, right)
end

"""Evaluate a JS expression AST with given argument values."""
function _eval_js_expr(expr, args)
    if expr isa JsConst
        return expr.val
    elseif expr isa JsParam
        return args[expr.idx]
    elseif expr isa JsUnaryOp
        v = _eval_js_expr(expr.arg, args)
        expr.op == :neg && return -v
        expr.op == :not && return !v
    elseif expr isa JsBinOp
        l = _eval_js_expr(expr.left, args)
        r = _eval_js_expr(expr.right, args)
        expr.op == :add && return l + r
        expr.op == :sub && return l - r
        expr.op == :mul && return l * r
        expr.op == :div && return r == 0 ? nothing : l / r
        expr.op == :pow && return l ^ r
        expr.op == :eq && return l == r
        expr.op == :ne && return l != r
        expr.op == :lt && return l < r
        expr.op == :le && return l <= r
        expr.op == :gt && return l > r
        expr.op == :ge && return l >= r
        expr.op == :and && return l && r
        expr.op == :or && return l || r
    elseif expr isa JsTernary
        c = _eval_js_expr(expr.cond, args)
        return c ? _eval_js_expr(expr.iftrue, args) : _eval_js_expr(expr.iffalse, args)
    end
    error("Unknown JS expression node: $expr")
end

"""Compile a JavaScript parser into a Julia function."""
function _compile_js_parser(ty_name::String, code::String)::Union{Function, Nothing}
    code = strip(code)
    # "x => x" — identity parser (strings stay as strings)
    if code == "x => x"
        return s -> s
    # "parseInt" or "x => parseInt(x)"
    elseif code == "parseInt" || occursin("parseInt", code)
        return s -> _safe_parse_int(s)
    # "x => java.lang.Double.parseDouble(x)" or "parseFloat" or "new java.lang.Double(x)"
    elseif occursin("parseDouble", code) || occursin("parseFloat", code) ||
           occursin("new java.lang.Double", code) || occursin("BigDecimal", code)
        return s -> _safe_parse_float(s)
    # Boolean parsers
    elseif occursin("Boolean", code) || occursin("parseBool", code)
        return s -> lowercase(string(s)) in ("true", "1")
    # Optional parsers
    elseif occursin("Optional.of", code) && occursin("parseInt", code)
        return s -> _safe_parse_int(s)
    end
    nothing
end

function _safe_parse_int(s)::Union{Int, Nothing}
    s isa Number && return Int(s)
    n = tryparse(Int, string(s))
    n !== nothing && return n
    f = tryparse(Float64, string(s))
    f !== nothing && return Int(round(f))
    nothing
end

function _safe_parse_float(s)::Union{Float64, Nothing}
    s isa Number && return Float64(s)
    tryparse(Float64, string(s))
end

function _try_parse_js_constant(body::String)
    body == "true" && return true
    body == "false" && return false
    body == "0" && return 0
    body == "0.0" && return 0.0
    body == "\"\"" && return ""
    n = tryparse(Float64, body)
    n !== nothing && return n
    nothing
end

"""Try to evaluate a CQLSym using typeside external functions.
Returns a CQLTerm (reduced) or nothing if evaluation not possible."""
function try_eval_typeside_sym(ts::Typeside, t::CQLSym)::Union{CQLTerm, Nothing}
    haskey(ts.java_fns, t.sym) || return nothing
    fn = ts.java_fns[t.sym]

    # Extract concrete values from args
    arg_vals = Any[]
    for a in t.args
        v = _extract_concrete_value(a, ts)
        v === nothing && return nothing
        push!(arg_vals, v)
    end

    # Evaluate
    result = try
        fn(arg_vals...)
    catch
        return nothing
    end
    result === nothing && return nothing

    # Get return type
    ret_type = haskey(ts.syms, t.sym) ? ts.syms[t.sym][2] : :String

    # Convert result back to CQLTerm
    _value_to_term(result, ret_type)
end

"""Extract a concrete Julia value from a CQLTerm, or nothing if symbolic."""
function _extract_concrete_value(t::CQLTerm, ts::Typeside)
    if t isa CQLSk
        s = string(t.sk)
        # Try parsing as a number
        n = tryparse(Float64, s)
        n !== nothing && return (n == floor(n) ? Int(n) : n)
        # It's a string literal
        return s
    elseif t isa CQLSym
        if isempty(t.args)
            s = string(t.sym)
            # Check boolean constants
            s == "true" && return true
            s == "false" && return false
            # Try number
            n = tryparse(Float64, s)
            n !== nothing && return (n == floor(n) ? Int(n) : n)
            # It's a string/symbol constant
            return s
        else
            # Recursively evaluate
            result = try_eval_typeside_sym(ts, t)
            result === nothing && return nothing
            return _extract_concrete_value(result, ts)
        end
    end
    nothing
end

"""Convert a Julia value back to a CQLTerm."""
function _value_to_term(val, ret_type::Symbol)::CQLTerm
    if val isa Bool
        sym = val ? Symbol("true") : Symbol("false")
        return CQLSym(sym, CQLTerm[])
    elseif val isa Number
        # Format based on the declared return type
        if ret_type in (:Double, :Float, :Real, :Doubleprecision, :Decimal)
            # Java uses "10.0" format for doubles
            f = Float64(val)
            s = f == floor(f) ? string(Int(floor(f))) * ".0" : string(f)
            return CQLSk(Symbol(s))
        else
            # Integer types: use plain integer format
            if val isa AbstractFloat && val == floor(val)
                return CQLSk(Symbol(string(Int(floor(val)))))
            end
            return CQLSk(Symbol(string(val)))
        end
    elseif val isa AbstractString
        return CQLSk(Symbol(val))
    elseif val === nothing
        return CQLSym(:null, CQLTerm[])
    else
        return CQLSk(Symbol(string(val)))
    end
end

# ============================================================================
# Expression types
# ============================================================================

abstract type TypesideExp end

struct TypesideVar <: TypesideExp
    name::String
end

struct TypesideInitial <: TypesideExp end

struct TypesideSql <: TypesideExp end

struct TypesideRdf <: TypesideExp end

struct TypesideRawExp <: TypesideExp
    raw::TypesideRaw
end

"""Extract typeside from a schema: typesideOf S"""
struct TypesideOf <: TypesideExp
    schema::Any  # SchemaExp
end

function deps(e::TypesideExp)::Vector{Tuple{String,Kind}}
    if e isa TypesideVar
        [(e.name, TYPESIDE)]
    elseif e isa TypesideInitial || e isa TypesideSql || e isa TypesideRdf
        Tuple{String,Kind}[]
    elseif e isa TypesideRawExp
        vcat([deps(i) for i in e.raw.imports]...)
    elseif e isa TypesideOf
        e.schema isa SchemaExp ? deps(e.schema) : Tuple{String,Kind}[]
    else
        Tuple{String,Kind}[]
    end
end

function get_options_exp(e::TypesideExp)
    if e isa TypesideRawExp
        e.raw.options
    else
        Tuple{String,String}[]
    end
end
