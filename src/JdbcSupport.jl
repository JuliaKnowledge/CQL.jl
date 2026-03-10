"""
JDBC support for CQL.jl via JDBC.jl/JavaCall.jl.

Provides exec_jdbc, import_jdbc, and export_jdbc_instance functionality.
"""

# ============================================================================
# JVM initialization
# ============================================================================

const _jvm_initialized = Ref(false)

"""Initialize the JVM with JDBC drivers on the classpath."""
function _ensure_jvm!(classpaths::Vector{String}=String[])
    _jvm_initialized[] && return
    # Set JAVA_HOME if not already set or pointing to a valid JDK
    if !haskey(ENV, "JAVA_HOME") || !isfile(joinpath(ENV["JAVA_HOME"], "lib", "server", "libjvm.dylib"))
        candidates = String[]
        # Homebrew on macOS (ARM64 and Intel)
        for brew_prefix in ["/opt/homebrew", "/usr/local"]
            push!(candidates, joinpath(brew_prefix, "opt", "openjdk@11", "libexec", "openjdk.jdk", "Contents", "Home"))
            push!(candidates, joinpath(brew_prefix, "opt", "openjdk", "libexec", "openjdk.jdk", "Contents", "Home"))
        end
        # Standard Linux locations
        for d in ["/usr/lib/jvm", "/usr/java"]
            isdir(d) && for entry in readdir(d; join=true)
                isdir(entry) && push!(candidates, entry)
            end
        end
        for candidate in candidates
            if isdir(candidate)
                ENV["JAVA_HOME"] = candidate
                break
            end
        end
    end
    ENV["JULIA_COPY_STACKS"] = "yes"
    # Find H2 jar in common locations
    for cp in classpaths
        isfile(cp) && JavaCall.addClassPath(cp)
    end
    # Try standard locations for H2 and Derby via CQL_JDBC_CLASSPATH env var
    if haskey(ENV, "CQL_JDBC_CLASSPATH")
        for cp in split(ENV["CQL_JDBC_CLASSPATH"], ':')
            p = abspath(strip(cp))
            isfile(p) && JavaCall.addClassPath(p)
        end
    end
    JavaCall.init()
    _jvm_initialized[] = true
end

# ============================================================================
# Connection management
# ============================================================================

"""Resolve a JDBC connection string, using jdbc_default_string if empty."""
function _resolve_jdbc_conn(conn::String, opts::CQLOptions)::String
    s = strip(conn, '"')
    if isempty(s)
        s = get_str(opts, JDBC_DEFAULT_STRING)
    end
    isempty(s) && throw(CQLException(
        "JDBC connection string is empty and no jdbc_default_string option set"))
    s
end

# ============================================================================
# exec_jdbc: execute raw SQL statements
# ============================================================================

"""Execute SQL statements against a JDBC database."""
function eval_exec_jdbc(conn::String, sqls::Vector{String}, opts::CQLOptions)
    _ensure_jvm!()
    jdbc_url = _resolve_jdbc_conn(conn, opts)
    jconn = JDBC.DriverManager.getConnection(jdbc_url)
    try
        stmt = JDBC.createStatement(jconn)
        try
            for sql in sqls
                trimmed = strip(sql)
                isempty(trimmed) && continue
                try
                    JDBC.execute(stmt, trimmed)
                catch e
                    @warn "JDBC exec_jdbc SQL error" sql=trimmed exception=e
                end
            end
        finally
            close(stmt)
        end
    finally
        close(jconn)
    end
end

# ============================================================================
# export_jdbc_instance: export CQL instance to SQL tables
# ============================================================================

"""Export a CQL instance to SQL tables via JDBC."""
function eval_export_jdbc(inst::CQLInstance, conn::String, prefix::String,
                          opts::CQLOptions)
    _ensure_jvm!()
    jdbc_url = _resolve_jdbc_conn(conn, opts)
    tick = get_str(opts, JDBC_QUOTE_CHAR)
    start_id = get_int(opts, START_IDS_AT)
    varchar_len = get_int(opts, VARCHAR_LENGTH)

    sch = inst.schema
    alg = inst.algebra

    jconn = JDBC.DriverManager.getConnection(jdbc_url)
    try
        stmt = JDBC.createStatement(jconn)
        try
            for en in sch.ens
                tbl_name = "$(tick)$(prefix)$(en)$(tick)"

                # Drop table if exists
                try
                    JDBC.executeUpdate(stmt, "DROP TABLE IF EXISTS $tbl_name")
                catch; end

                # Build CREATE TABLE
                cols = String[]
                # Foreign key columns
                for fk_name in keys(sch.fks)
                    src_en, tgt_en = sch.fks[fk_name]
                    src_en == en || continue
                    col_name = _jdbc_display_name(fk_name)
                    push!(cols, "$(tick)$(col_name)$(tick) INTEGER")
                end
                # Attribute columns
                for att_name in keys(sch.atts)
                    att_en, att_ty = sch.atts[att_name]
                    att_en == en || continue
                    col_name = _jdbc_display_name(att_name)
                    sql_type = _cql_type_to_sql(att_ty, varchar_len)
                    push!(cols, "$(tick)$(col_name)$(tick) $(sql_type)")
                end

                if isempty(cols)
                    create_sql = "CREATE TABLE $tbl_name ($(tick)id$(tick) INTEGER)"
                else
                    create_sql = "CREATE TABLE $tbl_name ($(join(cols, ", ")))"
                end
                JDBC.executeUpdate(stmt, create_sql)

                # INSERT rows — iterate carrier elements for this entity
                elements = collect(carrier(alg, en))
                # Assign integer IDs to carrier elements
                elem_ids = Dict{Any, Int}()
                for (i, x) in enumerate(elements)
                    elem_ids[x] = start_id + i - 1
                end

                for x in elements
                    col_names = String[]
                    values = String[]

                    for fk_name in keys(sch.fks)
                        src_en, tgt_en = sch.fks[fk_name]
                        src_en == en || continue
                        col_name = _jdbc_display_name(fk_name)
                        push!(col_names, "$(tick)$(col_name)$(tick)")
                        tgt_x = eval_fk(alg, fk_name, x)
                        tgt_id = get(elem_ids, tgt_x, 0)
                        push!(values, string(tgt_id))
                    end

                    for att_name in keys(sch.atts)
                        att_en, att_ty = sch.atts[att_name]
                        att_en == en || continue
                        col_name = _jdbc_display_name(att_name)
                        push!(col_names, "$(tick)$(col_name)$(tick)")
                        val = eval_att(alg, att_name, x)
                        push!(values, _term_to_sql_value(val))
                    end

                    if !isempty(col_names)
                        insert_sql = "INSERT INTO $tbl_name ($(join(col_names, ", "))) VALUES ($(join(values, ", ")))"
                        JDBC.executeUpdate(stmt, insert_sql)
                    end
                end
            end
        finally
            close(stmt)
        end
    finally
        close(jconn)
    end
end

# ============================================================================
# import_jdbc: import SQL query results as CQL instance
# ============================================================================

"""Import a CQL instance from JDBC query results."""
function eval_import_jdbc(env::Env, e::InstanceImportJdbc)::CQLInstance
    _ensure_jvm!()

    local_opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
    conn_str = _resolve_jdbc_conn(e.conn, local_opts)
    prepend = get_bool(local_opts, PREPEND_ENTITY_ON_IDS)

    # Try to resolve schema; if it's the built-in 'sql' typeside, auto-discover
    sch = try
        eval_schema(env, e.schema)
    catch
        # Auto-discover schema from SQL queries using sql typeside
        ts = if e.schema isa SchemaVar && haskey(env.typesides, e.schema.name)
            env.typesides[e.schema.name]
        else
            sql_typeside()
        end
        _discover_jdbc_schema(ts, e.entity_sql, conn_str)
    end

    # Build entity -> SQL query mapping
    entity_sql = Dict{Symbol, String}()
    for (en_str, sql) in e.entity_sql
        entity_sql[Symbol(en_str)] = sql
    end

    # Default: SELECT * FROM entity_name for unmapped entities
    for en in sch.ens
        if !haskey(entity_sql, en)
            entity_sql[en] = "SELECT * FROM $(en)"
        end
    end

    gens = Dict{Symbol, Symbol}()
    eqs = Set{Equation}()
    gen_counter = Ref(0)

    # Track gen names per entity for FK resolution
    entity_gens = Dict{Symbol, Vector{Tuple{Symbol, Dict{String,String}}}}()

    jconn = JDBC.DriverManager.getConnection(conn_str)
    try
        stmt = JDBC.createStatement(jconn)
        try
            for en in sch.ens
                sql = get(entity_sql, en, nothing)
                sql === nothing && continue

                entity_gens[en] = Tuple{Symbol, Dict{String,String}}[]

                rs = JDBC.executeQuery(stmt, sql)
                md = JDBC.getMetaData(rs)
                ncols = JDBC.getColumnCount(md)

                # Get column names and types
                col_names = String[]
                col_types = Int[]
                for i in 1:ncols
                    push!(col_names, JDBC.getColumnName(md, i))
                    push!(col_types, JDBC.getColumnType(md, i))
                end

                while JavaCall.jcall(rs, "next", JavaCall.jboolean, ()) != 0
                    gen_id = gen_counter[]
                    gen_counter[] += 1
                    gen_sym = if prepend
                        Symbol(en, "_", gen_id)
                    else
                        Symbol(gen_id)
                    end
                    gens[gen_sym] = en

                    # Read all column values (normalize keys to lowercase for matching)
                    row_data = Dict{String, String}()
                    for i in 1:ncols
                        val = JDBC.getString(rs, i)
                        if JDBC.wasNull(rs)
                            # NULL → empty string (matches Java CQL behavior)
                            row_data[lowercase(col_names[i])] = ""
                        else
                            # Normalize boolean values to lowercase only for BOOLEAN columns
                            if col_types[i] in (16, -7)  # BOOLEAN, BIT
                                if val == "TRUE"
                                    val = "true"
                                elseif val == "FALSE"
                                    val = "false"
                                end
                            end
                            row_data[lowercase(col_names[i])] = val
                        end
                    end

                    push!(entity_gens[en], (gen_sym, row_data))

                    # Create attribute equations
                    for att_name in keys(sch.atts)
                        att_en, att_ty = sch.atts[att_name]
                        att_en == en || continue
                        col = lowercase(_jdbc_display_name(att_name))
                        val = get(row_data, col, nothing)
                        val === nothing && continue
                        push!(eqs, Equation(
                            CQLAtt(att_name, CQLGen(gen_sym)),
                            CQLSym(Symbol(val), CQLTerm[])))
                    end
                end
                close(rs)
            end

            # Resolve foreign key equations
            for en in sch.ens
                haskey(entity_gens, en) || continue
                for (gen_sym, row_data) in entity_gens[en]
                    for fk_name in keys(sch.fks)
                        src_en, tgt_en = sch.fks[fk_name]
                        src_en == en || continue
                        col = lowercase(_jdbc_display_name(fk_name))
                        val = get(row_data, col, nothing)
                        val === nothing && continue
                        # Find target generator by matching ID
                        tgt_gen = _find_gen_by_id(entity_gens, tgt_en, val, prepend)
                        if tgt_gen !== nothing
                            push!(eqs, Equation(
                                CQLFk(fk_name, CQLGen(gen_sym)),
                                CQLGen(tgt_gen)))
                        end
                    end
                end
            end

        finally
            close(stmt)
        end
    finally
        close(jconn)
    end

    pres = Presentation(gens, Dict{Symbol,Symbol}(), eqs)
    saturated_instance(sch, pres)
end

# ============================================================================
# import_jdbc_direct: auto-generate SQL from schema entities
# ============================================================================

"""Import JDBC direct: for each entity in schema, generate SELECT query and import."""
function eval_import_jdbc_direct(env::Env, e::InstanceImportJdbcDirect)::CQLInstance
    _ensure_jvm!()

    sch = eval_schema(env, e.schema)

    # import_jdbc_direct requires no FKs in the schema
    if !isempty(sch.fks)
        throw(CQLException("import_jdbc_direct: schema must have no foreign keys"))
    end

    # Get options from environment
    local_opts = env.options
    qu = get_str(local_opts, JDBC_QUOTE_CHAR)
    jdbc_zero = "(SELECT '0' AS CQL_ZERO) AS CQL_ZERO"

    # Generate entity -> SQL mappings
    entity_sql = Tuple{String,String}[]
    for en in sort(collect(sch.ens))
        en_str = string(en)
        # Get attributes for this entity
        att_names = String[]
        for (att_name, (att_en, _)) in sch.atts
            att_en == en || continue
            push!(att_names, _jdbc_display_name(att_name))
        end

        # Build SELECT clause
        z = if isempty(att_names)
            " $(e.rowid) AS CQL_ROW_ID "
        else
            join([qu * a * qu for a in att_names], ", ") * ", $(e.rowid) AS CQL_ROW_ID "
        end

        # Handle dotted entity names (SCHEMA.TABLE)
        parts = split(en_str, ".")
        quoted_parts = [qu * p * qu for p in parts]
        table_ref = join(quoted_parts, ".")

        query = "SELECT $z FROM $table_ref, $jdbc_zero"
        push!(entity_sql, (en_str, query))
    end

    # Build a synthetic InstanceImportJdbc and evaluate it
    # Use a non-existent schema name so eval_import_jdbc falls back to auto-discovery
    # from the sql typeside (matching Java's TyExpSch(schema) pattern)
    opts = [("id_column_name", "CQL_ROW_ID")]
    synth = InstanceImportJdbc(e.conn, e.schema, entity_sql, opts)
    eval_import_jdbc(env, synth)
end

"""Auto-discover a schema from JDBC query metadata."""
function _discover_jdbc_schema(ts::Typeside, entity_sqls::Vector{Tuple{String,String}},
                               conn_str::String)::CQLSchema
    _ensure_jvm!()
    ens = Set{Symbol}()
    fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    atts = Dict{Symbol, Tuple{Symbol, Symbol}}()

    default_type = :Varchar in ts.tys ? :Varchar :
                   :String in ts.tys ? :String :
                   :Dom in ts.tys ? :Dom : first(ts.tys)

    jconn = JDBC.DriverManager.getConnection(conn_str)
    try
        stmt = JDBC.createStatement(jconn)
        try
            for (en_str, sql) in entity_sqls
                en = Symbol(en_str)
                push!(ens, en)
                rs = JDBC.executeQuery(stmt, sql)
                md = JDBC.getMetaData(rs)
                ncols = JDBC.getColumnCount(md)
                for i in 1:ncols
                    col_name = JDBC.getColumnName(md, i)
                    att_key = Symbol(en, "__", col_name)
                    col_type = JDBC.getColumnType(md, i)
                    cql_ty = _sql_type_to_cql(col_type, ts)
                    atts[att_key] = (en, cql_ty)
                end
                close(rs)
            end
        finally
            close(stmt)
        end
    finally
        close(jconn)
    end

    att_by_name = Dict{Symbol, Vector{Symbol}}()
    for att_name in keys(atts)
        plain = Symbol(split(string(att_name), "__"; limit=2)[end])
        push!(get!(att_by_name, plain, Symbol[]), att_name)
    end

    CQLSchema(ts, ens, fks, atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(),
        (en, eq) -> eq.lhs == eq.rhs,
        Dict{Symbol,Vector{Symbol}}(), att_by_name, collect(keys(fks)))
end

"""Map JDBC SQL type code to CQL type symbol."""
function _sql_type_to_cql(sql_type::Integer, ts::Typeside)::Symbol
    if sql_type in (4, -5, 5, -6)  # INTEGER, BIGINT, SMALLINT, TINYINT
        :Integer in ts.tys ? :Integer : :Varchar
    elseif sql_type in (8, 6, 7, 2, 3)  # DOUBLE, FLOAT, REAL, NUMERIC, DECIMAL
        :Float in ts.tys ? :Float : :Varchar
    elseif sql_type in (16, -7)  # BOOLEAN, BIT
        :Boolean in ts.tys ? :Boolean : :Varchar
    else
        :Varchar in ts.tys ? :Varchar :
        :String in ts.tys ? :String : first(ts.tys)
    end
end

"""Find a generator by its source ID value across entity generators."""
function _find_gen_by_id(entity_gens::Dict, tgt_en::Symbol, id_val::String,
                         prepend::Bool)
    haskey(entity_gens, tgt_en) || return nothing
    for (gen_sym, row_data) in entity_gens[tgt_en]
        row_id = get(row_data, "id", nothing)
        if row_id !== nothing && row_id == id_val
            return gen_sym
        end
    end
    # Fallback: try matching by generator name suffix
    for (gen_sym, _) in entity_gens[tgt_en]
        s = string(gen_sym)
        if prepend
            parts = split(s, "_"; limit=2)
            length(parts) >= 2 && parts[2] == id_val && return gen_sym
        else
            s == id_val && return gen_sym
        end
    end
    nothing
end

# ============================================================================
# Helpers
# ============================================================================

"""Strip Entity__ prefix from a name for display/SQL column matching."""
function _jdbc_display_name(name::Symbol)::String
    s = string(name)
    idx = findfirst("__", s)
    idx === nothing ? s : s[last(idx)+1:end]
end

"""Convert a CQL type to SQL type string."""
function _cql_type_to_sql(ty::Symbol, varchar_len::Int)::String
    s = lowercase(string(ty))
    if s == "string" || s == "varchar" || s == "dom"
        "VARCHAR($varchar_len)"
    elseif s == "integer" || s == "int"
        "INTEGER"
    elseif s == "float" || s == "double" || s == "real"
        "DOUBLE"
    elseif s == "boolean" || s == "bool"
        "BOOLEAN"
    else
        "VARCHAR($varchar_len)"
    end
end

"""Convert a CQL term to a SQL value string for INSERT."""
function _term_to_sql_value(t::CQLTerm)::String
    if t isa CQLSym
        s = string(t.sym)
        # Escape single quotes
        s = replace(s, "'" => "''")
        "'$s'"
    elseif t isa CQLSk
        s = string(t.sk)
        s = replace(s, "'" => "''")
        "'$s'"
    else
        s = string(t)
        s = replace(s, "'" => "''")
        "'$s'"
    end
end

# ============================================================================
# import_jdbc_all: discover schema from JDBC metadata
# ============================================================================

"""Discover a schema from all tables in a JDBC database."""
function eval_schema_import_jdbc_all(env::Env, e::SchemaImportJdbcAll)::CQLSchema
    _ensure_jvm!()

    # Check allow_sql_import_all_unsafe option
    local_opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
    allow = get_bool(local_opts, ALLOW_SQL_IMPORT_ALL_UNSAFE)
    if !allow
        throw(CQLException(
            "import_jdbc_all is best-effort only and unsound. " *
            "Set allow_sql_import_all_unsafe=true to continue."))
    end

    conn_str = _resolve_jdbc_conn(e.connection, local_opts)
    ts = sql_typeside()

    ens = Set{Symbol}()
    fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    atts = Dict{Symbol, Tuple{Symbol, Symbol}}()

    # System schemas to skip (matching Java CQL behavior)
    skip_schemas = Set(["system", "sys", "ctxsys", "mdsys", "xdb"])

    jconn = JDBC.DriverManager.getConnection(conn_str)
    try
        stmt = JDBC.createStatement(jconn)
        try
            # Discover tables using INFORMATION_SCHEMA
            rs = JDBC.executeQuery(stmt, """
                SELECT TABLE_SCHEMA, TABLE_NAME
                FROM INFORMATION_SCHEMA.TABLES
                WHERE TABLE_TYPE = 'TABLE' OR TABLE_TYPE = 'BASE TABLE'
                ORDER BY TABLE_SCHEMA, TABLE_NAME
            """)
            tables = Tuple{String,String}[]
            while JavaCall.jcall(rs, "next", JavaCall.jboolean, ()) != 0
                table_schema = JDBC.getString(rs, 1)
                table_name = JDBC.getString(rs, 2)
                push!(tables, (table_schema, table_name))
            end
            close(rs)

            for (table_schema, table_name) in tables
                ls = lowercase(table_schema)
                ls in skip_schemas && continue

                # Entity name: SCHEMA.TABLE (if schema != dbo), or just TABLE
                en_name = if lowercase(table_schema) == "dbo"
                    table_name
                else
                    "$(table_schema).$(table_name)"
                end
                en = Symbol(en_name)
                push!(ens, en)

                # Discover columns for this table
                cols_rs = JDBC.executeQuery(stmt, """
                    SELECT COLUMN_NAME, DATA_TYPE
                    FROM INFORMATION_SCHEMA.COLUMNS
                    WHERE TABLE_SCHEMA = '$(table_schema)' AND TABLE_NAME = '$(table_name)'
                    ORDER BY ORDINAL_POSITION
                """)
                while JavaCall.jcall(cols_rs, "next", JavaCall.jboolean, ()) != 0
                    col_name = JDBC.getString(cols_rs, 1)
                    type_name = JDBC.getString(cols_rs, 2)
                    cql_ty = _sql_typename_to_cql(type_name, ts)
                    att_key = Symbol(en, "__", col_name)
                    atts[att_key] = (en, cql_ty)
                end
                close(cols_rs)
            end
        finally
            close(stmt)
        end
    finally
        close(jconn)
    end

    att_by_name = Dict{Symbol, Vector{Symbol}}()
    for att_name in keys(atts)
        plain = Symbol(split(string(att_name), "__"; limit=2)[end])
        push!(get!(att_by_name, plain, Symbol[]), att_name)
    end

    CQLSchema(ts, ens, fks, atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(),
        (en, eq) -> eq.lhs == eq.rhs,
        Dict{Symbol,Vector{Symbol}}(), att_by_name, collect(keys(fks)))
end

"""Map SQL type name string to CQL type (matching Java's sqlTypeToAqlType)."""
function _sql_typename_to_cql(type_name::String, ts::Typeside)::Symbol
    x = lowercase(strip(type_name))
    # Handle multi-word type names that map to standard types
    if x == "character varying"
        return :Varchar in ts.tys ? :Varchar : :Other
    elseif x == "character large object"
        return :Clob in ts.tys ? :Clob : :Other
    elseif x == "binary large object"
        return :Blob in ts.tys ? :Blob : :Other
    elseif x == "double precision"
        return :Doubleprecision in ts.tys ? :Doubleprecision : :Double in ts.tys ? :Double : :Other
    elseif x == "time with time zone" || x == "timestamp with time zone"
        return :Timestamp in ts.tys ? :Timestamp : :Other
    end
    # Capitalize first letter
    y = uppercase(x[1:1]) * x[2:end]
    sym = Symbol(y)
    if sym in ts.tys
        return sym
    end
    :Other
end
