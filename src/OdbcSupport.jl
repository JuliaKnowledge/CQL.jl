"""
ODBC support for CQL.jl via ODBC.jl.

Provides exec_odbc, import_odbc, import_odbc_direct, export_odbc_instance,
and import_odbc_all functionality, mirroring the JDBC API.

Note: ODBC.jl must be configured with the correct driver manager before use.
On macOS, call `ODBC.setunixODBC()` if using unixODBC-based drivers (e.g., MariaDB).
"""

const _odbc_initialized = Ref(false)

"""Initialize ODBC driver manager. On macOS, defaults to unixODBC for MariaDB compatibility."""
function _ensure_odbc!()
    _odbc_initialized[] && return
    _ensure_odbc_package_loaded!()
    @static if Sys.isapple()
        ODBC.setunixODBC()
    end
    _odbc_initialized[] = true
end

# ============================================================================
# Connection management
# ============================================================================

"""Resolve an ODBC connection string, using odbc_default_string option if empty."""
function _resolve_odbc_conn(conn::String, opts::CQLOptions)::String
    s = strip(conn, '"')
    if isempty(s)
        s = get_str(opts, JDBC_DEFAULT_STRING)  # reuse same option key
    end
    isempty(s) && throw(CQLException(
        "ODBC connection string is empty and no jdbc_default_string option set"))
    s
end

# ============================================================================
# exec_odbc: execute raw SQL statements
# ============================================================================

"""Execute SQL statements against an ODBC database."""
function eval_exec_odbc(conn::String, sqls::Vector{String}, opts::CQLOptions)
    _ensure_odbc!()
    conn_str = _resolve_odbc_conn(conn, opts)
    oconn = ODBC.Connection(conn_str)
    try
        for sql in sqls
            trimmed = strip(sql)
            isempty(trimmed) && continue
            try
                ODBC.DBInterface.execute(oconn, trimmed)
            catch e
                @warn "ODBC exec_odbc SQL error" sql=trimmed exception=e
            end
        end
    finally
        ODBC.disconnect!(oconn)
    end
end

# ============================================================================
# export_odbc_instance: export CQL instance to SQL tables
# ============================================================================

"""Export a CQL instance to SQL tables via ODBC."""
function eval_export_odbc(inst::CQLInstance, conn::String, prefix::String,
                          opts::CQLOptions)
    _ensure_odbc!()
    conn_str = _resolve_odbc_conn(conn, opts)
    tick = get_str(opts, JDBC_QUOTE_CHAR)
    start_id = get_int(opts, START_IDS_AT)
    varchar_len = get_int(opts, VARCHAR_LENGTH)

    sch = inst.schema
    alg = inst.algebra

    oconn = ODBC.Connection(conn_str)
    try
        for en in sch.ens
            tbl_name = "$(tick)$(prefix)$(en)$(tick)"

            # Drop table if exists
            try
                ODBC.DBInterface.execute(oconn, "DROP TABLE IF EXISTS $tbl_name")
            catch; end

            # Build CREATE TABLE
            cols = String[]
            for fk_name in keys(sch.fks)
                src_en, tgt_en = sch.fks[fk_name]
                src_en == en || continue
                col_name = _odbc_display_name(fk_name)
                push!(cols, "$(tick)$(col_name)$(tick) INTEGER")
            end
            for att_name in keys(sch.atts)
                att_en, att_ty = sch.atts[att_name]
                att_en == en || continue
                col_name = _odbc_display_name(att_name)
                sql_type = _cql_type_to_sql(att_ty, varchar_len)
                push!(cols, "$(tick)$(col_name)$(tick) $(sql_type)")
            end

            if isempty(cols)
                create_sql = "CREATE TABLE $tbl_name ($(tick)id$(tick) INTEGER)"
            else
                create_sql = "CREATE TABLE $tbl_name ($(join(cols, ", ")))"
            end
            ODBC.DBInterface.execute(oconn, create_sql)

            # INSERT rows
            elements = collect(carrier(alg, en))
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
                    col_name = _odbc_display_name(fk_name)
                    push!(col_names, "$(tick)$(col_name)$(tick)")
                    tgt_x = eval_fk(alg, fk_name, x)
                    tgt_id = get(elem_ids, tgt_x, 0)
                    push!(values, string(tgt_id))
                end

                for att_name in keys(sch.atts)
                    att_en, att_ty = sch.atts[att_name]
                    att_en == en || continue
                    col_name = _odbc_display_name(att_name)
                    push!(col_names, "$(tick)$(col_name)$(tick)")
                    val = eval_att(alg, att_name, x)
                    push!(values, _term_to_sql_value(val))
                end

                if !isempty(col_names)
                    insert_sql = "INSERT INTO $tbl_name ($(join(col_names, ", "))) VALUES ($(join(values, ", ")))"
                    ODBC.DBInterface.execute(oconn, insert_sql)
                end
            end
        end
    finally
        ODBC.disconnect!(oconn)
    end
end

# ============================================================================
# import_odbc: import SQL query results as CQL instance
# ============================================================================

"""Import a CQL instance from ODBC query results."""
function eval_import_odbc(env::Env, e::InstanceImportOdbc)::CQLInstance
    _ensure_odbc!()
    local_opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
    conn_str = _resolve_odbc_conn(e.conn, local_opts)
    prepend = get_bool(local_opts, PREPEND_ENTITY_ON_IDS)

    # Resolve schema; if not found, auto-discover from SQL queries
    sch = try
        eval_schema(env, e.schema)
    catch
        ts = if e.schema isa SchemaVar && haskey(env.typesides, e.schema.name)
            env.typesides[e.schema.name]
        else
            sql_typeside()
        end
        _discover_odbc_schema(ts, e.entity_sql, conn_str)
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

    oconn = ODBC.Connection(conn_str)
    try
        for en in sch.ens
            sql = get(entity_sql, en, nothing)
            sql === nothing && continue

            entity_gens[en] = Tuple{Symbol, Dict{String,String}}[]

            cursor = ODBC.DBInterface.execute(oconn, sql; iterate_rows=true)
            col_names = [string(nm) for nm in cursor.names]
            col_types = cursor.types

            for row in cursor
                gen_id = gen_counter[]
                gen_counter[] += 1
                gen_sym = if prepend
                    Symbol(en, "_", gen_id)
                else
                    Symbol(gen_id)
                end
                gens[gen_sym] = en

                # Read all column values
                row_data = Dict{String, String}()
                for (i, col_name) in enumerate(col_names)
                    raw_val = ODBC.Tables.getcolumn(row, i)
                    if raw_val === missing
                        row_data[lowercase(col_name)] = ""
                    else
                        val = string(raw_val)
                        # Normalize boolean values
                        if _is_bool_type(col_types[i])
                            if val == "TRUE" || val == "1"
                                val = "true"
                            elseif val == "FALSE" || val == "0"
                                val = "false"
                            end
                        end
                        row_data[lowercase(col_name)] = val
                    end
                end

                push!(entity_gens[en], (gen_sym, row_data))

                # Create attribute equations
                for att_name in keys(sch.atts)
                    att_en, att_ty = sch.atts[att_name]
                    att_en == en || continue
                    col = lowercase(_odbc_display_name(att_name))
                    val = get(row_data, col, nothing)
                    val === nothing && continue
                    push!(eqs, Equation(
                        CQLAtt(att_name, CQLGen(gen_sym)),
                        CQLSym(Symbol(val), CQLTerm[])))
                end
            end
        end

        # Resolve foreign key equations
        for en in sch.ens
            haskey(entity_gens, en) || continue
            for (gen_sym, row_data) in entity_gens[en]
                for fk_name in keys(sch.fks)
                    src_en, tgt_en = sch.fks[fk_name]
                    src_en == en || continue
                    col = lowercase(_odbc_display_name(fk_name))
                    val = get(row_data, col, nothing)
                    val === nothing && continue
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
        ODBC.disconnect!(oconn)
    end

    pres = Presentation(gens, Dict{Symbol,Symbol}(), eqs)
    saturated_instance(sch, pres)
end

# ============================================================================
# import_odbc_direct: auto-generate SQL from schema entities
# ============================================================================

"""Import ODBC direct: for each entity in schema, generate SELECT query and import."""
function eval_import_odbc_direct(env::Env, e::InstanceImportOdbcDirect)::CQLInstance
    sch = eval_schema(env, e.schema)

    if !isempty(sch.fks)
        throw(CQLException("import_odbc_direct: schema must have no foreign keys"))
    end

    local_opts = env.options
    qu = get_str(local_opts, JDBC_QUOTE_CHAR)

    # Generate entity -> SQL mappings
    entity_sql = Tuple{String,String}[]
    for en in sort(collect(sch.ens))
        en_str = string(en)
        att_names = String[]
        for (att_name, (att_en, _)) in sch.atts
            att_en == en || continue
            push!(att_names, _odbc_display_name(att_name))
        end

        z = if isempty(att_names)
            " $(e.rowid) AS CQL_ROW_ID "
        else
            join([qu * a * qu for a in att_names], ", ") * ", $(e.rowid) AS CQL_ROW_ID "
        end

        parts = split(en_str, ".")
        quoted_parts = [qu * p * qu for p in parts]
        table_ref = join(quoted_parts, ".")

        query = "SELECT $z FROM $table_ref"
        push!(entity_sql, (en_str, query))
    end

    opts = [("id_column_name", "CQL_ROW_ID")]
    synth = InstanceImportOdbc(e.conn, e.schema, entity_sql, opts)
    eval_import_odbc(env, synth)
end

# ============================================================================
# import_odbc_all: discover schema from ODBC metadata
# ============================================================================

"""Discover a schema from all tables in an ODBC database."""
function eval_schema_import_odbc_all(env::Env, e::SchemaImportOdbcAll)::CQLSchema
    _ensure_odbc!()
    local_opts = isempty(e.options) ? env.options : to_options(env.options, e.options)
    allow = get_bool(local_opts, ALLOW_SQL_IMPORT_ALL_UNSAFE)
    if !allow
        throw(CQLException(
            "import_odbc_all is best-effort only and unsound. " *
            "Set allow_sql_import_all_unsafe=true to continue."))
    end

    conn_str = _resolve_odbc_conn(e.connection, local_opts)
    ts = sql_typeside()

    ens = Set{Symbol}()
    fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    atts = Dict{Symbol, Tuple{Symbol, Symbol}}()

    skip_schemas = Set(["system", "sys", "ctxsys", "mdsys", "xdb",
                        "information_schema", "performance_schema", "mysql"])

    oconn = ODBC.Connection(conn_str)
    try
        # Discover tables using INFORMATION_SCHEMA
        cursor = ODBC.DBInterface.execute(oconn, """
            SELECT TABLE_SCHEMA, TABLE_NAME
            FROM INFORMATION_SCHEMA.TABLES
            WHERE TABLE_TYPE = 'BASE TABLE'
            ORDER BY TABLE_SCHEMA, TABLE_NAME
        """; iterate_rows=true)
        tables = Tuple{String,String}[]
        for row in cursor
            table_schema = string(ODBC.Tables.getcolumn(row, 1))
            table_name = string(ODBC.Tables.getcolumn(row, 2))
            push!(tables, (table_schema, table_name))
        end

        for (table_schema, table_name) in tables
            ls = lowercase(table_schema)
            ls in skip_schemas && continue

            en_name = table_name
            en = Symbol(en_name)
            push!(ens, en)

            # Discover columns
            cols_cursor = ODBC.DBInterface.execute(oconn, """
                SELECT COLUMN_NAME, DATA_TYPE
                FROM INFORMATION_SCHEMA.COLUMNS
                WHERE TABLE_SCHEMA = '$(table_schema)' AND TABLE_NAME = '$(table_name)'
                ORDER BY ORDINAL_POSITION
            """; iterate_rows=true)
            for col_row in cols_cursor
                col_name = string(ODBC.Tables.getcolumn(col_row, 1))
                type_name = string(ODBC.Tables.getcolumn(col_row, 2))
                cql_ty = _sql_typename_to_cql(type_name, ts)
                att_key = Symbol(en, "__", col_name)
                atts[att_key] = (en, cql_ty)
            end
        end
    finally
        ODBC.disconnect!(oconn)
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

# ============================================================================
# Helpers
# ============================================================================

"""Strip Entity__ prefix from a name for display/SQL column matching."""
function _odbc_display_name(name::Symbol)::String
    s = string(name)
    idx = findfirst("__", s)
    idx === nothing ? s : s[last(idx)+1:end]
end

"""Check if a Julia type represents a boolean SQL column."""
function _is_bool_type(T::Type)::Bool
    BT = T >: Missing ? Base.nonmissingtype(T) : T
    BT === Bool
end

"""Auto-discover a schema from ODBC query metadata."""
function _discover_odbc_schema(ts::Typeside, entity_sqls::Vector{Tuple{String,String}},
                               conn_str::String)::CQLSchema
    _ensure_odbc!()
    ens = Set{Symbol}()
    fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    atts = Dict{Symbol, Tuple{Symbol, Symbol}}()

    default_type = :Varchar in ts.tys ? :Varchar :
                   :String in ts.tys ? :String :
                   :Dom in ts.tys ? :Dom : first(ts.tys)

    oconn = ODBC.Connection(conn_str)
    try
        for (en_str, sql) in entity_sqls
            en = Symbol(en_str)
            push!(ens, en)
            cursor = ODBC.DBInterface.execute(oconn, sql; iterate_rows=true)
            for (i, col_sym) in enumerate(cursor.names)
                col_name = string(col_sym)
                att_key = Symbol(en, "__", col_name)
                cql_ty = _odbc_jltype_to_cql(cursor.types[i], ts)
                atts[att_key] = (en, cql_ty)
            end
        end
    finally
        ODBC.disconnect!(oconn)
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

"""Map a Julia type from ODBC cursor to CQL type symbol."""
function _odbc_jltype_to_cql(T::Type, ts::Typeside)::Symbol
    BT = T >: Missing ? Base.nonmissingtype(T) : T
    if BT <: Integer
        :Integer in ts.tys ? :Integer : :Varchar
    elseif BT <: AbstractFloat
        :Float in ts.tys ? :Float : :Varchar
    elseif BT === Bool
        :Boolean in ts.tys ? :Boolean : :Varchar
    else
        :Varchar in ts.tys ? :Varchar :
        :String in ts.tys ? :String : first(ts.tys)
    end
end
