# Dump CQL instance data in a deterministic, comparable format.
# Matches the output of CqlDump.java for cross-implementation comparison.
using CQL

function dump_instances(path::String)
    src = read(path, String)
    env = run_program(src)
    program = CQL.parse_program(src)

    # Extract raw generator order and detect interpret_as_algebra/frozen instances
    raw_gen_orders = Dict{String, Vector{Tuple{String,String}}}()
    use_gen_names = Set{String}()  # instances where FK targets use gen names
    frozen_instances = Set{String}()  # frozen instances use idN naming
    for decl in program.exps
        decl.kind == CQL.INSTANCE || continue
        if decl.body isa CQL.InstanceRawExp
            raw_gen_orders[decl.name] = decl.body.raw.gens
            # Check for interpret_as_algebra option
            for (k, v) in decl.body.raw.options
                if k == "interpret_as_algebra" && lowercase(v) == "true"
                    push!(use_gen_names, decl.name)
                end
            end
        elseif decl.body isa CQL.InstanceFrozen
            push!(use_gen_names, decl.name)
            push!(frozen_instances, decl.name)
        end
    end

    # Resolve imported gen orders: if an instance has imports but no own gens,
    # use the imported instance's generators
    for decl in program.exps
        decl.kind == CQL.INSTANCE || continue
        decl.body isa CQL.InstanceRawExp || continue
        gens = get(raw_gen_orders, decl.name, Tuple{String,String}[])
        if isempty(gens) && !isempty(decl.body.raw.imports)
            merged = Tuple{String,String}[]
            for imp in decl.body.raw.imports
                imp_name = imp isa String ? imp : hasproperty(imp, :name) ? imp.name : string(imp)
                append!(merged, get(raw_gen_orders, imp_name, Tuple{String,String}[]))
            end
            if !isempty(merged)
                raw_gen_orders[decl.name] = merged
            end
        end
    end

    # Propagate gen_order from source instances to derived instances
    # For chase, sigma, delta, quotient_query, distinct, coproduct:
    # use the source instance's gen_order to process generators in the right order
    for decl in program.exps
        decl.kind == CQL.INSTANCE || continue
        haskey(raw_gen_orders, decl.name) && continue  # already has raw gen_order
        body = decl.body
        src_name = nothing
        if hasproperty(body, :instance) && body.instance isa CQL.InstanceVar
            src_name = body.instance.name
        end
        if src_name !== nothing && haskey(raw_gen_orders, src_name)
            raw_gen_orders[decl.name] = raw_gen_orders[src_name]
        end
    end

    # Build global elem_index across all instances using Java-compatible ordering
    global_elem_index = Dict{Any, Int}()
    for decl in program.exps
        decl.kind == CQL.INSTANCE || continue
        haskey(env.instances, decl.name) || continue
        inst = env.instances[decl.name]
        gen_order = get(raw_gen_orders, decl.name, Tuple{String,String}[])
        # If no AST gen_order, use the engine's gen_order from Presentation
        if isempty(gen_order) && !isempty(inst.pres.gen_order)
            gen_order = [(string(g), string(inst.pres.gens[g])) for g in inst.pres.gen_order
                         if haskey(inst.pres.gens, g)]
        end
        idx = _java_elem_index(inst.algebra, inst.schema, gen_order)
        # Iterate in local index order (not Dict's arbitrary order)
        for (elem, _) in sort(collect(idx), by=x->x[2])
            if !haskey(global_elem_index, elem)
                global_elem_index[elem] = length(global_elem_index)
            end
        end
    end

    # Detect coproduct instances and build source element maps
    coprod_source_names = Dict{String, Vector{String}}()  # inst_name -> source instance names
    for decl in program.exps
        decl.kind == CQL.INSTANCE || continue
        if decl.body isa CQL.InstanceCoproduct
            src_names = String[]
            for inst_exp in decl.body.instances
                push!(src_names, hasproperty(inst_exp, :name) ? inst_exp.name : string(inst_exp))
            end
            coprod_source_names[decl.name] = src_names
        end
    end

    # Detect colimits with simplify_names=false → collect their entity sets
    # We'll match instances by checking if their schema entities == a no-simplify colimit's entities
    no_simplify_ent_sets = Set{Set{Symbol}}()
    for decl in program.exps
        decl.kind == CQL.SCHEMA_COLIMIT || continue
        is_no_simplify = false
        if hasproperty(decl.body, :options)
            for (k, v) in decl.body.options
                if k == "simplify_names" && lowercase(v) == "false"
                    is_no_simplify = true
                end
            end
        end
        if is_no_simplify && haskey(env.colimits, decl.name)
            colim_sch = env.colimits[decl.name].schema
            push!(no_simplify_ent_sets, Set(colim_sch.ens))
        end
    end

    for decl in program.exps
        decl.kind == CQL.INSTANCE || continue
        name = decl.name
        haskey(env.instances, name) || continue
        inst = env.instances[name]

        # Build query provenance if this is a query-derived instance
        query_prov = Dict{Symbol, Tuple{Symbol, Dict{Symbol, Any}}}()
        query_src_index = Dict{Any, Int}()
        query_src_coprod = Dict{Any, String}()  # coproduct provenance for source instance
        try
            if decl.body isa CQL.InstanceEval
                q = CQL.eval_query(env, decl.body.query)
                src_inst = CQL.eval_instance(env, decl.body.instance)
                query_prov = CQL.query_provenance(q, src_inst)
                # Build source-instance-local element index for provenance formatting
                src_name = decl.body.instance isa CQL.InstanceVar ? decl.body.instance.name : ""
                src_gen_order = get(raw_gen_orders, src_name, Tuple{String,String}[])
                query_src_index = _java_elem_index(src_inst.algebra, src_inst.schema, src_gen_order)
                # Build coproduct provenance for source instance if it's a coproduct
                if haskey(coprod_source_names, src_name)
                    csrc_names = coprod_source_names[src_name]
                    csrc_indices = Dict{Int, Dict{Any, Int}}()
                    for (k, sn) in enumerate(csrc_names)
                        if haskey(env.instances, sn)
                            csrc_inst = env.instances[sn]
                            csrc_go = get(raw_gen_orders, sn, Tuple{String,String}[])
                            csrc_indices[k] = _java_elem_index(csrc_inst.algebra, csrc_inst.schema, csrc_go)
                        end
                    end
                    for en in src_inst.schema.ens
                        for elem in get(src_inst.algebra.en, en, Set())
                            cprov = _coprod_provenance(elem, csrc_names, csrc_indices, env)
                            if cprov !== nothing
                                query_src_coprod[elem] = cprov
                            end
                        end
                    end
                end
            end
        catch
        end

        # Build coproduct element display map: elem -> "(SourceName, source_idx)"
        coprod_elem_display = Dict{Any, String}()
        if haskey(coprod_source_names, name)
            src_names = coprod_source_names[name]
            # Build element indices for each source instance
            src_indices = Dict{Int, Dict{Any, Int}}()
            for (k, sn) in enumerate(src_names)
                if haskey(env.instances, sn)
                    src_inst = env.instances[sn]
                    src_go = get(raw_gen_orders, sn, Tuple{String,String}[])
                    src_indices[k] = _java_elem_index(src_inst.algebra, src_inst.schema, src_go)
                end
            end
            # Map coproduct elements to (SourceName, source_idx)
            for en in inst.schema.ens
                for elem in get(inst.algebra.en, en, Set())
                    cprov = _coprod_provenance(elem, src_names, src_indices, env)
                    if cprov !== nothing
                        coprod_elem_display[elem] = cprov
                    end
                end
            end
        end

        println("INSTANCE $name")
        try
            gen_order = get(raw_gen_orders, name, Tuple{String,String}[])
            gen_names = name in use_gen_names
            is_frozen = name in frozen_instances
            # Check if this instance's schema matches a no-simplify colimit's entity set
            no_strip = Set(inst.schema.ens) in no_simplify_ent_sets
            dump_instance(inst, global_elem_index, gen_order, gen_names, query_prov, query_src_index;
                         is_frozen=is_frozen, coprod_elem_display=coprod_elem_display,
                         query_src_coprod=query_src_coprod, no_colimit_strip=no_strip)
        catch e
            println("  ERROR: $e")
        end
        println()
    end
end

"""Build Java-compatible element index via depth-first FK expansion from generators."""
function _java_elem_index(alg, sch, gen_order::Vector{Tuple{String,String}})::Dict{Any, Int}
    elem_index = Dict{Any, Int}()
    next_id = Ref(0)

    # Build FK-from-entity map using schema's FK declaration order
    fks_from = Dict{Symbol, Vector{Symbol}}()
    for en in sch.ens
        fks_from[en] = Symbol[]
    end
    for fk in sch.fk_order
        haskey(sch.fks, fk) || continue
        (src, _) = sch.fks[fk]
        push!(fks_from[src], fk)
    end

    function add!(en::Symbol, elem)
        haskey(elem_index, elem) && return
        elem_index[elem] = next_id[]
        next_id[] += 1
        # Depth-first: immediately expand FK targets
        for fk in get(fks_from, en, Symbol[])
            haskey(alg.fk, fk) || continue
            fk_map = alg.fk[fk]
            haskey(fk_map, elem) || continue
            target = fk_map[elem]
            tgt_en = sch.fks[fk][2]
            add!(tgt_en, target)
        end
    end

    # Process generators in declaration order
    for (gen_name, gen_en) in gen_order
        sym = Symbol(gen_name)
        en = Symbol(gen_en)
        haskey(alg.gen, sym) || continue
        add!(en, alg.gen[sym])
    end

    # Catch any remaining elements not reached via generators (e.g., from eval/delta/sigma)
    for en in sort(collect(sch.ens))
        for elem in sort(collect(get(alg.en, en, Set())), by=string)
            add!(en, elem)
        end
    end

    elem_index
end

"""Map a coproduct carrier element back to (SourceName, source_idx) string.
Coproduct elements have generators prefixed with iN_ (N = 1-based source index).
Strips prefix and evaluates FK chain through source algebra to find carrier element."""
function _coprod_provenance(elem, src_names::Vector{String},
                            src_indices::Dict{Int, Dict{Any, Int}},
                            env)::Union{String, Nothing}
    s = _elem_str(elem)
    m = match(r"^i(\d+)_(.+)$", s)
    m === nothing && return nothing
    k = parse(Int, m[1])
    (k < 1 || k > length(src_names)) && return nothing
    src_name = src_names[k]
    src_idx_map = get(src_indices, k, nothing)
    src_idx_map === nothing && return nothing
    orig_term = _parse_elem_term(m[2])
    # Try direct term lookup
    idx = get(src_idx_map, orig_term, nothing)
    if idx === nothing && haskey(env.instances, src_name)
        # Evaluate FK chain through source algebra to find normalized carrier
        carrier = _eval_fk_chain(orig_term, env.instances[src_name].algebra)
        carrier !== nothing && (idx = get(src_idx_map, carrier, nothing))
    end
    idx === nothing && return nothing
    return "($src_name, $idx)"
end

"""Evaluate a CQLGen/CQLFk term through an algebra's FK maps to get carrier element."""
function _eval_fk_chain(term, alg)
    if term isa CQL.CQLGen
        return get(alg.gen, term.gen, nothing)
    elseif term isa CQL.CQLFk
        inner = _eval_fk_chain(term.arg, alg)
        inner === nothing && return nothing
        fk_map = get(alg.fk, term.fk, nothing)
        fk_map === nothing && return nothing
        return get(fk_map, inner, nothing)
    else
        return nothing
    end
end

"""Get string representation of a carrier element for prefix matching."""
function _elem_str(elem)::String
    if elem isa CQL.CQLGen
        return string(elem.gen)
    elseif elem isa CQL.CQLFk
        return _elem_str(elem.arg) * "." * string(elem.fk)
    else
        return string(elem)
    end
end

"""Parse a dotted element string back into a CQLGen/CQLFk term."""
function _parse_elem_term(s::AbstractString)
    parts = split(s, '.')
    term = CQL.CQLGen(Symbol(parts[1]))
    for i in 2:length(parts)
        term = CQL.CQLFk(Symbol(parts[i]), term)
    end
    term
end

function dump_instance(inst::CQL.CQLInstance,
                       global_elem_index::Dict{Any, Int}=Dict{Any, Int}(),
                       gen_order::Vector{Tuple{String,String}}=Tuple{String,String}[],
                       use_gen_names::Bool=false,
                       query_prov::Dict{Symbol, Tuple{Symbol, Dict{Symbol, Any}}}=Dict{Symbol, Tuple{Symbol, Dict{Symbol, Any}}}(),
                       query_src_index::Dict{Any, Int}=Dict{Any, Int}();
                       is_frozen::Bool=false,
                       coprod_elem_display::Dict{Any, String}=Dict{Any, String}(),
                       query_src_coprod::Dict{Any, String}=Dict{Any, String}(),
                       no_colimit_strip::Bool=false)
    sch = inst.schema
    alg = inst.algebra

    # Types that have external parsers → get @Type annotation
    parsed_types = Set{Symbol}(keys(sch.typeside.java_parsers))

    # Build Java-compatible element index
    elem_index = _java_elem_index(alg, sch, gen_order)

    # Merge global elem_index for cross-instance Skolem resolution
    elem_index = merge(global_elem_index, elem_index)

    # Build reverse map: carrier elem → generator name (for frozen/interpret_as_algebra)
    gen_name_map = Dict{Any, Symbol}()
    if use_gen_names
        if is_frozen
            # Frozen instances: use idN naming for all elements (matching Java's convention)
            for (elem, idx) in sort(collect(elem_index), by=x->x[2])
                gen_name_map[elem] = Symbol("id", idx)
            end
        else
            for (gen, elem) in alg.gen
                gen_name_map[elem] = gen
            end
        end
    end

    # Build source element index for delta instances (Tuple carriers)
    delta_src_index = Dict{Any, Int}()
    _has_tuple_carriers = any(x isa Tuple{Symbol, Any} for xs in values(alg.en) for x in xs)
    if _has_tuple_carriers
        # Collect source elements per entity, index them
        src_by_en = Dict{Symbol, Vector{Any}}()
        for (en, xs) in alg.en
            for x in xs
                if x isa Tuple{Symbol, Any}
                    (_, src_elem) = x
                    src_en = x[1]
                    push!(get!(src_by_en, src_en, Any[]), src_elem)
                end
            end
        end
        # Index source elements within each entity
        for (en, elems) in src_by_en
            unique_elems = sort(unique(elems), by=e -> get(global_elem_index, e, 0))
            for (i, e) in enumerate(unique_elems)
                delta_src_index[e] = i - 1  # 0-based
            end
        end
    end

    for en in sort(collect(sch.ens))
        xs = get(alg.en, en, Set())
        println("  ENTITY $en ($(length(xs)) rows)")

        # Get FK and attribute names from schema, sorted together (like Java's TreeMap)
        fk_names = Set([fk for (fk, (src, _)) in sch.fks if src == en])
        att_names_set = Set([att for (att, (src, _)) in sch.atts if src == en])
        all_col_syms = collect(union(fk_names, att_names_set))

        # Build display names: strip colimit entity prefix (e.g., Olog1Schema_Patient_ID → ID)
        # Uses greedy assignment: first (alphabetically) gets simple name, duplicates keep full name
        col_display = _build_col_display_names(all_col_syms, en; no_colimit_strip=no_colimit_strip)

        # Sort by display name to match Java's TreeMap ordering
        all_col_names = sort(all_col_syms, by=x -> col_display[x])

        rows = String[]
        for x in xs
            parts = String[]
            for col in all_col_names
                display = col_display[col]
                if col in fk_names
                    target = alg.fk[col][x]
                    # Tuple carriers = delta instance: format as (entity, idx)
                    if target isa Tuple{Symbol, Any}
                        (t_en, t_elem) = target
                        # Use source-instance-local index for the target element
                        t_idx = get(delta_src_index, t_elem, nothing)
                        if t_idx !== nothing
                            val_str = "($t_en, $t_idx)"
                        else
                            val_str = "($t_en, $t_elem)"
                        end
                    # Symbol carriers = interpret_as_algebra: use name directly
                    elseif target isa Symbol
                        # Check for query provenance
                        if !isempty(query_prov) && haskey(query_prov, target)
                            prov_idx = isempty(query_src_index) ? elem_index : query_src_index
                            val_str = _format_query_prov(query_prov[target][2], prov_idx;
                                                         coprod_elem_display=query_src_coprod)
                        else
                            val_str = string(target)
                        end
                    elseif use_gen_names && haskey(gen_name_map, target)
                        val_str = string(gen_name_map[target])
                    elseif !isempty(coprod_elem_display) && haskey(coprod_elem_display, target)
                        val_str = coprod_elem_display[target]
                    else
                        idx = get(elem_index, target, nothing)
                        val_str = idx !== nothing ? string(idx) : format_term(target, elem_index)
                    end
                    push!(parts, "$display=$val_str")
                else
                    val = alg.nf_y(CQL.Right((x, col)))
                    val_orig = val
                    # Try evaluating typeside functions
                    val = CQL.eval_typeside_term(sch.typeside, val)
                    tgt_type = sch.atts[col][2]
                    push!(parts, "$display=$(format_att_val(val, tgt_type, elem_index, parsed_types, gen_name_map; parent_elem=x, parent_att=col, coprod_elem_display=coprod_elem_display))")
                end
            end
            push!(rows, join(parts, ", "))
        end
        sort!(rows)
        for row in rows
            println("    $row")
        end
    end
end

"""Format query provenance tuple as (var=inl idx) / (var=inr val) to match Java."""
function _format_query_prov(assignment::Dict{Symbol, Any}, elem_index::Dict{Any, Int};
                           coprod_elem_display::Dict{Any, String}=Dict{Any, String}())
    # Separate entity-level (inl) and type-level (inr) variables
    inl_parts = Tuple{Symbol, String}[]
    inr_parts = Tuple{Symbol, String}[]
    for var in keys(assignment)
        val = assignment[var]
        if val isa Tuple{Symbol, Any}
            # Tuple carrier (delta instance): format as (Entity, idx)
            (t_en, t_elem) = val
            # Look up the TUPLE in elem_index (delta instances index by tuple)
            t_idx = get(elem_index, val, nothing)
            if t_idx !== nothing
                push!(inl_parts, (var, "($var=inl ($t_en, $t_idx))"))
            else
                # Try inner element
                t_idx2 = get(elem_index, t_elem, nothing)
                if t_idx2 !== nothing
                    push!(inl_parts, (var, "($var=inl ($t_en, $t_idx2))"))
                else
                    push!(inl_parts, (var, "($var=inl ($t_en, $t_elem))"))
                end
            end
        elseif val isa CQL.CQLSym || val isa CQL.CQLSk
            push!(inr_parts, (var, "($var=inr $(val.sym))"))
        else
            idx = get(elem_index, val, nothing)
            if idx !== nothing
                # Check if this element has coproduct provenance
                cprov = get(coprod_elem_display, val, nothing)
                if cprov !== nothing
                    push!(inl_parts, (var, "($var=inl $cprov)"))
                else
                    push!(inl_parts, (var, "($var=inl $idx)"))
                end
            else
                push!(inl_parts, (var, "($var=$val)"))
            end
        end
    end
    # Java builds nested Term: alphabetical order, type vars (inr) wrap entity vars (inl)
    # Outermost (printed first) is last in iteration order
    sort!(inl_parts, by=x->x[1])
    sort!(inr_parts, by=x->x[1])
    all_sorted = vcat(inl_parts, inr_parts)
    join([p[2] for p in reverse(all_sorted)])
end

"""Strip prefixes from qualified names for display.
Handles Entity__ (double underscore) patterns."""
function _display_name(name::Symbol)::String
    s = string(name)
    # Strip Entity__ prefix (double underscore) from qualified names
    idx = findfirst("__", s)
    if idx !== nothing
        return s[last(idx)+1:end]
    end
    s
end

"""Build display names for columns.
Strips Entity__ prefix and colimit Schema_Entity_ prefix from attribute names."""
function _build_col_display_names(cols::Vector{Symbol}, entity::Symbol;
                                  no_colimit_strip::Bool=false)::Dict{Symbol, String}
    result = Dict{Symbol, String}()
    en_str = string(entity)
    en_prefix = en_str * "_"
    is_colimit_entity = contains(en_str, '_')
    # First pass: compute display names
    display_names = Dict{Symbol, String}()
    for col in cols
        s = string(col)
        # Strip Entity__ prefix (double underscore) — always applies
        idx = findfirst("__", s)
        if idx !== nothing
            display_names[col] = s[last(idx)+1:end]
        elseif no_colimit_strip
            # simplify_names=false: keep full attribute names
            display_names[col] = s
        # For colimit entities: strip entity prefix from attributes
        elseif is_colimit_entity && startswith(s, en_prefix) && length(s) > length(en_prefix)
            display_names[col] = s[length(en_prefix)+1:end]
        else
            # Try colimit-pattern simplification for attrs from merged entities
            simplified = _simplify_att_name(col)
            display_names[col] = simplified
        end
    end
    # Check for conflicts
    name_count = Dict{String, Int}()
    for (_, dn) in display_names
        name_count[dn] = get(name_count, dn, 0) + 1
    end
    for col in cols
        dn = display_names[col]
        if name_count[dn] > 1
            result[col] = string(col)  # keep full name on conflict
        else
            result[col] = dn
        end
    end
    result
end

"""Format an attribute value to match Java output.
Java shows: literal@Type for concrete values (only when type has external_parser),
"inr (idx, att)" for Skolems."""
function format_att_val(t, tgt_type::Symbol,
                        elem_index::Dict{Any, Int},
                        parsed_types::Set{Symbol}=Set{Symbol}(),
                        gen_name_map::Dict{Any, Symbol}=Dict{Any, Symbol}();
                        parent_elem=nothing, parent_att::Symbol=:_,
                        coprod_elem_display::Dict{Any, String}=Dict{Any, String}())::String
    has_parser = tgt_type in parsed_types
    # Java unwraps Optional types: Optional.of(2) displays as plain 2
    is_nullable = startswith(string(tgt_type), "Nullable")
    if t isa CQL.CQLSk
        s = string(t.sk)
        # Java Optional.empty() displays as empty string
        if s == "null"
            return ""
        end
        # Check if this is an unresolved Skolem (gen.fk...att pattern)
        inr = _try_skolem_inr(s, elem_index, gen_name_map, coprod_elem_display)
        if inr !== nothing
            return inr
        end
        # Chase-generated Skolem (e.g., "ce5"): format as inr(elem_idx, att)
        # Only match colimit/chase prefixes, not user-defined generators like "order1"
        if parent_elem !== nothing && !has_parser && !is_nullable &&
           match(r"^ce\d+$", s) !== nothing
            att_display = _simplify_att_name(parent_att)
            gen = get(gen_name_map, parent_elem, nothing)
            cprov = get(coprod_elem_display, parent_elem, nothing)
            if gen !== nothing
                return "\"inr ($gen, $att_display)\""
            elseif cprov !== nothing
                return "\"inr ($cprov, $att_display)\""
            end
            idx = get(elem_index, parent_elem, nothing)
            if idx !== nothing
                return "\"inr ($idx, $att_display)\""
            end
        end
        # With parser: quote + annotate. Without: bare value.
        # Nullable types: unwrap Optional, display inner value without annotation
        if is_nullable
            return s
        elseif has_parser
            return _maybe_quote(s, tgt_type) * "@" * string(tgt_type)
        else
            return s
        end
    elseif t isa CQL.CQLSym
        if isempty(t.args)
            s = string(t.sym)
            # Java Optional.empty() displays as empty string
            if s == "null"
                return ""
            end
            if is_nullable
                return s
            elseif has_parser
                return _maybe_quote(s, tgt_type) * "@" * string(tgt_type)
            else
                # For numeric types, Java doesn't call maybeQuote — display raw
                if tgt_type in (:Integer, :Int, :int, :integer, :Bigint, :bigint,
                                :Smallint, :smallint, :Tinyint, :tinyint,
                                :Double, :Float, :Real, :double, :float, :real,
                                :Numeric, :numeric, :Decimal, :decimal)
                    return s
                end
                return _maybe_quote(s, tgt_type; quote_integers=false)
            end
        else
            return _format_complex(t, elem_index, parsed_types, gen_name_map)
        end
    elseif t isa CQL.CQLAtt
        inner = t.arg
        att_display = _simplify_att_name(t.att)
        gen = get(gen_name_map, inner, nothing)
        cprov = get(coprod_elem_display, inner, nothing)
        if gen !== nothing
            return "\"inr ($gen, $att_display)\""
        elseif cprov !== nothing
            return "\"inr ($cprov, $att_display)\""
        end
        idx = get(elem_index, inner, nothing)
        if idx !== nothing
            return "\"inr ($idx, $att_display)\""
        else
            return format_term(t, elem_index)
        end
    elseif t isa CQL.CQLFk
        return format_term(t, elem_index)
    elseif t isa Symbol
        if has_parser
            return _maybe_quote(string(t), tgt_type) * "@" * string(tgt_type)
        else
            return string(t)
        end
    else
        return format_term(t, elem_index)
    end
end

"""Simplify a colimit-prefixed attribute name: SchemaName_EntityName_BaseName → BaseName.
Only strips when the name has a clear colimit prefix pattern (SchemaName_EntityName_)."""
function _simplify_att_name(att::Symbol)::String
    s = string(att)
    # Strip Entity__ prefix from entity-qualified names (e.g., Gender__att → att)
    idx = findfirst("__", s)
    if idx !== nothing
        return s[last(idx)+1:end]
    end
    # Strip colimit Schema_Entity_ prefix (e.g., sPatientMed_Patient_PM_Patient_Name → PM_Patient_Name)
    parts = split(s, '_')
    if length(parts) >= 3 && length(parts[1]) >= 2 &&
       parts[1][1] == 's' && isuppercase(parts[1][2])
        return join(parts[3:end], '_')
    end
    s
end

"""Try to parse a Skolem name as gen.fk1.fk2...att and format as inr(idx, att)."""
function _try_skolem_inr(s::String, elem_index::Dict{Any, Int},
                         gen_name_map::Dict{Any, Symbol}=Dict{Any, Symbol}(),
                         coprod_elem_display::Dict{Any, String}=Dict{Any, String}())::Union{String, Nothing}
    parts = split(s, '.')
    length(parts) < 2 && return nothing
    att_name = _simplify_att_name(Symbol(parts[end]))
    # Build the carrier element term from gen.fk1.fk2...
    gen_name = Symbol(parts[1])
    term = CQL.CQLGen(gen_name)
    for i in 2:length(parts)-1
        term = CQL.CQLFk(Symbol(parts[i]), term)
    end
    # For frozen/interpret_as_algebra: use gen name if available
    gen = get(gen_name_map, term, nothing)
    if gen !== nothing
        return "\"inr ($gen, $att_name)\""
    end
    # Coproduct provenance
    cprov = get(coprod_elem_display, term, nothing)
    if cprov !== nothing
        return "\"inr ($cprov, $att_name)\""
    end
    idx = get(elem_index, term, nothing)
    idx === nothing && return nothing
    return "\"inr ($idx, $att_name)\""
end

"""Match Java's Util.maybeQuote: quote strings with non-alphanumeric chars, escape JSON.
For Double/Float types, format whole numbers with .0 suffix."""
function _maybe_quote(s::String, tgt_type::Symbol=:unknown; quote_integers::Bool=true)::String
    # For Double/Float types, format numeric values with .0 suffix for whole numbers
    is_float_type = tgt_type in (:Double, :Float, :Real, :Doubleprecision, :double, :float)
    if is_float_type && _looks_numeric(s)
        n = parse(Float64, s)
        formatted = n == floor(n) && isfinite(n) ? string(Int(n)) * ".0" : string(n)
        return "\"$formatted\""
    end
    # If starts with digit or is a negative number, check if purely numeric
    if !isempty(s) && (isdigit(s[1]) || (s[1] == '-' && length(s) > 1 && isdigit(s[2])))
        # Pure integers: optional leading minus, then all digits
        is_pure_int = if s[1] == '-'
            length(s) > 1 && all(isdigit, @view s[2:end])
        else
            all(isdigit, s)
        end
        if is_pure_int && !quote_integers
            return s
        end
        return "\"" * _escape_json(s) * "\""
    end
    # If alphanumeric (letters, digits only), no quoting needed
    if all(c -> isletter(c) || isdigit(c), s)
        return s
    end
    # If alphanumeric + underscores only, no quoting needed
    if all(c -> isletter(c) || isdigit(c) || c == '_', s)
        return s
    end
    # Otherwise, quote with JSON escaping
    return "\"" * _escape_json(s) * "\""
end

"""Escape string for JSON output (like StringEscapeUtils.escapeJson)."""
function _escape_json(s::String)::String
    buf = IOBuffer()
    for c in s
        if c == '"'
            write(buf, "\\\"")
        elseif c == '\\'
            write(buf, "\\\\")
        elseif c == '/'
            write(buf, "\\/")
        elseif c == '\n'
            write(buf, "\\n")
        elseif c == '\r'
            write(buf, "\\r")
        elseif c == '\t'
            write(buf, "\\t")
        else
            write(buf, c)
        end
    end
    return String(take!(buf))
end

"""Format a complex term (CQLSym with args)."""
function _format_complex(t::CQL.CQLSym, elem_index::Dict{Any, Int},
                         parsed_types::Set{Symbol}=Set{Symbol}(),
                         gen_name_map::Dict{Any, Symbol}=Dict{Any, Symbol}())::String
    args = join([_format_complex_arg(a, elem_index, parsed_types) for a in t.args], " ")
    if length(t.args) == 0
        return string(t.sym)
    elseif length(t.args) == 2
        return "($(format_att_val_inner(t.args[1], elem_index, parsed_types, gen_name_map)) $(t.sym) $(format_att_val_inner(t.args[2], elem_index, parsed_types, gen_name_map)))"
    else
        return "$(t.sym)($(join([format_att_val_inner(a, elem_index, parsed_types, gen_name_map) for a in t.args], ", ")))"
    end
end

function format_att_val_inner(t, elem_index::Dict{Any, Int},
                              parsed_types::Set{Symbol}=Set{Symbol}(),
                              gen_name_map::Dict{Any, Symbol}=Dict{Any, Symbol}())::String
    has_parsers = !isempty(parsed_types)
    if t isa CQL.CQLSk
        s = string(t.sk)
        # Check for unresolved Skolem (gen.att pattern)
        inr = _try_skolem_inr(s, elem_index, gen_name_map)
        if inr !== nothing
            return inr
        end
        if has_parsers
            guessed_type = _looks_numeric(s) ? Symbol(_guess_numeric_type(s)) : :unknown
            quoted = _maybe_quote(s, guessed_type)
            # For inner values, add @Type if it looks numeric
            if _looks_numeric(s)
                return quoted * "@" * _guess_numeric_type(s)
            end
            return quoted
        else
            return s
        end
    elseif t isa CQL.CQLSym
        if isempty(t.args)
            s = string(t.sym)
            if has_parsers
                guessed_type = _looks_numeric(s) ? Symbol(_guess_numeric_type(s)) : :unknown
                quoted = _maybe_quote(s, guessed_type)
                if _looks_numeric(s)
                    return quoted * "@" * _guess_numeric_type(s)
                end
                return quoted
            else
                return s
            end
        else
            return _format_complex(t, elem_index, parsed_types, gen_name_map)
        end
    elseif t isa CQL.CQLAtt
        att_display = _simplify_att_name(t.att)
        gen = get(gen_name_map, t.arg, nothing)
        if gen !== nothing
            return "\"inr ($gen, $att_display)\""
        end
        idx = get(elem_index, t.arg, nothing)
        if idx !== nothing
            return "\"inr ($idx, $att_display)\""
        end
        return format_term(t, elem_index)
    else
        return format_term(t, elem_index)
    end
end

function _looks_numeric(s::String)::Bool
    try
        parse(Float64, s)
        return true
    catch
        return false
    end
end

function _guess_numeric_type(s::String)::String
    occursin('.', s) ? "Double" : "Integer"
end

"""Format a CQL term for comparison output."""
function format_term(t, elem_index::Dict{Any, Int}=Dict{Any,Int}())::String
    if t isa CQL.CQLSym
        if isempty(t.args)
            return string(t.sym)
        else
            args = join([format_term(a, elem_index) for a in t.args], ", ")
            return "$(t.sym)($args)"
        end
    elseif t isa CQL.CQLSk
        return string(t.sk)
    elseif t isa CQL.CQLGen
        return string(t.gen)
    elseif t isa CQL.CQLVar
        return string(t.var)
    elseif t isa CQL.CQLAtt
        return "$(t.att)($(format_term(t.arg, elem_index)))"
    elseif t isa CQL.CQLFk
        return "$(t.fk)($(format_term(t.arg, elem_index)))"
    else
        return string(t)
    end
end

function _format_complex_arg(t, elem_index::Dict{Any, Int},
                             parsed_types::Set{Symbol}=Set{Symbol}())::String
    format_att_val_inner(t, elem_index, parsed_types)
end

if length(ARGS) < 1
    println(stderr, "Usage: julia cql_dump.jl <file.cql>")
    exit(1)
end

dump_instances(ARGS[1])
