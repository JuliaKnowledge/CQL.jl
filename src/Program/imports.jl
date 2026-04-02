# ============================================================================
# CSV import
# ============================================================================

"""Evaluate an import_csv instance expression.
If the schema reference resolves to a typeside, auto-discover schema from CSV files.
If it resolves to a schema, use it directly."""
function _eval_import_csv(env::Env, e::InstanceImportCsv)::CQLInstance
    path = strip(e.path, '"')

    # Try to resolve as a schema first
    sch = try
        eval_schema(env, e.schema)
    catch
        nothing
    end

    if sch !== nothing
        return import_csv_instance(path, sch)
    end

    # Resolve as a typeside and auto-discover schema from CSV files
    ts = if e.schema isa SchemaVar
        haskey(env.typesides, e.schema.name) || throw(CQLException(
            "import_csv: '$(e.schema.name)' is neither a schema nor a typeside"))
        env.typesides[e.schema.name]
    else
        throw(CQLException("import_csv: cannot resolve schema/typeside reference"))
    end

    # Discover schema and build instance from CSV files
    _import_csv_discover(path, ts, env.options)
end

"""Auto-discover schema from CSV files and import data."""
function _import_csv_discover(dir::AbstractString, ts::Typeside, opts::CQLOptions)::CQLInstance
    isdir(dir) || throw(CQLException("import_csv: directory not found: $dir"))

    csv_files = filter(f -> endswith(lowercase(f), ".csv"), readdir(dir))
    isempty(csv_files) && throw(CQLException("import_csv: no CSV files found in $dir"))

    # Default attribute type: use String if available, else first type
    default_type = :String in ts.tys ? :String :
                   :Dom in ts.tys ? :Dom : first(ts.tys)

    ens = Set{Symbol}()
    fks = Dict{Symbol, Tuple{Symbol, Symbol}}()
    atts = Dict{Symbol, Tuple{Symbol, Symbol}}()
    gens = Dict{Symbol, Symbol}()
    eqs = Set{Equation}()

    # Mapping from entity -> (column_name -> row_id -> value)
    entity_ids = Dict{Symbol, Dict{String, Symbol}}()

    for csv_file in csv_files
        en_name = Symbol(replace(csv_file, r"\.csv$"i => ""))
        push!(ens, en_name)
        entity_ids[en_name] = Dict{String, Symbol}()

        filepath = joinpath(dir, csv_file)
        csvdata = CSV.File(filepath; silencewarnings=true)
        cols = propertynames(csvdata)

        # Each column becomes an attribute: entity__col : entity -> default_type
        for col in cols
            att_name = Symbol(en_name, "__", col)
            atts[att_name] = (en_name, default_type)
        end

        # Create generators for each row (auto-incremented IDs)
        row_id = 0
        for row in csvdata
            gen_sym = Symbol(en_name, "_", row_id)
            gens[gen_sym] = en_name
            entity_ids[en_name][string(row_id)] = gen_sym

            for col in cols
                att_name = Symbol(en_name, "__", col)
                val = getproperty(row, col)
                if val !== missing
                    val_str = strip(string(val))
                    if !isempty(val_str)
                        push!(eqs, Equation(
                            CQLAtt(att_name, CQLGen(gen_sym)),
                            CQLSym(Symbol(val_str), CQLTerm[])))
                    end
                end
            end
            row_id += 1
        end
    end

    # Build name lookup indices
    att_by_name = Dict{Symbol, Vector{Symbol}}()
    for att_name in keys(atts)
        plain = Symbol(split(string(att_name), "__"; limit=2)[end])
        if !haskey(att_by_name, plain)
            att_by_name[plain] = Symbol[]
        end
        push!(att_by_name[plain], att_name)
    end

    sch = CQLSchema(ts, ens, fks, atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(),
        (en, eq) -> eq.lhs == eq.rhs,
        Dict{Symbol,Vector{Symbol}}(), att_by_name, collect(keys(fks)))

    pres = Presentation(gens, Dict{Symbol,Symbol}(), eqs)
    saturated_instance(sch, pres)
end

# ============================================================================
# XML import
# ============================================================================

"""Import an XML file as an RDF-style CQL instance.
Flattens the XML tree into (subject, predicate, object) triples on the built-in RDF schema."""
function _eval_import_xml(path::AbstractString)::CQLInstance
    path = strip(path, '"')
    isfile(path) || throw(CQLException("import_xml_all: file not found: $path"))

    doc = read(path, XMLParser.Node)

    # Build RDF schema
    ts = rdf_typeside()
    ens = Set{Symbol}([:R])
    fks = Dict{Symbol,Tuple{Symbol,Symbol}}()
    atts = Dict{Symbol,Tuple{Symbol,Symbol}}(
        :subject => (:R, :Dom),
        :predicate => (:R, :Dom),
        :object => (:R, :Dom),
    )
    sch = CQLSchema(ts, ens, fks, atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(),
        (en, eq) -> eq.lhs == eq.rhs)

    # Flatten XML into triples
    triples = Tuple{String, String, String}[]
    counter = Ref(0)
    _xml_to_triples!(triples, doc, "", counter)

    # Build instance
    gens = Dict{Symbol, Symbol}()
    eqs = Set{Equation}()
    for (i, (subj, pred, obj)) in enumerate(triples)
        gen_sym = Symbol("triple_", i)
        gens[gen_sym] = :R
        push!(eqs, Equation(
            CQLAtt(:subject, CQLGen(gen_sym)),
            CQLSym(Symbol(subj), CQLTerm[])))
        push!(eqs, Equation(
            CQLAtt(:predicate, CQLGen(gen_sym)),
            CQLSym(Symbol(pred), CQLTerm[])))
        push!(eqs, Equation(
            CQLAtt(:object, CQLGen(gen_sym)),
            CQLSym(Symbol(obj), CQLTerm[])))
    end

    pres = Presentation(gens, Dict{Symbol,Symbol}(), eqs)
    saturated_instance(sch, pres)
end

"""Recursively flatten an XML node tree into (subject, predicate, object) triples.
Matches Java's XML→JSON→RDF pipeline: leaf elements with only text content
are collapsed into the parent triple, and the root element gets a wrapper triple."""
function _xml_to_triples!(triples::Vector{Tuple{String,String,String}},
                           node::XMLParser.Node, parent_id::String, counter::Ref{Int})
    nk = XMLParser.nodetype(node)

    if nk == XMLParser.Element
        node_tag = XMLParser.tag(node)

        # Gather text and element children
        text_parts = String[]
        child_elems = XMLParser.Node[]
        for child in XMLParser.children(node)
            ct = XMLParser.nodetype(child)
            if ct == XMLParser.Text
                txt = strip(XMLParser.value(child))
                if !isempty(txt)
                    push!(text_parts, txt)
                end
            elseif ct == XMLParser.Element
                push!(child_elems, child)
            end
        end

        # Leaf element (only text, no child elements): collapse into parent
        if !isempty(text_parts) && isempty(child_elems) && !isempty(parent_id)
            push!(triples, (parent_id, node_tag, join(text_parts, " ")))
            return
        end

        # Non-leaf element: create a node
        counter[] += 1
        node_id = string("node_", counter[])

        if !isempty(parent_id)
            push!(triples, (parent_id, node_tag, node_id))
        end

        # Attributes (no @ prefix, matching Java's JSON conversion)
        node_attrs = XMLParser.attributes(node)
        if node_attrs !== nothing
            for (k, v) in node_attrs
                push!(triples, (node_id, k, v))
            end
        end

        # Recurse into child elements
        for child in child_elems
            _xml_to_triples!(triples, child, node_id, counter)
        end

        # Non-leaf with text: add text as content triple
        if !isempty(text_parts) && !isempty(child_elems)
            push!(triples, (node_id, "content", join(text_parts, " ")))
        end
    elseif nk == XMLParser.Document
        for child in XMLParser.children(node)
            ct = XMLParser.nodetype(child)
            if ct == XMLParser.Element
                # Root element: add wrapper triple (root_node --tag--> content_node)
                root_tag = XMLParser.tag(child)
                counter[] += 1
                wrapper_id = string("node_", counter[])
                counter[] += 1
                content_id = string("node_", counter[])
                push!(triples, (content_id, root_tag, wrapper_id))
                # Process root element's children using wrapper_id as parent
                root_attrs = XMLParser.attributes(child)
                if root_attrs !== nothing
                    for (k, v) in root_attrs
                        push!(triples, (wrapper_id, k, v))
                    end
                end
                for grandchild in XMLParser.children(child)
                    _xml_to_triples!(triples, grandchild, wrapper_id, counter)
                end
            end
        end
    end
end

"""Spanify an RDF instance: group triples by predicate, creating one entity per predicate.
Each entity gets subject and object attributes of type Dom."""
function _eval_instance_spanify(inst::CQLInstance, env::Env)::CQLInstance
    ts = rdf_typeside()
    alg = inst.algebra

    # Group generators by predicate value
    pred_groups = Dict{String, Vector{Symbol}}()  # predicate -> [gen_syms]
    r_gens = get(alg.en, :R, Set{Symbol}())

    for x in r_gens
        pred_term = alg.nf_y(Right((x, :predicate)))
        pred_str = if pred_term isa CQLSym
            string(pred_term.sym)
        elseif pred_term isa CQLSk
            string(pred_term.sk)
        else
            string(pred_term)
        end
        lst = get!(pred_groups, pred_str, Symbol[])
        push!(lst, x)
    end

    # Build spanified schema: one entity per predicate, each with subject/object attributes
    ens = Set{Symbol}()
    fks = Dict{Symbol,Tuple{Symbol,Symbol}}()
    atts = Dict{Symbol,Tuple{Symbol,Symbol}}()
    for pred in keys(pred_groups)
        en_sym = Symbol(pred)
        push!(ens, en_sym)
        atts[Symbol(string(en_sym, "__subject"))] = (en_sym, :Dom)
        atts[Symbol(string(en_sym, "__object"))] = (en_sym, :Dom)
    end
    sch = CQLSchema(ts, ens, fks, atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(),
        (en, eq) -> eq.lhs == eq.rhs)

    # Build presentation with generators and attribute equations
    pres_gens = Dict{Symbol, Symbol}()
    pres_eqs = Set{Equation}()
    for (pred, xs) in pred_groups
        en_sym = Symbol(pred)
        subj_att = Symbol(string(en_sym, "__subject"))
        obj_att = Symbol(string(en_sym, "__object"))
        for x in xs
            pres_gens[x] = en_sym
            # Get subject and object values from original algebra
            subj_term = alg.nf_y(Right((x, :subject)))
            obj_term = alg.nf_y(Right((x, :object)))
            push!(pres_eqs, Equation(CQLAtt(subj_att, CQLGen(x)), subj_term))
            push!(pres_eqs, Equation(CQLAtt(obj_att, CQLGen(x)), obj_term))
        end
    end

    pres = Presentation(pres_gens, Dict{Symbol,Symbol}(), pres_eqs)
    saturated_instance(sch, pres)
end

"""Evaluate an import_json_ld_all instance expression.
Converts JSON to RDF-style triples following the JSON2RDF algorithm:
each JSON object becomes a blank node, keys become predicates, values become literals."""
function _eval_import_json_ld(path::AbstractString)::CQLInstance
    path = strip(path, '"')
    isfile(path) || throw(CQLException("import_json_ld_all: file not found: $path"))

    data = JSONParser.parsefile(path)

    # Build RDF schema (same as XML import)
    ts = rdf_typeside()
    ens = Set{Symbol}([:R])
    fks = Dict{Symbol,Tuple{Symbol,Symbol}}()
    atts = Dict{Symbol,Tuple{Symbol,Symbol}}(
        :subject => (:R, :Dom),
        :predicate => (:R, :Dom),
        :object => (:R, :Dom),
    )
    sch = CQLSchema(ts, ens, fks, atts,
        Set{Tuple{Symbol,Equation}}(), Set{Tuple{Symbol,Equation}}(),
        (en, eq) -> eq.lhs == eq.rhs)

    # Flatten JSON into RDF triples
    triples = Tuple{String, String, String}[]
    counter = Ref(0)
    base_uri = "cql://json"
    _json_to_triples!(triples, data, "", base_uri, counter)

    # Build instance
    gens = Dict{Symbol, Symbol}()
    eqs = Set{Equation}()
    for (i, (subj, pred, obj)) in enumerate(triples)
        gen_sym = Symbol("triple_", i)
        gens[gen_sym] = :R
        push!(eqs, Equation(
            CQLAtt(:subject, CQLGen(gen_sym)),
            CQLSym(Symbol(subj), CQLTerm[])))
        push!(eqs, Equation(
            CQLAtt(:predicate, CQLGen(gen_sym)),
            CQLSym(Symbol(pred), CQLTerm[])))
        push!(eqs, Equation(
            CQLAtt(:object, CQLGen(gen_sym)),
            CQLSym(Symbol(obj), CQLTerm[])))
    end

    pres = Presentation(gens, Dict{Symbol,Symbol}(), eqs)
    saturated_instance(sch, pres)
end

"""Recursively convert a JSON value into (subject, predicate, object) triples.
Follows the JSON2RDF algorithm: objects → blank nodes, keys → URI predicates,
scalars → literal objects, arrays → repeated predicates."""
function _json_to_triples!(triples::Vector{Tuple{String,String,String}},
                           value, parent_id::String, base_uri::String, counter::Ref{Int})
    if value isa AbstractDict
        counter[] += 1
        node_id = string("node_", counter[])
        # Link parent to this object
        if !isempty(parent_id)
            push!(triples, (parent_id, "", node_id))
        end
        # Process each key-value pair
        for (k, v) in value
            prop = string(base_uri, "#", k)
            _json_kv_to_triples!(triples, node_id, prop, v, base_uri, counter)
        end
        return node_id
    elseif value isa AbstractVector
        for item in value
            _json_kv_to_triples!(triples, parent_id, "", item, base_uri, counter)
        end
        return parent_id
    else
        # Scalar at top level (unusual) — ignore
        return ""
    end
end

"""Convert a JSON key-value pair into triples."""
function _json_kv_to_triples!(triples::Vector{Tuple{String,String,String}},
                              subject::String, predicate::String, value,
                              base_uri::String, counter::Ref{Int})
    if value isa AbstractDict
        counter[] += 1
        child_id = string("node_", counter[])
        push!(triples, (subject, predicate, child_id))
        for (k, v) in value
            prop = string(base_uri, "#", k)
            _json_kv_to_triples!(triples, child_id, prop, v, base_uri, counter)
        end
    elseif value isa AbstractVector
        for item in value
            _json_kv_to_triples!(triples, subject, predicate, item, base_uri, counter)
        end
    elseif value === nothing
        # null — skip (matches Java behavior)
    else
        push!(triples, (subject, predicate, string(value)))
    end
end

