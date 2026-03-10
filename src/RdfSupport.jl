# RdfSupport.jl — Minimal RDF/XML support for CQL.jl
# Provides export_rdf_instance_xml and import_rdf_all functionality

import XML as XMLParser

# ============================================================================
# RDF/XML Export — generates RDF/XML from CQL instance
# ============================================================================

const _RDF_NS = "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
const _RDFS_NS = "http://www.w3.org/2000/01/rdf-schema#"
const _XSD_DEFAULT = "http://www.w3.org/2001/XMLSchema#String"

"""Convert a CQL type to an XSD URI, using the external_types map if available."""
function _rdf_type_convert(ty::String, type_map::Dict{String,String})::String
    haskey(type_map, ty) && return type_map[ty]
    return _XSD_DEFAULT
end

"""Extract a string value from a CQL attribute term, using the algebra to distinguish
concrete values from Skolem terms. Returns nothing for Skolem/unknown terms."""
function _rdf_value_string(t::CQLTerm, alg::Algebra)::Union{String,Nothing}
    if t isa CQLSym && isempty(t.args)
        return string(t.sym)
    end
    if t isa CQLSk
        # Look up the TalgGen representation to check if this is a concrete value
        tg = TalgGen(Left(t.sk))
        if haskey(alg.repr_y, tg)
            repr = alg.repr_y[tg]
            if repr isa CQLSk
                # Concrete value — the Skolem name IS the value
                return string(t.sk)
            end
        end
    end
    return nothing
end

"""Split a URI into (namespace, localname) at the last # or /."""
function _split_uri(uri::String)::Tuple{String,String}
    idx_hash = findlast('#', uri)
    idx_slash = findlast('/', uri)
    if idx_hash !== nothing && (idx_slash === nothing || idx_hash > idx_slash)
        return (uri[1:idx_hash], uri[idx_hash+1:end])
    elseif idx_slash !== nothing
        return (uri[1:idx_slash], uri[idx_slash+1:end])
    end
    return (uri, "")
end

"""XML-escape a string for safe embedding in XML attributes and text."""
function _xml_escape(s::String)::String
    s = replace(s, '&' => "&amp;")
    s = replace(s, '<' => "&lt;")
    s = replace(s, '>' => "&gt;")
    s = replace(s, '"' => "&quot;")
    return s
end

"""
Export a CQL instance to RDF/XML format, matching Java CQL's RdfExporter.xmlExport1.

Generates:
- Schema triples: entities as rdfs:Class, attributes/fks as rdf:Property with domain/range
- Instance triples: entity members with rdf:type, attribute literals, fk resource links
"""
function eval_export_rdf_instance_xml(env, inst_name::String, filepath::String,
                                      external_types::Dict{String,String},
                                      opts)
    haskey(env.instances, inst_name) || throw(CQLException(
        "export_rdf_instance_xml: undefined instance: $inst_name"))
    inst = env.instances[inst_name]
    sch = inst.schema
    alg = inst.algebra

    start = 0  # default start_ids_at

    # Build type map from external_types (ty -> xsd_uri)
    type_map = copy(external_types)

    # Collect all triples as (subject, predicate, object_uri_or_nothing, object_literal_or_nothing)
    triples = Tuple{String,String,Union{String,Nothing},Union{String,Nothing}}[]

    # --- Schema triples ---
    sorted_ens = sort(collect(sch.ens))

    for en in sorted_ens
        en_str = string(en)
        push!(triples, ("cql://entity/$en_str", _RDF_NS * "type", _RDFS_NS * "Class", nothing))
    end

    for en in sorted_ens
        en_str = string(en)
        # Attributes from this entity
        for (att_sym, ty_sym) in schema_atts_from(sch, en)
            att_name = _display_name(att_sym)
            ty_str = string(ty_sym)
            range_uri = _rdf_type_convert(ty_str, type_map)
            att_uri = "cql://attribute/$en_str/$att_name"
            push!(triples, (att_uri, _RDF_NS * "type", _RDF_NS * "Property", nothing))
            push!(triples, (att_uri, _RDFS_NS * "domain", "cql://entity/$en_str", nothing))
            push!(triples, (att_uri, _RDFS_NS * "range", range_uri, nothing))
        end
        # Foreign keys from this entity
        for (fk_sym, tgt_en) in schema_fks_from(sch, en)
            fk_name = _display_name(fk_sym)
            tgt_str = string(tgt_en)
            fk_uri = "cql://foreign_key/$en_str/$fk_name"
            push!(triples, (fk_uri, _RDF_NS * "type", _RDF_NS * "Property", nothing))
            push!(triples, (fk_uri, _RDFS_NS * "domain", "cql://entity/$en_str", nothing))
            push!(triples, (fk_uri, _RDFS_NS * "range", "cql://entity/$tgt_str", nothing))
        end
    end

    # --- Instance data ---
    # Build element → resource URI map, maintaining order
    en_elements = Dict{Symbol, Vector{Any}}()
    en_resources = Dict{Symbol, Dict{Any, String}}()

    for en in sorted_ens
        en_str = string(en)
        elements = sort(collect(alg.en[en]), by=x -> string(repr_x(alg, x)))
        en_elements[en] = elements
        res_map = Dict{Any, String}()
        for (idx, x) in enumerate(elements)
            uri = "cql://entity/$en_str/$(idx - 1 + start)"
            res_map[x] = uri
        end
        en_resources[en] = res_map
    end

    # Entity member triples
    for en in sorted_ens
        en_str = string(en)
        elements = en_elements[en]
        for x in elements
            uri = en_resources[en][x]
            # rdf:type
            push!(triples, (uri, _RDF_NS * "type", "cql://entity/$en_str", nothing))
        end
    end

    # Attribute triples
    for en in sorted_ens
        en_str = string(en)
        elements = en_elements[en]
        for (att_sym, _) in schema_atts_from(sch, en)
            att_name = _display_name(att_sym)
            for x in elements
                val_term = eval_att(alg, att_sym, x)
                val_str = _rdf_value_string(val_term, alg)
                val_str === nothing && continue
                uri = en_resources[en][x]
                push!(triples, (uri, "cql://attribute/$en_str/$att_name", nothing, val_str))
            end
        end
    end

    # Foreign key triples
    for en in sorted_ens
        en_str = string(en)
        elements = en_elements[en]
        for (fk_sym, tgt_en) in schema_fks_from(sch, en)
            fk_name = _display_name(fk_sym)
            for x in elements
                tgt_x = eval_fk(alg, fk_sym, x)
                tgt_uri = en_resources[tgt_en][tgt_x]
                uri = en_resources[en][x]
                push!(triples, (uri, "cql://foreign_key/$en_str/$fk_name", tgt_uri, nothing))
            end
        end
    end

    # Generate RDF/XML
    xml_str = _triples_to_rdf_xml(triples)

    open(filepath, "w") do io
        write(io, xml_str)
    end
end

"""Generate RDF/XML string from a list of triples."""
function _triples_to_rdf_xml(triples::Vector{Tuple{String,String,Union{String,Nothing},Union{String,Nothing}}})::String
    # Collect unique namespace URIs from predicates
    ns_map = Dict{String,String}(
        "rdf" => _RDF_NS,
        "rdfs" => _RDFS_NS,
    )
    auto_ns_counter = 0
    ns_reverse = Dict{String,String}(v => k for (k,v) in ns_map)

    function ensure_ns(uri::String)::Tuple{String,String}
        ns, localname = _split_uri(uri)
        if haskey(ns_reverse, ns)
            return (ns_reverse[ns], localname)
        end
        prefix = "j.$auto_ns_counter"
        auto_ns_counter += 1
        ns_map[prefix] = ns
        ns_reverse[ns] = prefix
        return (prefix, localname)
    end

    # Pre-scan predicates
    for (_, pred, _, _) in triples
        ensure_ns(pred)
    end

    io = IOBuffer()
    println(io, """<?xml version="1.0" encoding="UTF-8"?>""")
    print(io, "<rdf:RDF")
    for (prefix, uri) in sort(collect(ns_map), by=first)
        print(io, "\n    xmlns:$prefix=\"$(_xml_escape(uri))\"")
    end
    println(io, ">")

    # Group triples by subject
    subj_triples = Dict{String, Vector{Tuple{String,Union{String,Nothing},Union{String,Nothing}}}}()
    for (subj, pred, obj_uri, obj_lit) in triples
        push!(get!(subj_triples, subj, []), (pred, obj_uri, obj_lit))
    end

    for subj in sort(collect(keys(subj_triples)))
        println(io, "  <rdf:Description rdf:about=\"$(_xml_escape(subj))\">")
        for (pred, obj_uri, obj_lit) in subj_triples[subj]
            prefix, localname = ensure_ns(pred)
            if obj_uri !== nothing
                println(io, "    <$prefix:$localname rdf:resource=\"$(_xml_escape(obj_uri))\"/>")
            else
                println(io, "    <$prefix:$localname>$(_xml_escape(obj_lit))</$(prefix):$(localname)>")
            end
        end
        println(io, "  </rdf:Description>")
    end

    println(io, "</rdf:RDF>")
    String(take!(io))
end

# ============================================================================
# RDF/XML Import — parses RDF/XML into CQL instance with entity R
# ============================================================================

"""
Import an RDF/XML file as a CQL instance with entity R (subject, predicate, object).
Adapted from RDFLib.jl's RDF/XML parser, using XML.jl instead of EzXML.
"""
function eval_import_rdf_all(path::AbstractString)::CQLInstance
    path = strip(path, '"')
    isfile(path) || throw(CQLException("import_rdf_all: file not found: $path"))

    content = read(path, String)
    triples = _parse_rdf_xml(content)

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

    # Build instance
    gens = Dict{Symbol, Symbol}()
    eqs = Set{Equation}()
    gen_order = Symbol[]
    for (i, (subj, pred, obj)) in enumerate(triples)
        gen_sym = Symbol(string(i - 1))
        gens[gen_sym] = :R
        push!(gen_order, gen_sym)
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

    pres = Presentation(gens, Dict{Symbol,Symbol}(), eqs, gen_order)
    saturated_instance(sch, pres)
end

# ============================================================================
# RDF/XML Parser — minimal parser using XML.jl
# ============================================================================

"""Parse RDF/XML string into a list of (subject, predicate, object) string triples."""
function _parse_rdf_xml(input::String)::Vector{Tuple{String,String,String}}
    doc = XMLParser.parse(input, XMLParser.Node)
    triples = Tuple{String,String,String}[]

    # Find the root element (skip Document, Declaration, etc.)
    root_elem = nothing
    for child in XMLParser.children(doc)
        if XMLParser.nodetype(child) == XMLParser.Element
            root_elem = child
            break
        end
    end
    root_elem === nothing && return triples

    # Build namespace map from root
    ns_map = _rdfxml_collect_namespaces(root_elem)

    # Check for rdf:RDF root
    tag = XMLParser.tag(root_elem)
    local_tag = _rdfxml_local_name(tag)

    if local_tag == "RDF"
        for child in XMLParser.children(root_elem)
            XMLParser.nodetype(child) == XMLParser.Element || continue
            _rdfxml_parse_node!(triples, child, root_elem)
        end
    else
        _rdfxml_parse_node!(triples, root_elem, root_elem)
    end

    triples
end

"""Collect xmlns:* declarations from an element into a prefix→URI map."""
function _rdfxml_collect_namespaces(elem::XMLParser.Node)::Dict{String,String}
    ns_map = Dict{String,String}()
    attrs = XMLParser.attributes(elem)
    attrs === nothing && return ns_map
    for (aname, aval) in attrs
        if startswith(aname, "xmlns:")
            prefix = aname[7:end]
            ns_map[prefix] = aval
        elseif aname == "xmlns"
            ns_map[""] = aval
        end
    end
    ns_map
end

"""Collect all namespace declarations from an element and its ancestors."""
function _rdfxml_collect_all_namespaces(elem::XMLParser.Node, root::XMLParser.Node)::Dict{String,String}
    # Walk from root to elem collecting namespaces
    # Since XML.jl doesn't have parentnode, collect from root and elem
    ns_map = _rdfxml_collect_namespaces(root)
    if elem !== root
        merge!(ns_map, _rdfxml_collect_namespaces(elem))
    end
    ns_map
end

"""Get the local name from a potentially prefixed tag."""
function _rdfxml_local_name(tag::String)::String
    idx = findfirst(':', tag)
    idx === nothing ? tag : tag[idx+1:end]
end

"""Get the prefix from a potentially prefixed tag. Returns empty string if no prefix."""
function _rdfxml_prefix(tag::String)::String
    idx = findfirst(':', tag)
    idx === nothing ? "" : tag[1:idx-1]
end

"""Resolve a prefixed name to a full URI using namespace maps."""
function _rdfxml_resolve_name(name::String, elem::XMLParser.Node, root::XMLParser.Node)::String
    prefix = _rdfxml_prefix(name)
    localname = _rdfxml_local_name(name)

    # Look for namespace in element and ancestors
    ns_uri = _rdfxml_find_ns(elem, root, prefix)
    if ns_uri !== nothing
        return ns_uri * localname
    end

    # If no namespace found, return local name
    return localname
end

"""Find the namespace URI for a prefix by searching the element and root."""
function _rdfxml_find_ns(elem::XMLParser.Node, root::XMLParser.Node, prefix::String)::Union{String,Nothing}
    # Check element first
    attrs = XMLParser.attributes(elem)
    ns_attr = prefix == "" ? "xmlns" : "xmlns:$prefix"
    if attrs !== nothing && haskey(attrs, ns_attr)
        return attrs[ns_attr]
    end

    # Check root
    if elem !== root
        rattrs = XMLParser.attributes(root)
        if rattrs !== nothing && haskey(rattrs, ns_attr)
            return rattrs[ns_attr]
        end
    end

    nothing
end

"""Get the rdf:about, rdf:ID, or rdf:nodeID from an element to determine subject."""
function _rdfxml_get_subject(elem::XMLParser.Node)::String
    attrs = XMLParser.attributes(elem)
    if attrs !== nothing
        for (aname, aval) in attrs
            localname = _rdfxml_local_name(aname)
            if localname == "about"
                return aval
            elseif localname == "ID"
                return "#" * aval
            elseif localname == "nodeID"
                return "_:" * aval
            end
        end
    end
    # Anonymous subject — generate a unique blank node ID
    return "_:bnode_$(objectid(elem))"
end

"""Parse a node element (rdf:Description or typed node) into triples."""
function _rdfxml_parse_node!(triples::Vector{Tuple{String,String,String}},
                             elem::XMLParser.Node, root::XMLParser.Node)
    subject = _rdfxml_get_subject(elem)

    # If element is not rdf:Description, add rdf:type triple
    tag = XMLParser.tag(elem)
    local_tag = _rdfxml_local_name(tag)
    if local_tag != "Description"
        type_uri = _rdfxml_resolve_name(tag, elem, root)
        push!(triples, (subject, _RDF_NS * "type", type_uri))
    end

    # Process child property elements
    for child in XMLParser.children(elem)
        XMLParser.nodetype(child) == XMLParser.Element || continue
        _rdfxml_parse_property!(triples, subject, child, root)
    end
end

"""Parse a property element to extract a triple."""
function _rdfxml_parse_property!(triples::Vector{Tuple{String,String,String}},
                                 subject::String, elem::XMLParser.Node, root::XMLParser.Node)
    tag = XMLParser.tag(elem)
    predicate = _rdfxml_resolve_name(tag, elem, root)

    attrs = XMLParser.attributes(elem)
    if attrs === nothing
        attrs = Dict{String,String}()
    end

    # Check for rdf:resource (URI object)
    for (aname, aval) in attrs
        localname = _rdfxml_local_name(aname)
        if localname == "resource"
            push!(triples, (subject, predicate, aval))
            return
        elseif localname == "nodeID"
            push!(triples, (subject, predicate, "_:" * aval))
            return
        end
    end

    # Check for rdf:parseType
    parse_type = get(attrs, "rdf:parseType", get(attrs, "parseType", nothing))
    if parse_type == "Resource"
        bnode = "_:bnode_$(objectid(elem))_res"
        push!(triples, (subject, predicate, bnode))
        for child in XMLParser.children(elem)
            XMLParser.nodetype(child) == XMLParser.Element || continue
            _rdfxml_parse_property!(triples, bnode, child, root)
        end
        return
    end

    # Check for child elements (nested node)
    children_elems = XMLParser.Node[]
    for child in XMLParser.children(elem)
        XMLParser.nodetype(child) == XMLParser.Element && push!(children_elems, child)
    end

    if !isempty(children_elems)
        child = children_elems[1]
        _rdfxml_parse_node!(triples, child, root)
        obj = _rdfxml_get_subject(child)
        push!(triples, (subject, predicate, obj))
        return
    end

    # Text content → literal value
    text_parts = String[]
    for child in XMLParser.children(elem)
        if XMLParser.nodetype(child) == XMLParser.Text
            push!(text_parts, XMLParser.value(child))
        end
    end
    text = strip(join(text_parts))

    push!(triples, (subject, predicate, text))
end
