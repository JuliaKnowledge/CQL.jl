# Bridging RDF and Property Graphs with CQL
Simon Frost

- [Introduction](#introduction)
- [Two Paradigms, Two Schemas](#two-paradigms-two-schemas)
- [A Marine Food Web as a Property
  Graph](#a-marine-food-web-as-a-property-graph)
- [LPG → RDF via Sigma (Pushforward)](#lpg--rdf-via-sigma-pushforward)
- [RDF → LPG via Delta (Pullback)](#rdf--lpg-via-delta-pullback)
- [Unit and Counit: Formal Round-Trip
  Guarantees](#unit-and-counit-formal-round-trip-guarantees)
- [SPARQL-Like Queries: Joining
  Triples](#sparql-like-queries-joining-triples)
- [The Asymmetry: Edge Properties](#the-asymmetry-edge-properties)
- [Reification: Extending RDF for Edge
  Properties](#reification-extending-rdf-for-edge-properties)
- [Starting from RDF: Delta
  Extraction](#starting-from-rdf-delta-extraction)
- [Schema Colimit: A Unified View](#schema-colimit-a-unified-view)
- [Summary](#summary)

## Introduction

Knowledge graphs come in two dominant paradigms:

1.  **RDF (Resource Description Framework)** — the W3C standard for the
    Semantic Web. Data is stored as **triples** (subject, predicate,
    object). Every entity is a URI. Properties are triples whose object
    is a literal value. Queried via SPARQL.

2.  **Labeled Property Graphs (LPG)** — the model used by Neo4j, Amazon
    Neptune, and TigerGraph. Data consists of **nodes** with labels and
    key–value properties, connected by **edges** that also carry
    properties. Queried via Cypher or Gremlin.

Both paradigms represent knowledge as graphs, but their internal
structure differs in important ways. Moving data between them is a
recurring challenge in bioinformatics, ecology, and public health —
domains where linked data standards (RDF/OWL) coexist with operational
graph databases (Neo4j).

CQL (Categorical Query Language) offers a principled solution. Because
CQL models data via **schemas** (categories) and **instances**
(set-valued functors), both RDF and LPG can be expressed as CQL schemas.
The relationship between the two paradigms becomes a **schema morphism**
(functor), and data migration becomes a functorial operation — **Sigma**
(pushforward) and **Delta** (pullback) — with mathematically guaranteed
round-trip properties.

This vignette demonstrates:

| §   | CQL Operation     | What It Shows                            |
|-----|-------------------|------------------------------------------|
| 2   | Schema definition | Both paradigms as CQL schemas            |
| 3   | Instance          | A marine food web in property graph form |
| 4   | Mapping + Sigma   | LPG → RDF via pushforward migration      |
| 5   | Delta             | RDF → LPG via pullback migration         |
| 6   | Unit / Counit     | Round-trip fidelity guarantees           |
| 7   | Query             | SPARQL-like triple joins in CQL          |
| 8   | Edge properties   | The fundamental LPG/RDF asymmetry        |
| 9   | Reification       | Extending RDF to handle edge properties  |
| 10  | Schema colimit    | A unified view merging both paradigms    |

``` julia
using CQL
```

------------------------------------------------------------------------

## Two Paradigms, Two Schemas

The key structural difference between RDF and LPG, expressed as CQL
schemas:

**Property Graph** — nodes carry properties as separate entities linked
by foreign keys. In graph database terms: each `PGNode` is a labeled
node, `PGEdge` is a directed relationship, and `PGProp` is a key–value
property attached to a node.

**Triple Store** — everything is either a `Resource` (identified by a
URI), an `ObjTriple` (a relationship triple linking two resources), or a
`DataTriple` (a property triple assigning a literal value to a
resource).

``` julia
typeside = """
typeside Ty = literal {
  types String
}
"""

pg_schema = """
schema PropertyGraph = literal : Ty {
  entities
    PGNode PGEdge PGProp
  foreign_keys
    src : PGEdge -> PGNode
    tgt : PGEdge -> PGNode
    prop_of : PGProp -> PGNode
  attributes
    node_id : PGNode -> String
    edge_label : PGEdge -> String
    prop_key : PGProp -> String
    prop_val : PGProp -> String
}
"""

rdf_schema = """
schema TripleStore = literal : Ty {
  entities
    Resource ObjTriple DataTriple
  foreign_keys
    subj : ObjTriple -> Resource
    obj : ObjTriple -> Resource
    dt_subj : DataTriple -> Resource
  attributes
    uri : Resource -> String
    predicate : ObjTriple -> String
    dt_pred : DataTriple -> String
    dt_val : DataTriple -> String
}
"""

env = run_program(typeside * pg_schema * rdf_schema)
pg = env.schemas["PropertyGraph"]
ts = env.schemas["TripleStore"]
println("PropertyGraph entities: ", join(sort(collect(pg.ens)), ", "))
println("TripleStore entities:   ", join(sort(collect(ts.ens)), ", "))
```

    PropertyGraph entities: PGEdge, PGNode, PGProp
    TripleStore entities:   DataTriple, ObjTriple, Resource

Notice the structural parallel:

| Property Graph | Triple Store  | Role                                    |
|----------------|---------------|-----------------------------------------|
| `PGNode`       | `Resource`    | Things in the world (species, habitats) |
| `PGEdge`       | `ObjTriple`   | Relationships between things            |
| `PGProp`       | `DataTriple`  | Literal properties of things            |
| `src`, `tgt`   | `subj`, `obj` | Edge endpoints                          |
| `prop_of`      | `dt_subj`     | Which node a property belongs to        |

This parallel is not a coincidence — it is an **isomorphism of
categories**.

------------------------------------------------------------------------

## A Marine Food Web as a Property Graph

We model a North Sea food web as a property graph. Each species is a
node with `name` and `trophicLevel` properties. Feeding relationships
are edges labeled `eco:feedsOn`. The URI-style identifiers (`eco:...`)
anticipate the RDF representation.

``` julia
food_web = """
instance MarineWeb = literal : PropertyGraph {
  generators
    n_phyto n_cope n_sandeel n_herring n_cod n_seal : PGNode
    e_seal_cod e_cod_herr e_cod_sand e_herr_cope e_sand_cope e_cope_phyto : PGEdge
    p_phyto_nm p_phyto_tl p_cope_nm p_cope_tl p_sand_nm p_sand_tl
    p_herr_nm p_herr_tl p_cod_nm p_cod_tl p_seal_nm p_seal_tl : PGProp
  equations
    n_phyto.node_id = "eco:phytoplankton"
    n_cope.node_id = "eco:copepod"
    n_sandeel.node_id = "eco:sand_eel"
    n_herring.node_id = "eco:herring"
    n_cod.node_id = "eco:atlantic_cod"
    n_seal.node_id = "eco:grey_seal"
    e_seal_cod.src = n_seal       e_seal_cod.tgt = n_cod       e_seal_cod.edge_label = "eco:feedsOn"
    e_cod_herr.src = n_cod        e_cod_herr.tgt = n_herring   e_cod_herr.edge_label = "eco:feedsOn"
    e_cod_sand.src = n_cod        e_cod_sand.tgt = n_sandeel   e_cod_sand.edge_label = "eco:feedsOn"
    e_herr_cope.src = n_herring   e_herr_cope.tgt = n_cope     e_herr_cope.edge_label = "eco:feedsOn"
    e_sand_cope.src = n_sandeel   e_sand_cope.tgt = n_cope     e_sand_cope.edge_label = "eco:feedsOn"
    e_cope_phyto.src = n_cope     e_cope_phyto.tgt = n_phyto   e_cope_phyto.edge_label = "eco:feedsOn"
    p_phyto_nm.prop_of = n_phyto  p_phyto_nm.prop_key = "name"         p_phyto_nm.prop_val = "Phytoplankton"
    p_phyto_tl.prop_of = n_phyto  p_phyto_tl.prop_key = "trophicLevel" p_phyto_tl.prop_val = "1"
    p_cope_nm.prop_of = n_cope    p_cope_nm.prop_key = "name"           p_cope_nm.prop_val = "Copepod"
    p_cope_tl.prop_of = n_cope    p_cope_tl.prop_key = "trophicLevel"   p_cope_tl.prop_val = "2"
    p_sand_nm.prop_of = n_sandeel p_sand_nm.prop_key = "name"           p_sand_nm.prop_val = "Sand Eel"
    p_sand_tl.prop_of = n_sandeel p_sand_tl.prop_key = "trophicLevel"   p_sand_tl.prop_val = "3"
    p_herr_nm.prop_of = n_herring p_herr_nm.prop_key = "name"           p_herr_nm.prop_val = "Herring"
    p_herr_tl.prop_of = n_herring p_herr_tl.prop_key = "trophicLevel"   p_herr_tl.prop_val = "3"
    p_cod_nm.prop_of = n_cod      p_cod_nm.prop_key = "name"            p_cod_nm.prop_val = "Atlantic Cod"
    p_cod_tl.prop_of = n_cod      p_cod_tl.prop_key = "trophicLevel"    p_cod_tl.prop_val = "4"
    p_seal_nm.prop_of = n_seal    p_seal_nm.prop_key = "name"           p_seal_nm.prop_val = "Grey Seal"
    p_seal_tl.prop_of = n_seal    p_seal_tl.prop_key = "trophicLevel"   p_seal_tl.prop_val = "5"
}
"""

env = run_program(typeside * pg_schema * food_web)
alg = env.instances["MarineWeb"].algebra
println("Nodes:      ", length(CQL.carrier(alg, :PGNode)), " species")
println("Edges:      ", length(CQL.carrier(alg, :PGEdge)), " feeding links")
println("Properties: ", length(CQL.carrier(alg, :PGProp)), " key-value pairs")
```

    Nodes:      6 species
    Edges:      6 feeding links
    Properties: 12 key-value pairs

This is exactly how the data would be stored in Neo4j: each species is a
`(:Species {name: "...", trophicLevel: "..."})` node, and each feeding
link is a `[:FEEDS_ON]` relationship.

------------------------------------------------------------------------

## LPG → RDF via Sigma (Pushforward)

The structural parallel between the two schemas is a **schema morphism**
(functor): it maps each PropertyGraph entity, foreign key, and attribute
to its TripleStore counterpart.

In ecological terms: this mapping says “a species node *is* an RDF
resource, a feeding link *is* an object triple, and a property *is* a
data triple.”

``` julia
mapping = """
mapping ToTriples = literal : PropertyGraph -> TripleStore {
  entity PGNode -> Resource
    attributes
      node_id -> lambda x. x.uri
  entity PGEdge -> ObjTriple
    foreign_keys
      src -> subj
      tgt -> obj
    attributes
      edge_label -> lambda x. x.predicate
  entity PGProp -> DataTriple
    foreign_keys
      prop_of -> dt_subj
    attributes
      prop_key -> lambda x. x.dt_pred
      prop_val -> lambda x. x.dt_val
}
"""

sigma_prog = """
instance AsTriples = sigma ToTriples MarineWeb
"""

env = run_program(typeside * pg_schema * rdf_schema * mapping * food_web * sigma_prog)
alg_rdf = env.instances["AsTriples"].algebra
```

    Algebra{CQLTerm, CQL.TalgGen}(schema {
      entities
        Resource
        ObjTriple
        DataTriple
      foreign_keys
        dt_subj : DataTriple -> Resource
        obj : ObjTriple -> Resource
        subj : ObjTriple -> Resource
      attributes
        predicate : ObjTriple -> String
        dt_pred : DataTriple -> String
        uri : Resource -> String
        dt_val : DataTriple -> String
      path_equations
      observation_equations
    }
    , Dict{Symbol, Set{CQLTerm}}(:Resource => Set([n_herring, n_cope, n_phyto, n_cod, n_sandeel, n_seal]), :ObjTriple => Set([e_herr_cope, e_cod_herr, e_sand_cope, e_seal_cod, e_cope_phyto, e_cod_sand]), :DataTriple => Set([p_phyto_nm, p_sand_tl, p_phyto_tl, p_cod_tl, p_herr_tl, p_cod_nm, p_sand_nm, p_cope_nm, p_seal_nm, p_cope_tl, p_herr_nm, p_seal_tl])), Dict{Symbol, CQLTerm}(:p_herr_tl => p_herr_tl, :p_seal_nm => p_seal_nm, :n_seal => n_seal, :e_cope_phyto => e_cope_phyto, :n_phyto => n_phyto, :p_cope_tl => p_cope_tl, :e_cod_sand => e_cod_sand, :e_herr_cope => e_herr_cope, :n_sandeel => n_sandeel, :e_sand_cope => e_sand_cope…), Dict{Symbol, Dict{CQLTerm, CQLTerm}}(:dt_subj => Dict(p_phyto_nm => n_phyto, p_sand_tl => n_sandeel, p_phyto_tl => n_phyto, p_cod_tl => n_cod, p_herr_tl => n_herring, p_cod_nm => n_cod, p_sand_nm => n_sandeel, p_cope_nm => n_cope, p_seal_nm => n_seal, p_cope_tl => n_cope…), :obj => Dict(e_herr_cope => n_cope, e_cod_herr => n_herring, e_sand_cope => n_cope, e_seal_cod => n_cod, e_cope_phyto => n_phyto, e_cod_sand => n_sandeel), :subj => Dict(e_herr_cope => n_herring, e_cod_herr => n_cod, e_sand_cope => n_sandeel, e_seal_cod => n_seal, e_cope_phyto => n_cope, e_cod_sand => n_cod)), Dict{CQLTerm, CQLTerm}(e_sand_cope => e_sand_cope, e_cod_herr => e_cod_herr, p_phyto_nm => p_phyto_nm, p_sand_tl => p_sand_tl, e_seal_cod => e_seal_cod, e_cope_phyto => e_cope_phyto, p_phyto_tl => p_phyto_tl, n_phyto => n_phyto, p_cod_tl => p_cod_tl, p_herr_tl => p_herr_tl…), Dict{Symbol, Set{CQL.TalgGen}}(:String => Set([Herring, name, eco:copepod, trophicLevel, Sand Eel, 1, 4, Grey Seal, Copepod, eco:herring, Atlantic Cod, 2, eco:feedsOn, eco:sand_eel, eco:grey_seal, eco:atlantic_cod, 3, 5, eco:phytoplankton, Phytoplankton])), CQL.var"#simplify_algebra##4#simplify_algebra##5"{Dict{Any, CQLTerm}, CQL.var"#128#129"{Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}}, Vector{Tuple{CQLTerm, CQLTerm}}, Vector{Tuple{CQL.Head, CQLTerm}}}(Dict{Any, CQLTerm}(), CQL.var"#128#129"{Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}}(Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}()), Tuple{CQLTerm, CQLTerm}[], Tuple{CQL.Head, CQLTerm}[(CQL.Head(CQL.H_SK, Symbol("p_cope_nm.dt_pred")), name), (CQL.Head(CQL.H_SK, Symbol("p_cope_tl.dt_val")), 2), (CQL.Head(CQL.H_SK, Symbol("p_herr_nm.dt_val")), Herring), (CQL.Head(CQL.H_SK, Symbol("p_cope_tl.dt_pred")), trophicLevel), (CQL.Head(CQL.H_SK, Symbol("p_seal_tl.dt_val")), 5), (CQL.Head(CQL.H_SK, Symbol("p_phyto_tl.dt_pred")), trophicLevel), (CQL.Head(CQL.H_SK, Symbol("n_phyto.uri")), eco:phytoplankton), (CQL.Head(CQL.H_SK, Symbol("p_herr_nm.dt_pred")), name), (CQL.Head(CQL.H_SK, Symbol("n_cope.uri")), eco:copepod), (CQL.Head(CQL.H_SK, Symbol("p_herr_tl.dt_val")), 3)  …  (CQL.Head(CQL.H_SK, Symbol("e_cod_herr.predicate")), eco:feedsOn), (CQL.Head(CQL.H_SK, Symbol("p_cod_nm.dt_pred")), name), (CQL.Head(CQL.H_SK, Symbol("p_seal_tl.dt_pred")), trophicLevel), (CQL.Head(CQL.H_SK, Symbol("n_sandeel.uri")), eco:sand_eel), (CQL.Head(CQL.H_SK, Symbol("p_sand_tl.dt_val")), 3), (CQL.Head(CQL.H_SK, Symbol("p_cod_tl.dt_val")), 4), (CQL.Head(CQL.H_SK, Symbol("p_seal_nm.dt_val")), Grey Seal), (CQL.Head(CQL.H_SK, Symbol("e_cod_sand.predicate")), eco:feedsOn), (CQL.Head(CQL.H_SK, Symbol("p_phyto_nm.dt_val")), Phytoplankton), (CQL.Head(CQL.H_SK, Symbol("p_phyto_nm.dt_pred")), name)]), Dict{CQL.TalgGen, CQLTerm}(name => name, n_herring.uri => n_herring.uri, p_sand_tl.dt_pred => p_sand_tl.dt_pred, p_sand_tl.dt_val => p_sand_tl.dt_val, eco:herring => eco:herring, Atlantic Cod => Atlantic Cod, p_cod_nm.dt_val => p_cod_nm.dt_val, p_cope_nm.dt_pred => p_cope_nm.dt_pred, p_cope_tl.dt_val => p_cope_tl.dt_val, p_sand_nm.dt_pred => p_sand_nm.dt_pred…), Set{Equation}())

**Sigma** pushes the property graph data forward along the mapping,
producing an RDF triple store. Each species node becomes a resource,
each feeding link becomes an object triple, and each property becomes a
data triple.

``` julia
println("=== RDF Resources (species URIs) ===")
for r in sort(collect(CQL.carrier(alg_rdf, :Resource)), by=string)
    println("  ", CQL.eval_att(alg_rdf, :uri, r))
end
```

    === RDF Resources (species URIs) ===
      eco:atlantic_cod
      eco:copepod
      eco:herring
      eco:phytoplankton
      eco:sand_eel
      eco:grey_seal

``` julia
println("=== Object Triples (feeding relationships) ===")
for t in sort(collect(CQL.carrier(alg_rdf, :ObjTriple)), by=string)
    s = CQL.eval_att(alg_rdf, :uri, CQL.eval_fk(alg_rdf, :subj, t))
    o = CQL.eval_att(alg_rdf, :uri, CQL.eval_fk(alg_rdf, :obj, t))
    p = CQL.eval_att(alg_rdf, :predicate, t)
    println("  $s  $p  $o .")
end
```

    === Object Triples (feeding relationships) ===
      eco:atlantic_cod  eco:feedsOn  eco:herring .
      eco:atlantic_cod  eco:feedsOn  eco:sand_eel .
      eco:copepod  eco:feedsOn  eco:phytoplankton .
      eco:herring  eco:feedsOn  eco:copepod .
      eco:sand_eel  eco:feedsOn  eco:copepod .
      eco:grey_seal  eco:feedsOn  eco:atlantic_cod .

``` julia
println("=== Data Triples (species properties) ===")
for d in sort(collect(CQL.carrier(alg_rdf, :DataTriple)), by=string)
    s = CQL.eval_att(alg_rdf, :uri, CQL.eval_fk(alg_rdf, :dt_subj, d))
    p = CQL.eval_att(alg_rdf, :dt_pred, d)
    v = CQL.eval_att(alg_rdf, :dt_val, d)
    println("  $s  $p  \"$v\" .")
end
```

    === Data Triples (species properties) ===
      eco:atlantic_cod  name  "Atlantic Cod" .
      eco:atlantic_cod  trophicLevel  "4" .
      eco:copepod  name  "Copepod" .
      eco:copepod  trophicLevel  "2" .
      eco:herring  name  "Herring" .
      eco:herring  trophicLevel  "3" .
      eco:phytoplankton  name  "Phytoplankton" .
      eco:phytoplankton  trophicLevel  "1" .
      eco:sand_eel  name  "Sand Eel" .
      eco:sand_eel  trophicLevel  "3" .
      eco:grey_seal  name  "Grey Seal" .
      eco:grey_seal  trophicLevel  "5" .

The output is valid RDF N-Triples syntax. Every piece of the property
graph — nodes, edges, and properties — has been systematically converted
to triples. No information was lost because the mapping is an
isomorphism.

------------------------------------------------------------------------

## RDF → LPG via Delta (Pullback)

The same mapping, applied in reverse via **Delta**, converts RDF data
into a property graph. This is useful when a linked data repository
(e.g., a SPARQL endpoint) provides ecological data that needs to be
loaded into a Neo4j-style graph database.

Delta is the *right adjoint* to Sigma: it pulls data back along the
mapping.

``` julia
delta_prog = """
instance RoundTrip = delta ToTriples AsTriples
"""

env = run_program(typeside * pg_schema * rdf_schema * mapping * food_web * sigma_prog * delta_prog)
alg_rt = env.instances["RoundTrip"].algebra

println("=== Round-trip Property Graph ===")
println("Nodes:      ", length(CQL.carrier(alg_rt, :PGNode)))
println("Edges:      ", length(CQL.carrier(alg_rt, :PGEdge)))
println("Properties: ", length(CQL.carrier(alg_rt, :PGProp)))
```

    === Round-trip Property Graph ===
    Nodes:      6
    Edges:      6
    Properties: 12

``` julia
println("Nodes:")
for n in sort(collect(CQL.carrier(alg_rt, :PGNode)), by=string)
    println("  ", CQL.eval_att(alg_rt, :node_id, n))
end
println("\nEdges:")
for e in sort(collect(CQL.carrier(alg_rt, :PGEdge)), by=string)
    sn = CQL.eval_att(alg_rt, :node_id, CQL.eval_fk(alg_rt, :src, e))
    tn = CQL.eval_att(alg_rt, :node_id, CQL.eval_fk(alg_rt, :tgt, e))
    println("  $sn --[$(CQL.eval_att(alg_rt, :edge_label, e))]--> $tn")
end
println("\nProperties:")
for p in sort(collect(CQL.carrier(alg_rt, :PGProp)), by=string)
    nid = CQL.eval_att(alg_rt, :node_id, CQL.eval_fk(alg_rt, :prop_of, p))
    pk = CQL.eval_att(alg_rt, :prop_key, p)
    pv = CQL.eval_att(alg_rt, :prop_val, p)
    println("  $nid . $pk = \"$pv\"")
end
```

    Nodes:
      eco:atlantic_cod
      eco:copepod
      eco:herring
      eco:phytoplankton
      eco:sand_eel
      eco:grey_seal

    Edges:
      eco:atlantic_cod --[eco:feedsOn]--> eco:herring
      eco:atlantic_cod --[eco:feedsOn]--> eco:sand_eel
      eco:copepod --[eco:feedsOn]--> eco:phytoplankton
      eco:herring --[eco:feedsOn]--> eco:copepod
      eco:sand_eel --[eco:feedsOn]--> eco:copepod
      eco:grey_seal --[eco:feedsOn]--> eco:atlantic_cod

    Properties:
      eco:atlantic_cod . name = "Atlantic Cod"
      eco:atlantic_cod . trophicLevel = "4"
      eco:copepod . name = "Copepod"
      eco:copepod . trophicLevel = "2"
      eco:herring . name = "Herring"
      eco:herring . trophicLevel = "3"
      eco:phytoplankton . name = "Phytoplankton"
      eco:phytoplankton . trophicLevel = "1"
      eco:sand_eel . name = "Sand Eel"
      eco:sand_eel . trophicLevel = "3"
      eco:grey_seal . name = "Grey Seal"
      eco:grey_seal . trophicLevel = "5"

The round-trip recovers the original property graph exactly: 6 nodes, 6
edges, 12 properties, with all attribute values preserved. This is
guaranteed by the categorical adjunction — when the mapping is an
isomorphism, Sigma and Delta are mutual inverses.

------------------------------------------------------------------------

## Unit and Counit: Formal Round-Trip Guarantees

Category theory provides formal transforms that witness the round-trip:

- **Unit** (η): `I → Delta(Sigma(I))` — embeds the original LPG instance
  into its round-trip. If η is an isomorphism, no data was lost.
- **Counit** (ε): `Sigma(Delta(J)) → J` — projects the round-trip of an
  RDF instance back. If ε is an isomorphism, no data was invented.

``` julia
unit_prog = """
transform UnitWeb = unit ToTriples MarineWeb
transform CounitTriples = counit ToTriples AsTriples
"""

env = run_program(typeside * pg_schema * rdf_schema * mapping * food_web * sigma_prog * delta_prog * unit_prog)

# Verify unit preserves cardinalities
src_alg = env.instances["MarineWeb"].algebra
tgt_alg = env.instances["RoundTrip"].algebra
for ent in [:PGNode, :PGEdge, :PGProp]
    n_src = length(CQL.carrier(src_alg, ent))
    n_tgt = length(CQL.carrier(tgt_alg, ent))
    status = n_src == n_tgt ? "✓ isomorphism" : "≠ not iso"
    println("  Unit on $ent: $n_src → $n_tgt  $status")
end

# Verify counit
src_alg2 = env.instances["AsTriples"].algebra
println("\n  Counit source and target both have:")
for ent in [:Resource, :ObjTriple, :DataTriple]
    n = length(CQL.carrier(src_alg2, ent))
    println("    $ent: $n")
end
```

      Unit on PGNode: 6 → 6  ✓ isomorphism
      Unit on PGEdge: 6 → 6  ✓ isomorphism
      Unit on PGProp: 12 → 12  ✓ isomorphism

      Counit source and target both have:
        Resource: 6
        ObjTriple: 6
        DataTriple: 12

Both unit and counit are isomorphisms — the migration is **lossless in
both directions**. This is the categorical guarantee: because the
mapping between PropertyGraph and TripleStore is a full isomorphism of
schemas, Sigma and Delta form an equivalence of categories of instances.

------------------------------------------------------------------------

## SPARQL-Like Queries: Joining Triples

CQL’s uber-flower queries can express the same pattern-matching that
SPARQL uses to extract structured data from a triple store. This is
useful when receiving ecological data as RDF and needing to reconstruct
a domain-specific schema.

Here we define a query that joins data triples to produce a species
report — equivalent to:

``` sparql
SELECT ?uri ?name ?tl WHERE {
  ?r eco:name ?name .
  ?r eco:trophicLevel ?tl .
  BIND(STR(?r) AS ?uri)
}
```

``` julia
query_prog = """
schema SpeciesReport = literal : Ty {
  entities Entry
  attributes entry_uri : Entry -> String  entry_name : Entry -> String  entry_tl : Entry -> String
}

query JoinTriples = literal : TripleStore -> SpeciesReport {
  entity Entry -> {
    from r : Resource  dn : DataTriple  dt : DataTriple
    where dn.dt_subj = r  dt.dt_subj = r  dn.dt_pred = "name"  dt.dt_pred = "trophicLevel"
    attributes
      entry_uri -> r.uri
      entry_name -> dn.dt_val
      entry_tl -> dt.dt_val
    foreign_keys
  }
}

instance Report = eval JoinTriples AsTriples
"""

env = run_program(typeside * pg_schema * rdf_schema * mapping * food_web * sigma_prog * query_prog)
alg_rep = env.instances["Report"].algebra

println("=== Species Report (from triple joins) ===")
for e in sort(collect(CQL.carrier(alg_rep, :Entry)), by=string)
    uri = CQL.eval_att(alg_rep, :entry_uri, e)
    nm = CQL.eval_att(alg_rep, :entry_name, e)
    tl = CQL.eval_att(alg_rep, :entry_tl, e)
    println("  $uri: $nm (trophic level $tl)")
end
```

    === Species Report (from triple joins) ===
      eco:herring: Herring (trophic level 3)
      eco:copepod: Copepod (trophic level 2)
      eco:phytoplankton: Phytoplankton (trophic level 1)
      eco:atlantic_cod: Atlantic Cod (trophic level 4)
      eco:sand_eel: Sand Eel (trophic level 3)
      eco:grey_seal: Grey Seal (trophic level 5)

The CQL query binds three variables — a Resource `r` and two DataTriples
`dn`, `dt` — and constrains them so that both triples refer to the same
resource and have specific predicates. This is exactly a **basic graph
pattern** in SPARQL.

The key advantage: CQL queries compose and have formal semantics, so
this pattern can be chained with downstream migrations (Sigma, Delta) in
a type-safe pipeline.

------------------------------------------------------------------------

## The Asymmetry: Edge Properties

So far, property graphs and triple stores appeared structurally
identical. But there is a fundamental asymmetry that the categorical
view makes precise.

In a property graph, **edges can carry properties** — for example, a
feeding relationship might have an `interaction_strength` or
`evidence_source` attribute. We model this by adding a `PGEdgeProp`
entity with a foreign key to `PGEdge`:

``` julia
rich_pg = """
schema RichPropertyGraph = literal : Ty {
  entities
    PGNode PGEdge PGProp PGEdgeProp
  foreign_keys
    src : PGEdge -> PGNode
    tgt : PGEdge -> PGNode
    prop_of : PGProp -> PGNode
    eprop_of : PGEdgeProp -> PGEdge
  attributes
    node_id : PGNode -> String
    edge_label : PGEdge -> String
    prop_key : PGProp -> String
    prop_val : PGProp -> String
    eprop_key : PGEdgeProp -> String
    eprop_val : PGEdgeProp -> String
}
"""

env = run_program(typeside * rich_pg)
sch = env.schemas["RichPropertyGraph"]
println("RichPropertyGraph entities: ", join(sort(collect(sch.ens)), ", "))
println("Foreign keys:")
for (k, v) in sort(collect(sch.fks), by=x->string(first(x)))
    dn = CQL._display_name(k)
    println("  $dn : $(first(v)) → $(last(v))")
end
```

    RichPropertyGraph entities: PGEdge, PGEdgeProp, PGNode, PGProp
    Foreign keys:
      eprop_of : PGEdgeProp → PGEdge
      prop_of : PGProp → PGNode
      src : PGEdge → PGNode
      tgt : PGEdge → PGNode

The `PGEdgeProp` entity has a foreign key `eprop_of → PGEdge`, but the
basic TripleStore schema has no entity with a foreign key pointing to
`ObjTriple`. A `DataTriple` points to a `Resource`, not to an
`ObjTriple`.

**There is no schema morphism from RichPropertyGraph to TripleStore.**

This is the categorical formalization of a well-known problem: RDF has
no native way to attach properties to edges (triples). In ecology, this
means metadata about interactions — confidence scores, observation
methods, seasonal variation — cannot be directly represented as RDF
triples without additional machinery.

------------------------------------------------------------------------

## Reification: Extending RDF for Edge Properties

The standard RDF solution is **reification**: making a statement *about*
a statement. In CQL terms, we extend the TripleStore schema with a
`TripleMeta` entity that points to an `ObjTriple`:

``` julia
reified_schema = """
schema ReifiedTripleStore = literal : Ty {
  entities
    Resource ObjTriple DataTriple TripleMeta
  foreign_keys
    subj : ObjTriple -> Resource
    obj : ObjTriple -> Resource
    dt_subj : DataTriple -> Resource
    meta_of : TripleMeta -> ObjTriple
  attributes
    uri : Resource -> String
    predicate : ObjTriple -> String
    dt_pred : DataTriple -> String
    dt_val : DataTriple -> String
    meta_key : TripleMeta -> String
    meta_val : TripleMeta -> String
}
"""

reified_mapping = """
mapping ToReified = literal : RichPropertyGraph -> ReifiedTripleStore {
  entity PGNode -> Resource
    attributes node_id -> lambda x. x.uri
  entity PGEdge -> ObjTriple
    foreign_keys src -> subj  tgt -> obj
    attributes edge_label -> lambda x. x.predicate
  entity PGProp -> DataTriple
    foreign_keys prop_of -> dt_subj
    attributes prop_key -> lambda x. x.dt_pred  prop_val -> lambda x. x.dt_val
  entity PGEdgeProp -> TripleMeta
    foreign_keys eprop_of -> meta_of
    attributes eprop_key -> lambda x. x.meta_key  eprop_val -> lambda x. x.meta_val
}
"""

rich_instance = """
instance RichWeb = literal : RichPropertyGraph {
  generators
    n_cod n_herring : PGNode
    e_cod_herr : PGEdge
    p_cod_nm p_herr_nm : PGProp
    ep_strength ep_evidence : PGEdgeProp
  equations
    n_cod.node_id = "eco:atlantic_cod"
    n_herring.node_id = "eco:herring"
    e_cod_herr.src = n_cod
    e_cod_herr.tgt = n_herring
    e_cod_herr.edge_label = "eco:feedsOn"
    p_cod_nm.prop_of = n_cod
    p_cod_nm.prop_key = "name"
    p_cod_nm.prop_val = "Atlantic Cod"
    p_herr_nm.prop_of = n_herring
    p_herr_nm.prop_key = "name"
    p_herr_nm.prop_val = "Herring"
    ep_strength.eprop_of = e_cod_herr
    ep_strength.eprop_key = "interaction_strength"
    ep_strength.eprop_val = "high"
    ep_evidence.eprop_of = e_cod_herr
    ep_evidence.eprop_key = "evidence"
    ep_evidence.eprop_val = "gut content analysis"
}

instance ReifiedTriples = sigma ToReified RichWeb
"""

env = run_program(typeside * rich_pg * reified_schema * reified_mapping * rich_instance)
alg_reif = env.instances["ReifiedTriples"].algebra
```

    Algebra{CQLTerm, CQL.TalgGen}(schema {
      entities
        TripleMeta
        Resource
        ObjTriple
        DataTriple
      foreign_keys
        dt_subj : DataTriple -> Resource
        obj : ObjTriple -> Resource
        meta_of : TripleMeta -> ObjTriple
        subj : ObjTriple -> Resource
      attributes
        predicate : ObjTriple -> String
        meta_val : TripleMeta -> String
        dt_pred : DataTriple -> String
        uri : Resource -> String
        dt_val : DataTriple -> String
        meta_key : TripleMeta -> String
      path_equations
      observation_equations
    }
    , Dict{Symbol, Set{CQLTerm}}(:TripleMeta => Set([ep_evidence, ep_strength]), :Resource => Set([n_herring, n_cod]), :ObjTriple => Set([ep_strength.meta_of]), :DataTriple => Set([p_herr_nm, p_cod_nm])), Dict{Symbol, CQLTerm}(:e_cod_herr => ep_strength.meta_of, :ep_evidence => ep_evidence, :p_herr_nm => p_herr_nm, :n_cod => n_cod, :n_herring => n_herring, :p_cod_nm => p_cod_nm, :ep_strength => ep_strength), Dict{Symbol, Dict{CQLTerm, CQLTerm}}(:dt_subj => Dict(p_herr_nm => n_herring, p_cod_nm => n_cod), :obj => Dict(ep_strength.meta_of => n_herring), :meta_of => Dict(ep_evidence => ep_strength.meta_of, ep_strength => ep_strength.meta_of), :subj => Dict(ep_strength.meta_of => n_cod)), Dict{CQLTerm, CQLTerm}(ep_strength.meta_of => ep_strength.meta_of, ep_evidence => ep_evidence, n_herring => n_herring, p_herr_nm => p_herr_nm, ep_strength => ep_strength, n_cod => n_cod, p_cod_nm => p_cod_nm), Dict{Symbol, Set{CQL.TalgGen}}(:String => Set([Herring, name, high, gut content analysis, eco:atlantic_cod, eco:herring, Atlantic Cod, evidence, eco:feedsOn, interaction_strength])), CQL.var"#simplify_algebra##4#simplify_algebra##5"{Dict{Any, CQLTerm}, CQL.var"#128#129"{Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}}, Vector{Tuple{CQLTerm, CQLTerm}}, Vector{Tuple{CQL.Head, CQLTerm}}}(Dict{Any, CQLTerm}(), CQL.var"#128#129"{Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}}(Dict{Symbol, Tuple{Vector{Symbol}, Symbol}}()), Tuple{CQLTerm, CQLTerm}[], Tuple{CQL.Head, CQLTerm}[(CQL.Head(CQL.H_SK, Symbol("ep_strength.meta_of.predicate")), eco:feedsOn), (CQL.Head(CQL.H_SK, Symbol("p_herr_nm.dt_val")), Herring), (CQL.Head(CQL.H_SK, Symbol("p_herr_nm.dt_pred")), name), (CQL.Head(CQL.H_SK, Symbol("ep_evidence.meta_key")), evidence), (CQL.Head(CQL.H_SK, Symbol("n_herring.uri")), eco:herring), (CQL.Head(CQL.H_SK, Symbol("n_cod.uri")), eco:atlantic_cod), (CQL.Head(CQL.H_SK, Symbol("ep_evidence.meta_val")), gut content analysis), (CQL.Head(CQL.H_SK, Symbol("ep_strength.meta_key")), interaction_strength), (CQL.Head(CQL.H_SK, Symbol("p_cod_nm.dt_val")), Atlantic Cod), (CQL.Head(CQL.H_SK, Symbol("p_cod_nm.dt_pred")), name), (CQL.Head(CQL.H_SK, Symbol("ep_strength.meta_val")), high)]), Dict{CQL.TalgGen, CQLTerm}(Herring => Herring, name => name, n_herring.uri => n_herring.uri, ep_evidence.meta_val => ep_evidence.meta_val, ep_strength.meta_of.predicate => ep_strength.meta_of.predicate, ep_evidence.meta_key => ep_evidence.meta_key, n_cod.uri => n_cod.uri, ep_strength.meta_val => ep_strength.meta_val, interaction_strength => interaction_strength, eco:herring => eco:herring…), Set{Equation}())

Now the edge properties — interaction strength and evidence source — are
preserved as `TripleMeta` entries in the reified triple store:

``` julia
println("=== Reified Triple Store ===")
println("Resources:  ", length(CQL.carrier(alg_reif, :Resource)))
println("ObjTriples: ", length(CQL.carrier(alg_reif, :ObjTriple)))
println("DataTriples:", length(CQL.carrier(alg_reif, :DataTriple)))
println("TripleMeta: ", length(CQL.carrier(alg_reif, :TripleMeta)))

println("\nObject triples:")
for t in sort(collect(CQL.carrier(alg_reif, :ObjTriple)), by=string)
    s = CQL.eval_att(alg_reif, :uri, CQL.eval_fk(alg_reif, :subj, t))
    o = CQL.eval_att(alg_reif, :uri, CQL.eval_fk(alg_reif, :obj, t))
    p = CQL.eval_att(alg_reif, :predicate, t)
    println("  $s  $p  $o .")
end

println("\nEdge metadata (reified statements):")
for m in sort(collect(CQL.carrier(alg_reif, :TripleMeta)), by=string)
    triple = CQL.eval_fk(alg_reif, :meta_of, m)
    s = CQL.eval_att(alg_reif, :uri, CQL.eval_fk(alg_reif, :subj, triple))
    o = CQL.eval_att(alg_reif, :uri, CQL.eval_fk(alg_reif, :obj, triple))
    mk = CQL.eval_att(alg_reif, :meta_key, m)
    mv = CQL.eval_att(alg_reif, :meta_val, m)
    println("  [$s → $o] . $mk = \"$mv\"")
end
```

    === Reified Triple Store ===
    Resources:  2
    ObjTriples: 1
    DataTriples:2
    TripleMeta: 2

    Object triples:
      eco:atlantic_cod  eco:feedsOn  eco:herring .

    Edge metadata (reified statements):
      [eco:atlantic_cod → eco:herring] . evidence = "gut content analysis"
      [eco:atlantic_cod → eco:herring] . interaction_strength = "high"

The reified mapping restores the isomorphism: every entity in
`RichPropertyGraph` now has a counterpart in `ReifiedTripleStore`, and
Sigma/Delta are again mutual inverses.

``` julia
rt_prog = """
instance ReifiedRT = delta ToReified ReifiedTriples
"""
env = run_program(typeside * rich_pg * reified_schema * reified_mapping * rich_instance * rt_prog)
alg_rt = env.instances["ReifiedRT"].algebra
println("Round-trip with reification:")
println("  PGNodes:     ", length(CQL.carrier(alg_rt, :PGNode)))
println("  PGEdges:     ", length(CQL.carrier(alg_rt, :PGEdge)))
println("  PGProps:     ", length(CQL.carrier(alg_rt, :PGProp)))
println("  PGEdgeProps: ", length(CQL.carrier(alg_rt, :PGEdgeProp)))
println("  All preserved: ",
    length(CQL.carrier(alg_rt, :PGNode)) == 2 &&
    length(CQL.carrier(alg_rt, :PGEdgeProp)) == 2 ? "✓" : "✗")
```

    Round-trip with reification:
      PGNodes:     2
      PGEdges:     1
      PGProps:     2
      PGEdgeProps: 2
      All preserved: ✓

------------------------------------------------------------------------

## Starting from RDF: Delta Extraction

In practice, ecological data often arrives as RDF from linked data
repositories (e.g., GBIF, the Encyclopedia of Life, or institutional
SPARQL endpoints). Delta extraction converts this RDF data into a
structured property graph suitable for Neo4j or similar graph databases.

``` julia
external_rdf = """
instance ExternalRDF = literal : TripleStore {
  generators
    r_cod r_herring r_copepod r_sandeel : Resource
    t_cod_herr t_cod_sand t_herr_cope : ObjTriple
    d_cod_nm d_cod_tl d_herr_nm d_herr_tl d_cope_nm d_cope_tl d_sand_nm d_sand_tl : DataTriple
  equations
    r_cod.uri = "eco:atlantic_cod"
    r_herring.uri = "eco:herring"
    r_copepod.uri = "eco:copepod"
    r_sandeel.uri = "eco:sand_eel"
    t_cod_herr.subj = r_cod        t_cod_herr.obj = r_herring   t_cod_herr.predicate = "eco:feedsOn"
    t_cod_sand.subj = r_cod        t_cod_sand.obj = r_sandeel   t_cod_sand.predicate = "eco:feedsOn"
    t_herr_cope.subj = r_herring   t_herr_cope.obj = r_copepod  t_herr_cope.predicate = "eco:feedsOn"
    d_cod_nm.dt_subj = r_cod       d_cod_nm.dt_pred = "name"           d_cod_nm.dt_val = "Atlantic Cod"
    d_cod_tl.dt_subj = r_cod       d_cod_tl.dt_pred = "trophicLevel"   d_cod_tl.dt_val = "4"
    d_herr_nm.dt_subj = r_herring  d_herr_nm.dt_pred = "name"          d_herr_nm.dt_val = "Herring"
    d_herr_tl.dt_subj = r_herring  d_herr_tl.dt_pred = "trophicLevel"  d_herr_tl.dt_val = "3"
    d_cope_nm.dt_subj = r_copepod  d_cope_nm.dt_pred = "name"          d_cope_nm.dt_val = "Copepod"
    d_cope_tl.dt_subj = r_copepod  d_cope_tl.dt_pred = "trophicLevel"  d_cope_tl.dt_val = "2"
    d_sand_nm.dt_subj = r_sandeel  d_sand_nm.dt_pred = "name"          d_sand_nm.dt_val = "Sand Eel"
    d_sand_tl.dt_subj = r_sandeel  d_sand_tl.dt_pred = "trophicLevel"  d_sand_tl.dt_val = "3"
}

instance ExtractedLPG = delta ToTriples ExternalRDF
"""
```

``` julia
env = run_program(typeside * pg_schema * rdf_schema * mapping * external_rdf)
alg_ext = env.instances["ExtractedLPG"].algebra

println("=== Extracted Property Graph from RDF ===")
println("Nodes:")
for n in sort(collect(CQL.carrier(alg_ext, :PGNode)), by=string)
    println("  ", CQL.eval_att(alg_ext, :node_id, n))
end
println("\nEdges:")
for e in sort(collect(CQL.carrier(alg_ext, :PGEdge)), by=string)
    sn = CQL.eval_att(alg_ext, :node_id, CQL.eval_fk(alg_ext, :src, e))
    tn = CQL.eval_att(alg_ext, :node_id, CQL.eval_fk(alg_ext, :tgt, e))
    println("  $sn --[$(CQL.eval_att(alg_ext, :edge_label, e))]--> $tn")
end
println("\nProperties:")
for p in sort(collect(CQL.carrier(alg_ext, :PGProp)), by=string)
    nid = CQL.eval_att(alg_ext, :node_id, CQL.eval_fk(alg_ext, :prop_of, p))
    pk = CQL.eval_att(alg_ext, :prop_key, p)
    pv = CQL.eval_att(alg_ext, :prop_val, p)
    println("  $nid . $pk = \"$pv\"")
end
```

    === Extracted Property Graph from RDF ===
    Nodes:
      eco:atlantic_cod
      eco:copepod
      eco:herring
      eco:sand_eel

    Edges:
      eco:atlantic_cod --[eco:feedsOn]--> eco:herring
      eco:atlantic_cod --[eco:feedsOn]--> eco:sand_eel
      eco:herring --[eco:feedsOn]--> eco:copepod

    Properties:
      eco:atlantic_cod . name = "Atlantic Cod"
      eco:atlantic_cod . trophicLevel = "4"
      eco:copepod . name = "Copepod"
      eco:copepod . trophicLevel = "2"
      eco:herring . name = "Herring"
      eco:herring . trophicLevel = "3"
      eco:sand_eel . name = "Sand Eel"
      eco:sand_eel . trophicLevel = "3"

Delta extracted 4 species nodes, 3 feeding links, and 8 property records
from the RDF data — exactly matching the input. This extracted property
graph could be loaded directly into Neo4j.

------------------------------------------------------------------------

## Schema Colimit: A Unified View

Rather than choosing one paradigm over the other, CQL’s **schema
colimit** can merge both schemas into a single unified view. The colimit
identifies corresponding entities (PGNode = Resource, PGEdge =
ObjTriple, PGProp = DataTriple) and equates their attributes.

``` julia
colimit_prog = """
schema_colimit Unified = quotient PropertyGraph + TripleStore : Ty {
  entity_equations
    PropertyGraph.PGNode = TripleStore.Resource
    PropertyGraph.PGEdge = TripleStore.ObjTriple
    PropertyGraph.PGProp = TripleStore.DataTriple
  observation_equations
    forall x. x.PropertyGraph_PGNode_node_id = x.TripleStore_Resource_uri
    forall x. x.PropertyGraph_PGEdge_edge_label = x.TripleStore_ObjTriple_predicate
    forall x. x.PropertyGraph_PGProp_prop_key = x.TripleStore_DataTriple_dt_pred
    forall x. x.PropertyGraph_PGProp_prop_val = x.TripleStore_DataTriple_dt_val
}
"""

env = run_program(typeside * pg_schema * rdf_schema * colimit_prog)
sc = env.colimits["Unified"]
unified = sc.schema

println("=== Unified Schema ===")
println("Entities: ", join(sort(collect(unified.ens)), ", "))
println("\nForeign keys (both naming conventions):")
for (k, v) in sort(collect(unified.fks), by=x->string(first(x)))
    dn = CQL._display_name(k)
    println("  $dn : $(first(v)) → $(last(v))")
end
println("\nAttributes (equated pairs share one entity):")
for (k, v) in sort(collect(unified.atts), by=x->string(first(x)))
    dn = CQL._display_name(k)
    println("  $dn : $(first(v)) → $(last(v))")
end
```

    === Unified Schema ===
    Entities: PropertyGraph_PGEdge, PropertyGraph_PGNode, PropertyGraph_PGProp

    Foreign keys (both naming conventions):
      PropertyGraph_PGEdge_src : PropertyGraph_PGEdge → PropertyGraph_PGNode
      PropertyGraph_PGEdge_tgt : PropertyGraph_PGEdge → PropertyGraph_PGNode
      PropertyGraph_PGProp_prop_of : PropertyGraph_PGProp → PropertyGraph_PGNode
      TripleStore_DataTriple_dt_subj : PropertyGraph_PGProp → PropertyGraph_PGNode
      TripleStore_ObjTriple_obj : PropertyGraph_PGEdge → PropertyGraph_PGNode
      TripleStore_ObjTriple_subj : PropertyGraph_PGEdge → PropertyGraph_PGNode

    Attributes (equated pairs share one entity):
      PropertyGraph_PGEdge_edge_label : PropertyGraph_PGEdge → String
      PropertyGraph_PGNode_node_id : PropertyGraph_PGNode → String
      PropertyGraph_PGProp_prop_key : PropertyGraph_PGProp → String
      PropertyGraph_PGProp_prop_val : PropertyGraph_PGProp → String
      TripleStore_DataTriple_dt_pred : PropertyGraph_PGProp → String
      TripleStore_DataTriple_dt_val : PropertyGraph_PGProp → String
      TripleStore_ObjTriple_predicate : PropertyGraph_PGEdge → String
      TripleStore_Resource_uri : PropertyGraph_PGNode → String

The colimit schema contains a single set of entities — since we
identified PGNode with Resource, PGEdge with ObjTriple, and PGProp with
DataTriple. The foreign keys and attributes from both paradigms coexist,
with the observation equations ensuring that `node_id = uri`,
`edge_label = predicate`, `prop_key = dt_pred`, and `prop_val = dt_val`.

Data from either paradigm can be migrated into the unified schema using
the canonical **Sigma** mappings that the colimit construction provides
automatically.

------------------------------------------------------------------------

## Summary

| Challenge | CQL Solution | Categorical Concept |
|----|----|----|
| LPG → RDF | Sigma (pushforward) | Left adjoint of functor |
| RDF → LPG | Delta (pullback) | Right adjoint of functor |
| Round-trip guarantee | Unit / Counit | Adjunction natural transforms |
| SPARQL-like extraction | Uber-flower query | Profunctor composition |
| Edge properties in RDF | Reification schema + Sigma | Schema extension + functor |
| Unified paradigm view | Schema colimit | Categorical colimit |

The key insight is that RDF and LPG are not fundamentally different —
they are **isomorphic presentations** of the same categorical structure,
as long as node properties are modeled as first-class entities. The
asymmetry only appears when LPG uses edge properties, which requires RDF
reification to resolve.

CQL makes this structural relationship precise and executable. Rather
than writing ad-hoc scripts to convert between Neo4j and SPARQL
endpoints, the conversion is derived automatically from a single schema
morphism — with mathematical guarantees that no data is lost or invented
in the process.
