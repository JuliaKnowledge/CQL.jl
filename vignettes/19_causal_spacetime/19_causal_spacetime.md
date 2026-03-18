# From Causal SQL to Semantic Spacetime via CQL
Simon Frost

- [Introduction](#introduction)
- [Part 1: CSQL as a CQL Schema](#part-1-csql-as-a-cql-schema)
  - [The SQL Approach](#the-sql-approach)
  - [The CQL Approach](#the-cql-approach)
  - [Populating the CQL Instance](#populating-the-cql-instance)
- [Part 2: SemanticSpacetime as a CQL
  Schema](#part-2-semanticspacetime-as-a-cql-schema)
  - [The Four-Type System](#the-four-type-system)
  - [The Same Data in SST Form](#the-same-data-in-sst-form)
- [Part 3: The Mapping — What’s Preserved and What’s
  Lost](#part-3-the-mapping--whats-preserved-and-whats-lost)
  - [What the Mapping Tells Us](#what-the-mapping-tells-us)
- [Part 4: Delta and Sigma — Moving Data Between
  Worlds](#part-4-delta-and-sigma--moving-data-between-worlds)
  - [Delta: Pulling SST Data into CSQL
    Form](#delta-pulling-sst-data-into-csql-form)
- [Part 5: Queries That CQL Makes
  Natural](#part-5-queries-that-cql-makes-natural)
  - [Multi-Hop Causal Paths](#multi-hop-causal-paths)
- [Part 6: A Hybrid Schema](#part-6-a-hybrid-schema)
  - [Querying Across Channels](#querying-across-channels)
- [Summary](#summary)
- [Julia DSL](#julia-dsl)

## Introduction

Two Julia packages model causal and semantic relationships in
fundamentally different ways:

- **CSQL.jl** ([arXiv:2601.08109](https://arxiv.org/abs/2601.08109))
  builds SQL-queryable causal databases from extracted causal triples
  (subject, relation, object), with 20 relation types, polarity
  tracking, and provenance
- **SemanticSpacetime.jl** models knowledge as a typed graph with
  exactly 4 fundamental relationship types arranged on a signed spectrum
  inspired by physics: **LEADSTO** (causality), **CONTAINS**
  (composition), **EXPRESS** (description), and **NEAR** (proximity)

Both represent directed graphs with typed edges, but they make very
different choices about **what the types mean** and **how structure is
encoded**. In this vignette, we use the Categorical Query Language (CQL)
to:

1.  Express both data models as CQL schemas
2.  Construct a **mapping** (schema morphism) between them
3.  Use **delta** and **sigma** migrations to move data between the two
    representations
4.  Discover what the morphism reveals about the structure of causal
    knowledge

The key insight: a CQL mapping between schemas is not just a translation
— it’s a **statement about what information is preserved, lost, or
gained** in the translation. The delta-sigma adjunction makes this
precise.

``` julia
using CQL
```

## Part 1: CSQL as a CQL Schema

### The SQL Approach

In CSQL.jl, causal knowledge is stored in four SQL tables:

| Table                | Purpose                                        |
|----------------------|------------------------------------------------|
| `atlas_nodes`        | Canonical causal concepts                      |
| `atlas_edges`        | Aggregated causal relationships                |
| `atlas_edge_support` | Provenance (links edges to source documents)   |
| `atlas_scc`          | Strongly connected components (feedback loops) |

The SQL schema uses integer foreign keys (`src_id`, `dst_id`, `edge_id`)
and string-typed relation labels (`CAUSES`, `INCREASES`, `REDUCES`,
etc.).

### The CQL Approach

In CQL, we model the same structure using **entities** (tables),
**foreign keys** (typed references), and **attributes** (data values).
Foreign keys are first-class — they are functions between entities, not
integer columns.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String Real Int
    constants
        CAUSES INCREASES REDUCES PREVENTS LEADS_TO ENABLES
        AFFECTS TREATS TARGETS INHIBITS ACTIVATES
        ASSOCIATED_WITH COOCCURS_WITH INTERACTS_WITH : String
        inc dec unk : String
        "0.0" "0.5" "0.85" "0.88" "0.92" "0.95" : Real
}

schema CausalAtlas = literal : Ty {
    entities
        Node Edge EdgeSupport
    foreign_keys
        src : Edge -> Node
        dst : Edge -> Node
        evidence : EdgeSupport -> Edge
    attributes
        label : Node -> String
        rel_type : Edge -> String
        polarity : Edge -> String
        score : Edge -> Real
        doc_id : EdgeSupport -> String
        evidence_score : EdgeSupport -> Real
}
"""

println("CausalAtlas entities: ", env.CausalAtlas.ens)
println("Foreign keys: ", collect(keys(env.CausalAtlas.fks)))
println("Attributes: ", collect(keys(env.CausalAtlas.atts)))
```

    CausalAtlas entities: Set([:EdgeSupport, :Node, :Edge])
    Foreign keys: [:src, :dst, :evidence]
    Attributes: [:rel_type, :polarity, :doc_id, :label, :evidence_score, :score]

Notice what CQL gives us that SQL does not:

- **`src` and `dst` are typed functions**, not integer columns. You
  cannot accidentally join on the wrong column.
- **Path expressions** like `e.src.label` follow foreign keys with
  guaranteed type safety. No `JOIN` clause needed.
- **The schema is a category**: entities are objects, foreign keys are
  morphisms, and path equations enforce constraints.

### Populating the CQL Instance

``` julia
env = cql"""
typeside Ty = literal {
    types
        String Real
    constants
        Vaccination Susceptibility Transmission : String
        PopulationImmunity ContactRate OutbreakSeverity : String
        REDUCES INCREASES : String
        inc dec : String
        smith2023 jones2024 : String
        "0.92" "0.88" "0.85" "0.95" : Real
}

schema CausalAtlas = literal : Ty {
    entities
        Node Edge EdgeSupport
    foreign_keys
        src : Edge -> Node
        dst : Edge -> Node
        evidence : EdgeSupport -> Edge
    attributes
        label : Node -> String
        rel_type : Edge -> String
        polarity : Edge -> String
        score : Edge -> Real
        doc_id : EdgeSupport -> String
}

instance EpiAtlas = literal : CausalAtlas {
    generators
        vaccination susceptibility transmission : Node
        pop_immunity contact_rate outbreak_sev : Node
        e1 e2 e3 e4 : Edge
        s1 s2 s3 s4 : EdgeSupport
    equations
        src(e1) = vaccination    dst(e1) = susceptibility
        src(e2) = vaccination    dst(e2) = pop_immunity
        src(e3) = contact_rate   dst(e3) = transmission
        src(e4) = transmission   dst(e4) = outbreak_sev

        rel_type(e1) = REDUCES    polarity(e1) = dec
        rel_type(e2) = INCREASES  polarity(e2) = inc
        rel_type(e3) = INCREASES  polarity(e3) = inc
        rel_type(e4) = INCREASES  polarity(e4) = inc

        score(e1) = "0.92"  score(e2) = "0.88"
        score(e3) = "0.85"  score(e4) = "0.95"

        evidence(s1) = e1  doc_id(s1) = smith2023
        evidence(s2) = e2  doc_id(s2) = smith2023
        evidence(s3) = e3  doc_id(s3) = jones2024
        evidence(s4) = e4  doc_id(s4) = jones2024

        label(vaccination) = Vaccination
        label(susceptibility) = Susceptibility
        label(transmission) = Transmission
        label(pop_immunity) = PopulationImmunity
        label(contact_rate) = ContactRate
        label(outbreak_sev) = OutbreakSeverity
}
"""

alg = env.EpiAtlas.algebra
println("Nodes: ", length(carrier(alg, :Node)))
println("Edges: ", length(carrier(alg, :Edge)))
println("Evidence records: ", length(carrier(alg, :EdgeSupport)))

println("\nCausal edges:")
for x in carrier(alg, :Edge)
    s = eval_att(alg, :label, eval_fk(alg, :src, x))
    d = eval_att(alg, :label, eval_fk(alg, :dst, x))
    r = eval_att(alg, :rel_type, x)
    println("  $s --[$r]--> $d")
end
```

    Nodes: 6
    Edges: 4
    Evidence records: 4

    Causal edges:
      ContactRate --[INCREASES]--> Transmission
      Vaccination --[REDUCES]--> Susceptibility
      Vaccination --[INCREASES]--> PopulationImmunity
      Transmission --[INCREASES]--> OutbreakSeverity

Compare this with SQL: in CQL, we write `eval_fk(alg, :src, x)` to
follow a foreign key — this is a **function application**, not a join.
The path `src(e).label` is a composition of morphisms in the schema
category.

## Part 2: SemanticSpacetime as a CQL Schema

### The Four-Type System

SemanticSpacetime classifies all relationships along a signed spectrum:

| STType | Channel   | Meaning                  | Examples                        |
|--------|-----------|--------------------------|---------------------------------|
| +1     | LEADSTO   | Causal/temporal forward  | “causes”, “leads to”, “enables” |
| -1     | -LEADSTO  | Causal/temporal backward | “caused by”, “preceded by”      |
| +2     | CONTAINS  | Compositional forward    | “has part”, “contains”          |
| -2     | -CONTAINS | Compositional backward   | “is part of”, “belongs to”      |
| +3     | EXPRESS   | Descriptive forward      | “has property”, “expresses”     |
| -3     | -EXPRESS  | Descriptive backward     | “is property of”                |
| 0      | NEAR      | Proximity/similarity     | “co-occurs with”, “similar to”  |

This is a much coarser type system than CSQL’s 20 relations, but it
carries **structural meaning**: the sign encodes direction, and the
magnitude encodes the semantic category.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String Real Int
    constants
        LEADSTO CONTAINS EXPRESS NEAR : String
        "1" "2" "3" "0" : Int
        "1.0" : Real
}

schema SemanticST = literal : Ty {
    entities
        Concept Link Arrow Context
    foreign_keys
        link_src : Link -> Concept
        link_dst : Link -> Concept
        link_arrow : Link -> Arrow
        link_context : Link -> Context
    attributes
        text : Concept -> String
        chapter : Concept -> String
        arrow_name : Arrow -> String
        stindex : Arrow -> Int
        weight : Link -> Real
        ctx_label : Context -> String
}
"""

println("SemanticST entities: ", env.SemanticST.ens)
println("Foreign keys: ", collect(keys(env.SemanticST.fks)))
```

    SemanticST entities: Set([:Context, :Concept, :Link, :Arrow])
    Foreign keys: [:link_context, :link_dst, :link_arrow, :link_src]

### The Same Data in SST Form

``` julia
env = cql"""
typeside Ty = literal {
    types
        String Real Int
    constants
        LEADSTO NEAR : String
        FwdCausal InhibCausal Proximity : String
        "1" "0" : Int
        epi : String
        Vaccination Susceptibility Transmission : String
        PopulationImmunity ContactRate OutbreakSeverity : String
        "0.92" "0.88" "0.85" "0.95" : Real
}

schema SemanticST = literal : Ty {
    entities
        Concept Link Arrow Context
    foreign_keys
        link_src : Link -> Concept
        link_dst : Link -> Concept
        link_arrow : Link -> Arrow
        link_context : Link -> Context
    attributes
        text : Concept -> String
        chapter : Concept -> String
        arrow_name : Arrow -> String
        stindex : Arrow -> Int
        weight : Link -> Real
        ctx_label : Context -> String
}

instance EpiSST = literal : SemanticST {
    generators
        vaccination susceptibility transmission : Concept
        pop_immunity contact_rate outbreak_sev : Concept
        fwd_causal inhib_causal proximity_arrow : Arrow
        epi_ctx : Context
        l1 l2 l3 l4 : Link
    equations
        text(vaccination) = Vaccination
        text(susceptibility) = Susceptibility
        text(transmission) = Transmission
        text(pop_immunity) = PopulationImmunity
        text(contact_rate) = ContactRate
        text(outbreak_sev) = OutbreakSeverity
        chapter(vaccination) = epi  chapter(susceptibility) = epi
        chapter(transmission) = epi  chapter(pop_immunity) = epi
        chapter(contact_rate) = epi  chapter(outbreak_sev) = epi

        arrow_name(fwd_causal) = LEADSTO   stindex(fwd_causal) = "1"
        arrow_name(inhib_causal) = LEADSTO  stindex(inhib_causal) = "1"
        arrow_name(proximity_arrow) = NEAR  stindex(proximity_arrow) = "0"

        ctx_label(epi_ctx) = epi

        link_src(l1) = vaccination    link_dst(l1) = susceptibility
        link_src(l2) = vaccination    link_dst(l2) = pop_immunity
        link_src(l3) = contact_rate   link_dst(l3) = transmission
        link_src(l4) = transmission   link_dst(l4) = outbreak_sev

        link_arrow(l1) = inhib_causal   weight(l1) = "0.92"
        link_arrow(l2) = fwd_causal     weight(l2) = "0.88"
        link_arrow(l3) = fwd_causal     weight(l3) = "0.85"
        link_arrow(l4) = fwd_causal     weight(l4) = "0.95"

        link_context(l1) = epi_ctx  link_context(l2) = epi_ctx
        link_context(l3) = epi_ctx  link_context(l4) = epi_ctx
}
"""

alg = env.EpiSST.algebra
println("Concepts: ", length(carrier(alg, :Concept)))
println("Links: ", length(carrier(alg, :Link)))
println("Arrows: ", length(carrier(alg, :Arrow)))

println("\nSST links:")
for x in carrier(alg, :Link)
    s = eval_att(alg, :text, eval_fk(alg, :link_src, x))
    d = eval_att(alg, :text, eval_fk(alg, :link_dst, x))
    a = eval_att(alg, :arrow_name, eval_fk(alg, :link_arrow, x))
    w = eval_att(alg, :weight, x)
    println("  $s --[$a]--> $d  (weight=$w)")
end
```

    Concepts: 6
    Links: 4
    Arrows: 3

    SST links:
      Vaccination --[LEADSTO]--> Susceptibility  (weight=0.92)
      ContactRate --[LEADSTO]--> Transmission  (weight=0.85)
      Transmission --[LEADSTO]--> OutbreakSeverity  (weight=0.95)
      Vaccination --[LEADSTO]--> PopulationImmunity  (weight=0.88)

## Part 3: The Mapping — What’s Preserved and What’s Lost

A CQL **mapping** `F : CausalAtlas → SemanticST` tells us exactly how
the CSQL world-view translates into the SST world-view.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String Real Int
    constants
        REDUCES INCREASES CAUSES PREVENTS LEADS_TO ENABLES
        AFFECTS TREATS TARGETS INHIBITS ACTIVATES
        ASSOCIATED_WITH COOCCURS_WITH INTERACTS_WITH : String
        inc dec unk : String
        LEADSTO NEAR : String
        "1" "0" : Int
        unknown_ctx : String
}

schema CausalAtlas = literal : Ty {
    entities
        Node Edge EdgeSupport
    foreign_keys
        src : Edge -> Node
        dst : Edge -> Node
        evidence : EdgeSupport -> Edge
    attributes
        label : Node -> String
        rel_type : Edge -> String
        polarity : Edge -> String
        score : Edge -> Real
        doc_id : EdgeSupport -> String
}

schema SemanticST = literal : Ty {
    entities
        Concept Link Arrow Context
    foreign_keys
        link_src : Link -> Concept
        link_dst : Link -> Concept
        link_arrow : Link -> Arrow
        link_context : Link -> Context
    attributes
        text : Concept -> String
        arrow_name : Arrow -> String
        stindex : Arrow -> Int
        weight : Link -> Real
        ctx_label : Context -> String
}

mapping F = literal : CausalAtlas -> SemanticST {
    entity
        Node -> Concept
        attributes
            label -> text

    entity
        Edge -> Link
        foreign_keys
            src -> link_src
            dst -> link_dst
        attributes
            score -> weight

    entity
        EdgeSupport -> Link
        foreign_keys
            evidence -> identity
}
"""

m = env.F
println("Mapping F: CausalAtlas -> SemanticST")
println("Entity mappings:")
for (src_en, tgt_en) in m.ens
    println("  $src_en -> $tgt_en")
end
```

    Mapping F: CausalAtlas -> SemanticST
    Entity mappings:
      EdgeSupport -> Link
      Node -> Concept
      Edge -> Link

### What the Mapping Tells Us

Let’s unpack what this mapping says:

**1. Node → Concept**: Every causal concept in CSQL becomes a semantic
concept in SST. The `label` attribute maps to `text`. This is a clean,
information-preserving translation.

**2. Edge → Link**: Every causal edge becomes a semantic link. Source
and destination are preserved. But notice what happens to the
attributes:

- `score → weight`: Evidence strength is preserved
- `rel_type`: Has **no image** in SemanticST’s Link attributes — it must
  go through the `Arrow` entity
- `polarity`: Also has no direct image — it’s encoded in the sign of the
  arrow’s `stindex`

This means **the mapping loses the fine-grained relation type**. CSQL
distinguishes INCREASES from CAUSES from ENABLES — SemanticSpacetime
collapses all of these into `+LEADSTO`.

**3. EdgeSupport → Link**: Provenance records collapse into the link
itself. Multiple evidence records for the same edge become **the same
link**. This is the most significant information loss: SST doesn’t track
how many documents support a claim.

## Part 4: Delta and Sigma — Moving Data Between Worlds

### Delta: Pulling SST Data into CSQL Form

Delta (pullback) restructures SST data into CSQL’s schema. Since the
mapping sends both `Edge` and `EdgeSupport` to `Link`, delta will create
**copies** of each SST link — one as an Edge, one as an EdgeSupport.

``` julia
# Using our mapping F and the EpiSST instance from earlier
# Delta pulls data backward: SST → CausalAtlas

env2 = cql"""
typeside Ty = literal {
    types
        String Real Int
    constants
        Vaccination Susceptibility Transmission : String
        PopulationImmunity ContactRate OutbreakSeverity : String
        LEADSTO NEAR : String
        FwdCausal InhibCausal : String
        epi : String
        "1" "0" : Int
        "0.92" "0.88" "0.85" "0.95" : Real
}

schema SemanticST = literal : Ty {
    entities
        Concept Link Arrow Context
    foreign_keys
        link_src : Link -> Concept
        link_dst : Link -> Concept
        link_arrow : Link -> Arrow
        link_context : Link -> Context
    attributes
        text : Concept -> String
        arrow_name : Arrow -> String
        stindex : Arrow -> Int
        weight : Link -> Real
        ctx_label : Context -> String
}

schema CausalAtlas = literal : Ty {
    entities
        Node Edge EdgeSupport
    foreign_keys
        src : Edge -> Node
        dst : Edge -> Node
        evidence : EdgeSupport -> Edge
    attributes
        label : Node -> String
        score : Edge -> Real
        doc_id : EdgeSupport -> String
}

instance EpiSST = literal : SemanticST {
    generators
        vaccination susceptibility transmission : Concept
        pop_immunity contact_rate outbreak_sev : Concept
        fwd_causal inhib_causal : Arrow
        epi_ctx : Context
        l1 l2 l3 l4 : Link
    equations
        text(vaccination) = Vaccination  text(susceptibility) = Susceptibility
        text(transmission) = Transmission  text(pop_immunity) = PopulationImmunity
        text(contact_rate) = ContactRate  text(outbreak_sev) = OutbreakSeverity
        arrow_name(fwd_causal) = LEADSTO  stindex(fwd_causal) = "1"
        arrow_name(inhib_causal) = LEADSTO  stindex(inhib_causal) = "1"
        ctx_label(epi_ctx) = epi
        link_src(l1) = vaccination  link_dst(l1) = susceptibility
        link_src(l2) = vaccination  link_dst(l2) = pop_immunity
        link_src(l3) = contact_rate  link_dst(l3) = transmission
        link_src(l4) = transmission  link_dst(l4) = outbreak_sev
        link_arrow(l1) = inhib_causal  weight(l1) = "0.92"
        link_arrow(l2) = fwd_causal  weight(l2) = "0.88"
        link_arrow(l3) = fwd_causal  weight(l3) = "0.85"
        link_arrow(l4) = fwd_causal  weight(l4) = "0.95"
        link_context(l1) = epi_ctx  link_context(l2) = epi_ctx
        link_context(l3) = epi_ctx  link_context(l4) = epi_ctx
}

schema SimpleAtlas = literal : Ty {
    entities
        Node Edge
    foreign_keys
        src : Edge -> Node
        dst : Edge -> Node
    attributes
        label : Node -> String
        score : Edge -> Real
}

query DeltaQ = literal : SemanticST -> SimpleAtlas {
    entity Node -> {
        from c : Concept
        attributes label -> text(c)
    }
    entity Edge -> {
        from l : Link
        attributes score -> weight(l)
        foreign_keys
            src -> {c -> link_src(l)}
            dst -> {c -> link_dst(l)}
    }
}

instance DeltaResult = eval DeltaQ EpiSST
"""

alg = env2.DeltaResult.algebra
println("=== Delta: SST -> SimpleAtlas ===")
println("Nodes: ", length(carrier(alg, :Node)))
println("Edges: ", length(carrier(alg, :Edge)))

println("\nReconstructed causal edges:")
for x in carrier(alg, :Edge)
    s = eval_att(alg, :label, eval_fk(alg, :src, x))
    d = eval_att(alg, :label, eval_fk(alg, :dst, x))
    sc = eval_att(alg, :score, x)
    println("  $s --> $d  (score=$sc)")
end
```

    === Delta: SST -> SimpleAtlas ===
    Nodes: 6
    Edges: 4

    Reconstructed causal edges:
      Vaccination --> Susceptibility  (score=0.92)
      ContactRate --> Transmission  (score=0.85)
      Vaccination --> PopulationImmunity  (score=0.88)
      Transmission --> OutbreakSeverity  (score=0.95)

Notice that the delta migration:

- **Preserves concepts** (Node ↔ Concept are 1:1)
- **Preserves edges** (Edge ↔ Link are 1:1)
- **Creates evidence records** from context labels (each link generates
  one evidence record)

But the `rel_type` and `polarity` attributes are missing from the result
— they were lost in the mapping because SST doesn’t distinguish them at
the Link level. This is the **information loss** made precise by the
adjunction.

## Part 5: Queries That CQL Makes Natural

### Multi-Hop Causal Paths

In SQL, finding 3-hop causal paths requires a triple self-join with
explicit ON clauses. In CQL, it’s a single uber-flower:

``` julia
env = cql"""
typeside Ty = literal {
    types
        String Real
    constants
        Vaccination Susceptibility Transmission : String
        PopulationImmunity ContactRate OutbreakSeverity : String
        REDUCES INCREASES : String
        "0.92" "0.88" "0.85" "0.95" : Real
}

schema CausalAtlas = literal : Ty {
    entities
        Node Edge
    foreign_keys
        src : Edge -> Node
        dst : Edge -> Node
    attributes
        label : Node -> String
        rel_type : Edge -> String
        score : Edge -> Real
}

schema PathResult = literal : Ty {
    entities
        Path
    attributes
        step1 : Path -> String
        rel1 : Path -> String
        step2 : Path -> String
        rel2 : Path -> String
        step3 : Path -> String
}

query CausalPath2 = literal : CausalAtlas -> PathResult {
    entity Path -> {
        from e1:Edge e2:Edge
        where dst(e1) = src(e2)
        attributes
            step1 -> label(src(e1))
            rel1 -> rel_type(e1)
            step2 -> label(dst(e1))
            rel2 -> rel_type(e2)
            step3 -> label(dst(e2))
    }
}

instance EpiAtlas = literal : CausalAtlas {
    generators
        vaccination susceptibility transmission : Node
        pop_immunity contact_rate outbreak_sev : Node
        e1 e2 e3 e4 : Edge
    equations
        src(e1) = vaccination    dst(e1) = susceptibility
        src(e2) = vaccination    dst(e2) = pop_immunity
        src(e3) = contact_rate   dst(e3) = transmission
        src(e4) = transmission   dst(e4) = outbreak_sev
        rel_type(e1) = REDUCES   rel_type(e2) = INCREASES
        rel_type(e3) = INCREASES rel_type(e4) = INCREASES
        score(e1) = "0.92"  score(e2) = "0.88"
        score(e3) = "0.85"  score(e4) = "0.95"
        label(vaccination) = Vaccination
        label(susceptibility) = Susceptibility
        label(transmission) = Transmission
        label(pop_immunity) = PopulationImmunity
        label(contact_rate) = ContactRate
        label(outbreak_sev) = OutbreakSeverity
}

instance Paths = eval CausalPath2 EpiAtlas
"""

alg = env.Paths.algebra
println("=== 2-Hop Causal Paths ===")
for x in carrier(alg, :Path)
    s1 = eval_att(alg, :step1, x)
    r1 = eval_att(alg, :rel1, x)
    s2 = eval_att(alg, :step2, x)
    r2 = eval_att(alg, :rel2, x)
    s3 = eval_att(alg, :step3, x)
    println("  $s1 --[$r1]--> $s2 --[$r2]--> $s3")
end
```

    === 2-Hop Causal Paths ===
      ContactRate --[INCREASES]--> Transmission --[INCREASES]--> OutbreakSeverity

The CQL query `CausalPath2` says: “for each pair of edges `(e1, e2)`
where the destination of `e1` equals the source of `e2`, create a path
record.” This is:

- **Type-safe**: the `where dst(e1) = src(e2)` constraint is checked
  against the schema
- **Composable**: we could compose this query with itself to get 4-hop
  paths
- **Functorial**: the result is guaranteed to be a valid instance on the
  `PathResult` schema

The equivalent SQL would be:

``` sql
SELECT n1.label AS step1, e1.rel_type AS rel1,
       n2.label AS step2, e2.rel_type AS rel2,
       n3.label AS step3
FROM edges e1
JOIN edges e2 ON e1.dst_id = e2.src_id
JOIN nodes n1 ON e1.src_id = n1.node_id
JOIN nodes n2 ON e1.dst_id = n2.node_id
JOIN nodes n3 ON e2.dst_id = n3.node_id
```

The CQL version is more concise, type-safe, and composable.

## Part 6: A Hybrid Schema

The morphism analysis reveals that an ideal causal knowledge
representation would combine:

- **CSQL’s provenance tracking** (separate Evidence entity)
- **SST’s typed channels** (separate entities for causal, compositional,
  descriptive links)
- **CQL’s path equations** (enforcing structural constraints)

``` julia
env = cql"""
typeside Ty = literal {
    types
        String Real
    constants
        Vaccination mRNADose Adjuvant : String
        WHORecommended TwoDoseSchedule : String
        Susceptibility Transmission : String
        PopulationImmunity ContactRate OutbreakSeverity : String
        inc dec : String
        smith2023 jones2024 : String
        "0.92" "0.88" "0.85" "0.95" "1.0" : Real
}

schema CausalSpacetime = literal : Ty {
    entities
        Concept
        CausalLink
        ContainsLink
        PropertyLink
        Evidence
    foreign_keys
        cause : CausalLink -> Concept
        effect : CausalLink -> Concept
        whole : ContainsLink -> Concept
        part : ContainsLink -> Concept
        subject : PropertyLink -> Concept
        property : PropertyLink -> Concept
        causal_evidence : Evidence -> CausalLink
    attributes
        name : Concept -> String
        causal_weight : CausalLink -> Real
        polarity : CausalLink -> String
        contains_weight : ContainsLink -> Real
        property_weight : PropertyLink -> Real
        doc_id : Evidence -> String
        evidence_score : Evidence -> Real
}

instance EpiHybrid = literal : CausalSpacetime {
    generators
        vaccination susceptibility transmission : Concept
        pop_immunity contact_rate outbreak_sev : Concept
        mRNA_dose adjuvant : Concept
        who_rec two_dose : Concept

        cl1 cl2 cl3 cl4 : CausalLink
        part1 part2 : ContainsLink
        prop1 prop2 : PropertyLink
        ev1 ev2 ev3 ev4 : Evidence

    equations
        name(vaccination) = Vaccination
        name(susceptibility) = Susceptibility
        name(transmission) = Transmission
        name(pop_immunity) = PopulationImmunity
        name(contact_rate) = ContactRate
        name(outbreak_sev) = OutbreakSeverity
        name(mRNA_dose) = mRNADose
        name(adjuvant) = Adjuvant
        name(who_rec) = WHORecommended
        name(two_dose) = TwoDoseSchedule

        cause(cl1) = vaccination    effect(cl1) = susceptibility
        cause(cl2) = vaccination    effect(cl2) = pop_immunity
        cause(cl3) = contact_rate   effect(cl3) = transmission
        cause(cl4) = transmission   effect(cl4) = outbreak_sev
        causal_weight(cl1) = "0.92"  polarity(cl1) = dec
        causal_weight(cl2) = "0.88"  polarity(cl2) = inc
        causal_weight(cl3) = "0.85"  polarity(cl3) = inc
        causal_weight(cl4) = "0.95"  polarity(cl4) = inc

        whole(part1) = vaccination  part(part1) = mRNA_dose
        whole(part2) = vaccination  part(part2) = adjuvant
        contains_weight(part1) = "1.0"
        contains_weight(part2) = "1.0"

        subject(prop1) = vaccination  property(prop1) = who_rec
        subject(prop2) = vaccination  property(prop2) = two_dose
        property_weight(prop1) = "1.0"
        property_weight(prop2) = "1.0"

        causal_evidence(ev1) = cl1  doc_id(ev1) = smith2023  evidence_score(ev1) = "0.92"
        causal_evidence(ev2) = cl2  doc_id(ev2) = smith2023  evidence_score(ev2) = "0.88"
        causal_evidence(ev3) = cl3  doc_id(ev3) = jones2024  evidence_score(ev3) = "0.85"
        causal_evidence(ev4) = cl4  doc_id(ev4) = jones2024  evidence_score(ev4) = "0.95"
}
"""

alg = env.EpiHybrid.algebra
println("=== CausalSpacetime: Hybrid Schema ===")
println("Concepts: ", length(carrier(alg, :Concept)))
println("Causal links: ", length(carrier(alg, :CausalLink)))
println("Containment links: ", length(carrier(alg, :ContainsLink)))
println("Property links: ", length(carrier(alg, :PropertyLink)))
println("Evidence records: ", length(carrier(alg, :Evidence)))

println("\nCausal links:")
for x in carrier(alg, :CausalLink)
    c = eval_att(alg, :name, eval_fk(alg, :cause, x))
    e = eval_att(alg, :name, eval_fk(alg, :effect, x))
    p = eval_att(alg, :polarity, x)
    w = eval_att(alg, :causal_weight, x)
    println("  $c --[$p,$w]--> $e")
end

println("\nContainment (parts of Vaccination):")
for x in carrier(alg, :ContainsLink)
    w = eval_att(alg, :name, eval_fk(alg, :whole, x))
    p = eval_att(alg, :name, eval_fk(alg, :part, x))
    println("  $w contains $p")
end

println("\nProperties of Vaccination:")
for x in carrier(alg, :PropertyLink)
    s = eval_att(alg, :name, eval_fk(alg, :subject, x))
    p = eval_att(alg, :name, eval_fk(alg, :property, x))
    println("  $s has property $p")
end
```

    === CausalSpacetime: Hybrid Schema ===
    Concepts: 10
    Causal links: 4
    Containment links: 2
    Property links: 2
    Evidence records: 4

    Causal links:
      Transmission --[inc,0.95]--> OutbreakSeverity
      Vaccination --[dec,0.92]--> Susceptibility
      ContactRate --[inc,0.85]--> Transmission
      Vaccination --[inc,0.88]--> PopulationImmunity

    Containment (parts of Vaccination):
      Vaccination contains mRNADose
      Vaccination contains Adjuvant

    Properties of Vaccination:
      Vaccination has property TwoDoseSchedule
      Vaccination has property WHORecommended

### Querying Across Channels

The hybrid schema enables queries that **neither CSQL nor SST can
express alone**. For example: “What are the causal effects of each
component of vaccination?”

``` julia
env2 = cql"""
typeside Ty = literal {
    types
        String Real
    constants
        Vaccination mRNADose Adjuvant : String
        Susceptibility PopulationImmunity : String
        inc dec : String
        "0.92" "0.88" "1.0" : Real
}

schema CausalSpacetime = literal : Ty {
    entities
        Concept CausalLink ContainsLink
    foreign_keys
        cause : CausalLink -> Concept
        effect : CausalLink -> Concept
        whole : ContainsLink -> Concept
        part : ContainsLink -> Concept
    attributes
        name : Concept -> String
        causal_weight : CausalLink -> Real
        polarity : CausalLink -> String
        contains_weight : ContainsLink -> Real
}

schema ComponentEffects = literal : Ty {
    entities
        Result
    attributes
        whole_name : Result -> String
        part_name : Result -> String
        effect_name : Result -> String
        effect_polarity : Result -> String
}

query CrossChannelQ = literal : CausalSpacetime -> ComponentEffects {
    entity Result -> {
        from
            cont : ContainsLink
            causal : CausalLink
        where
            whole(cont) = cause(causal)
        attributes
            whole_name -> name(whole(cont))
            part_name -> name(part(cont))
            effect_name -> name(effect(causal))
            effect_polarity -> polarity(causal)
    }
}

instance Hybrid = literal : CausalSpacetime {
    generators
        vaccination mRNA_dose adjuvant : Concept
        susceptibility pop_immunity : Concept
        cl1 cl2 : CausalLink
        p1 p2 : ContainsLink
    equations
        name(vaccination) = Vaccination
        name(mRNA_dose) = mRNADose
        name(adjuvant) = Adjuvant
        name(susceptibility) = Susceptibility
        name(pop_immunity) = PopulationImmunity

        cause(cl1) = vaccination    effect(cl1) = susceptibility
        cause(cl2) = vaccination    effect(cl2) = pop_immunity
        causal_weight(cl1) = "0.92"  polarity(cl1) = dec
        causal_weight(cl2) = "0.88"  polarity(cl2) = inc

        whole(p1) = vaccination  part(p1) = mRNA_dose
        whole(p2) = vaccination  part(p2) = adjuvant
        contains_weight(p1) = "1.0"  contains_weight(p2) = "1.0"
}

instance Results = eval CrossChannelQ Hybrid
"""

alg = env2.Results.algebra
println("=== Cross-Channel Query: Component Effects ===")
for x in carrier(alg, :Result)
    w = eval_att(alg, :whole_name, x)
    p = eval_att(alg, :part_name, x)
    e = eval_att(alg, :effect_name, x)
    pol = eval_att(alg, :effect_polarity, x)
    println("  $w (contains $p) --[$pol]--> $e")
end
```

    === Cross-Channel Query: Component Effects ===
      Vaccination (contains Adjuvant) --[inc]--> PopulationImmunity
      Vaccination (contains mRNADose) --[inc]--> PopulationImmunity
      Vaccination (contains mRNADose) --[dec]--> Susceptibility
      Vaccination (contains Adjuvant) --[dec]--> Susceptibility

This query joins across **two different relationship types**
(containment and causation) in a single uber-flower. In SQL, this would
require knowing which tables hold which relationship types and writing
explicit joins. In CQL, the foreign keys make the join implicit and
type-safe.

## Summary

| Aspect | CSQL (SQL) | SST (Graph) | CQL |
|----|----|----|----|
| **Edge types** | 20 string labels | 4 signed channels | Separate entities per channel |
| **Provenance** | Separate table | Context label | Separate entity with FK |
| **Path queries** | Self-join chains | Cone traversal | Uber-flower composition |
| **Type safety** | Integer FK columns | NodePtr structs | Typed morphisms |
| **Hierarchy** | Not modeled | CONTAINS channel | ContainsLink entity |
| **Properties** | Not modeled | EXPRESS channel | PropertyLink entity |
| **Round-trips** | No guarantee | No guarantee | Delta-sigma adjunction |
| **Schema merging** | Manual ETL | Not supported | Schema colimit |

The CQL approach reveals that **causality is not a single relationship
type** — it exists within a richer semantic space that includes
composition, description, and proximity. By making each channel a
separate entity, CQL enables queries that cross these channels while
maintaining formal guarantees about data integrity.

The mapping `F : CausalAtlas → SemanticST` makes the information loss
precise: CSQL’s 20 relation types collapse to 4 channels, and provenance
records merge into links. Going the other direction, delta `Δ(F)`
reconstructs the CSQL structure from SST data, but cannot recover the
lost fine-grained types. This asymmetry — quantified by the adjunction
unit and counit — tells us exactly what each representation can and
cannot express.

## Julia DSL

The examples above use the `cql"""..."""` string macro. Here is how the
CausalAtlas schema and a causal path query look using the Julia DSL
macros:

``` julia
using CQL

Ty = @typeside begin
    String::Ty; Real::Ty
    Vaccination::String; Susceptibility::String
    Transmission::String; OutbreakSeverity::String
    ContactRate::String; PopulationImmunity::String
    REDUCES::String; INCREASES::String
    "0.92"::Real; "0.88"::Real; "0.85"::Real; "0.95"::Real
end

CausalAtlas = @schema Ty begin
    @entities Node, Edge
    src : Edge → Node
    dst : Edge → Node
    label : Node ⇒ String
    rel_type : Edge ⇒ String
    score : Edge ⇒ Real
end

PathResult = @schema Ty begin
    @entities Path
    step1 : Path ⇒ String
    rel1 : Path ⇒ String
    step2 : Path ⇒ String
    rel2 : Path ⇒ String
    step3 : Path ⇒ String
end

CausalPath2 = @query CausalAtlas → PathResult begin
    @entity Path begin
        @from e1::Edge, e2::Edge
        @where dst(e1) == src(e2)
        @return step1 => e1.src.label,
                rel1 => rel_type(e1),
                step2 => e1.dst.label,
                rel2 => rel_type(e2),
                step3 => e2.dst.label
    end
end
```

The functional API operators (`Δ`, `Σ`, `Q(I)`, `∘`, `⊔`) work directly
with schema and instance objects constructed by either the DSL macros or
the `cql"""..."""` syntax — they are fully interoperable.
