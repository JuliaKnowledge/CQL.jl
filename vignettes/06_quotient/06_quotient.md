# Quotients and Merging in CQL
Simon Frost

## Introduction

Computing the **quotient** of a set by an equivalence relation — a
so-called **tuple merge** — is a common data integration operation that
is unwieldy in SQL but easy in CQL. When integrating data from multiple
sources, we often discover that different records refer to the same
real-world entity and must be merged.

In SQL, computing transitive closures and merging related rows requires
recursive CTEs and careful bookkeeping. In CQL, the same operation is a
single **sigma** (pushforward) data migration.

This vignette demonstrates:

1.  **Direct merging**: equating generators in an instance
2.  **Sigma-based merging**: using a mapping to compute equivalence
    classes
3.  A Simpsons-themed example from the [CQL quotient
    tutorial](https://categoricaldata.net/quotient.html)

``` julia
using CQL
```

## Direct Merging: Equating Generators

The simplest form of merging in CQL is adding **equations between
generators**. When you declare `a = c` in an instance, CQL’s theorem
prover automatically merges the two elements into a single equivalence
class.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Alice Bob Charlie Dave Eve : String
}

schema S = literal : Ty {
    entities
        Person
    attributes
        name : Person -> String
}

instance Merged = literal : S {
    generators
        a b c d e : Person
    equations
        name(a) = Alice  name(b) = Bob  name(c) = Charlie
        name(d) = Dave  name(e) = Eve
        a = c
        b = d
}
"""

alg = env.Merged.algebra
println("Started with 5 generators: a, b, c, d, e")
println("Added equations: a = c, b = d")
println("Result: ", length(carrier(alg, :Person)), " distinct persons\n")

for x in carrier(alg, :Person)
    println("  ", repr_x(alg, x), ": name = ", eval_att(alg, :name, x))
end
```

    Started with 5 generators: a, b, c, d, e
    Added equations: a = c, b = d
    Result: 3 distinct persons

      b: name = Bob
      e: name = Eve
      a: name = Alice

The prover reduced 5 generators to 3 elements:

- `a` and `c` were merged (since `a = c`)
- `b` and `d` were merged (since `b = d`)
- `e` remains distinct

Note that merging also forces attribute identification: since `a = c`,
we get `name(a) = name(c)`, meaning `Alice = Charlie` in the resulting
algebra.

## Sigma Data Migration: Computing Quotients

Direct generator equations are useful when you know exactly which
elements to merge. But what if the merging is determined by the
**structure** of the data? This is where **sigma** (pushforward) data
migration shines.

### The Idea

Given a mapping `F: S -> T` that sends multiple entities to the same
entity, sigma pushes an instance forward along `F`, **identifying**
elements that get mapped to the same target. This computes a quotient:
the result has one equivalence class for each group of
transitively-connected elements.

### Example: Finding Connected Components in a Social Graph

Consider the Simpsons: some characters like other characters, forming a
social graph. We want to find the **connected components** — groups of
people transitively linked by “likes” relationships.

#### The Likes Schema

``` julia
env = cql"""
typeside Ty = empty

schema Likes = literal : Ty {
    entities
        Like
        Person
    foreign_keys
        likee : Like -> Person
        liker : Like -> Person
}
"""

sch = env.Likes
println("Entities: ", sch.ens)
println("Foreign keys: ", collect(keys(sch.fks)))
```

    Entities: Set([:Person, :Like])
    Foreign keys: [:likee, :liker]

Each `Like` record connects a `liker` to a `likee`. This is a standard
edge-list representation of a directed graph.

#### The Simpsons Data

``` julia
env = cql"""
typeside Ty = empty

schema Likes = literal : Ty {
    entities
        Like
        Person
    foreign_keys
        likee : Like -> Person
        liker : Like -> Person
}

instance SimpsonsLikes = literal : Likes {
    generators
        Ned Maud Rodd Todd MrBurns Smithers : Person
        l1 l2 l3 l4 : Like
    equations
        liker(l1) = Ned  likee(l1) = Maud
        liker(l2) = Maud likee(l2) = Rodd
        liker(l3) = Rodd likee(l3) = Todd
        liker(l4) = Smithers likee(l4) = MrBurns
}
"""

alg = env.SimpsonsLikes.algebra

println("=== Person Table ===")
println("Persons: ", length(carrier(alg, :Person)))
println()

println("=== Like Table (Social Graph Edges) ===")
for x in carrier(alg, :Like)
    liker = eval_fk(alg, :liker, x)
    likee = eval_fk(alg, :likee, x)
    println("  ", repr_x(alg, liker), " likes ", repr_x(alg, likee))
end
```

    === Person Table ===
    Persons: 6

    === Like Table (Social Graph Edges) ===
      Ned likes Maud
      Rodd likes Todd
      Smithers likes MrBurns
      Maud likes Rodd

The social graph has two connected components:

- **Flanders family**: Ned → Maud → Rodd → Todd (a chain of likes)
- **Burns & Smithers**: Smithers → MrBurns

#### The Connections Mapping

To find connected components, we define a **target schema** with a
single entity `Connection` and a mapping that sends both `Person` and
`Like` to `Connection`:

``` julia
env = cql"""
typeside Ty = empty

schema Likes = literal : Ty {
    entities
        Like
        Person
    foreign_keys
        likee : Like -> Person
        liker : Like -> Person
}

schema Connections = literal : Ty {
    entities
        Connection
}

mapping FindConnections = literal : Likes -> Connections {
    entity
        Person -> Connection
    entity
        Like -> Connection
        foreign_keys
            likee -> Connection
            liker -> Connection
}
"""

println("Mapping: Likes -> Connections")
m = env.FindConnections
println("  Person -> Connection")
println("  Like   -> Connection")
println("  likee  -> identity on Connection")
println("  liker  -> identity on Connection")
```

    Mapping: Likes -> Connections
      Person -> Connection
      Like   -> Connection
      likee  -> identity on Connection
      liker  -> identity on Connection

The key insight: both `liker` and `likee` foreign keys map to the
**identity** on `Connection`. This means that for each like `l`, the
sigma operation will identify `liker(l)` with `l` and `likee(l)` with
`l`. Since both the liker and the likee are identified with the like
record, they are transitively identified with each other.

#### Computing the Quotient with Sigma

``` julia
env = cql"""
typeside Ty = empty

schema Likes = literal : Ty {
    entities
        Like
        Person
    foreign_keys
        likee : Like -> Person
        liker : Like -> Person
}

instance SimpsonsLikes = literal : Likes {
    generators
        Ned Maud Rodd Todd MrBurns Smithers : Person
        l1 l2 l3 l4 : Like
    equations
        liker(l1) = Ned  likee(l1) = Maud
        liker(l2) = Maud likee(l2) = Rodd
        liker(l3) = Rodd likee(l3) = Todd
        liker(l4) = Smithers likee(l4) = MrBurns
}

schema Connections = literal : Ty {
    entities
        Connection
}

mapping FindConnections = literal : Likes -> Connections {
    entity
        Person -> Connection
    entity
        Like -> Connection
        foreign_keys
            likee -> Connection
            liker -> Connection
}

instance SimpsonsConnections = sigma FindConnections SimpsonsLikes
"""

alg_likes = env.SimpsonsLikes.algebra
alg_conn = env.SimpsonsConnections.algebra

println("Before sigma:")
println("  Persons: ", length(carrier(alg_likes, :Person)))
println("  Likes:   ", length(carrier(alg_likes, :Like)))
println("  Total:   ", length(carrier(alg_likes, :Person)) + length(carrier(alg_likes, :Like)))

println("\nAfter sigma:")
println("  Connections: ", length(carrier(alg_conn, :Connection)))
```

    Before sigma:
      Persons: 6
      Likes:   4
      Total:   10

    After sigma:
      Connections: 2

Sigma reduced 10 elements (6 persons + 4 likes) to just **2
connections** — the two connected components of the social graph.

#### Tracing Group Membership

We can determine which group each original person belongs to by checking
which equivalence class their generator falls into:

``` julia
dp = env.SimpsonsConnections.dp
groups = collect(carrier(alg_conn, :Connection))

println("=== Connected Components ===\n")

persons = [:Ned, :Maud, :Rodd, :Todd, :MrBurns, :Smithers]
group_members = Dict(repr_x(alg_conn, g) => Symbol[] for g in groups)

for p in persons
    for g in groups
        gsym = repr_x(alg_conn, g)
        if dp(Equation(CQLGen(p), gsym))
            push!(group_members[gsym], p)
            break
        end
    end
end

for (i, g) in enumerate(groups)
    gsym = repr_x(alg_conn, g)
    members = group_members[gsym]
    println("Group $i (representative: $gsym):")
    for m in members
        println("  - $m")
    end
    println()
end
```

    === Connected Components ===

    Group 1 (representative: Ned):
      - Ned
      - Maud
      - Rodd
      - Todd

    Group 2 (representative: MrBurns):
      - MrBurns
      - Smithers

The Flanders family forms one connected component, and Burns with
Smithers forms another.

## How Sigma Computes the Quotient

The sigma operation works in three steps:

1.  **Remap generators**: All `Person` generators and `Like` generators
    become `Connection` generators in the target schema.

2.  **Remap equations**: The FK equations `liker(l1) = Ned` and
    `likee(l1) = Maud` become (after mapping) `l1 = Ned` and `l1 = Maud`
    (since both FKs map to the identity). This transitively gives
    `Ned = Maud`.

3.  **Compute initial algebra**: CQL’s theorem prover computes the
    equivalence classes, merging all transitively-equal generators.

Let’s trace through the chain for the Flanders family:

``` julia
println("=== Tracing the Flanders chain ===\n")
println("Original equations:")
println("  liker(l1) = Ned,  likee(l1) = Maud")
println("  liker(l2) = Maud, likee(l2) = Rodd")
println("  liker(l3) = Rodd, likee(l3) = Todd")
println()
println("After sigma (liker and likee map to identity):")
println("  l1 = Ned,  l1 = Maud    => Ned = Maud")
println("  l2 = Maud, l2 = Rodd    => Maud = Rodd")
println("  l3 = Rodd, l3 = Todd    => Rodd = Todd")
println()
println("Transitive closure:")
println("  Ned = Maud = Rodd = Todd = l1 = l2 = l3")
println("  (all in one equivalence class)")
```

    === Tracing the Flanders chain ===

    Original equations:
      liker(l1) = Ned,  likee(l1) = Maud
      liker(l2) = Maud, likee(l2) = Rodd
      liker(l3) = Rodd, likee(l3) = Todd

    After sigma (liker and likee map to identity):
      l1 = Ned,  l1 = Maud    => Ned = Maud
      l2 = Maud, l2 = Rodd    => Maud = Rodd
      l3 = Rodd, l3 = Todd    => Rodd = Todd

    Transitive closure:
      Ned = Maud = Rodd = Todd = l1 = l2 = l3
      (all in one equivalence class)

## Why This Is Hard in SQL

In SQL, finding connected components requires computing a **transitive
closure**, which needs recursive CTEs:

``` sql
-- SQL: Finding connected components (simplified)
WITH RECURSIVE connected(person, component) AS (
    -- Base case: each person is their own component
    SELECT DISTINCT p.id, p.id FROM Person p
    UNION
    -- Recursive step: merge through likes
    SELECT c.person, LEAST(c.component, l.likee)
    FROM connected c
    JOIN likes l ON c.person = l.liker
    UNION
    SELECT c.person, LEAST(c.component, l.liker)
    FROM connected c
    JOIN likes l ON c.person = l.likee
)
SELECT person, MIN(component) as group_id
FROM connected
GROUP BY person;
```

This SQL solution is:

- **Verbose**: ~15 lines vs. CQL’s single `sigma` call
- **Error-prone**: Getting the recursion right is tricky
- **Performance-sensitive**: Recursive CTEs can be slow on large graphs
- **Not composable**: Hard to chain with other operations

In CQL, the entire operation is:

    instance result = sigma FindConnections input_data

## Another Example: Deduplication

Sigma is also useful for **deduplication**: merging records that
represent the same real-world entity but appear in different tables.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Alice Bob Charlie : String
}

schema TwoSources = literal : Ty {
    entities
        Source1
        Source2
    attributes
        name1 : Source1 -> String
        name2 : Source2 -> String
}

schema Unified = literal : Ty {
    entities
        Person
    attributes
        name : Person -> String
}

mapping Merge = literal : TwoSources -> Unified {
    entity
        Source1 -> Person
        attributes
            name1 -> lambda x. name(x)
    entity
        Source2 -> Person
        attributes
            name2 -> lambda x. name(x)
}

instance TwoSourceData = literal : TwoSources {
    generators
        s1a s1b : Source1
        s2a s2b s2c : Source2
    equations
        name1(s1a) = Alice  name1(s1b) = Bob
        name2(s2a) = Alice  name2(s2b) = Charlie  name2(s2c) = Bob
}

instance Unified1 = sigma Merge TwoSourceData
"""

alg_before = env.TwoSourceData.algebra
alg_after = env.Unified1.algebra

println("=== Before Merge ===")
println("Source1: ", length(carrier(alg_before, :Source1)), " records")
for x in carrier(alg_before, :Source1)
    println("  ", repr_x(alg_before, x), ": ", eval_att(alg_before, :name1, x))
end
println("Source2: ", length(carrier(alg_before, :Source2)), " records")
for x in carrier(alg_before, :Source2)
    println("  ", repr_x(alg_before, x), ": ", eval_att(alg_before, :name2, x))
end

println("\n=== After Sigma Merge ===")
println("Person: ", length(carrier(alg_after, :Person)), " records")
for x in carrier(alg_after, :Person)
    println("  ", repr_x(alg_after, x), ": ", eval_att(alg_after, :name, x))
end
```

    === Before Merge ===
    Source1: 2 records
      s1a: Alice
      s1b: Bob
    Source2: 3 records
      s2c: Bob
      s2a: Alice
      s2b: Charlie

    === After Sigma Merge ===
    Person: 5 records
      s1a: Alice
      s2a: Alice
      s2c: Bob
      s1b: Bob
      s2b: Charlie

The sigma migration merges both sources into a single `Person` entity.
Records with the same name from different sources are **not**
automatically identified (they remain distinct unless explicitly
equated), but the unified schema allows downstream operations to work on
a single entity.

## Julia DSL

The examples above use the `cql"""..."""` string macro. CQL.jl also
provides Julia-native macros. Here is how the Likes schema, instance,
and sigma-based quotient look using the DSL:

``` julia
using CQL

Ty = @typeside begin end  # empty typeside

Likes = @schema Ty begin
    @entities Like, Person
    likee : Like → Person
    liker : Like → Person
end

SimpsonsLikes = @instance Likes begin
    Ned::Person; Maud::Person; Rodd::Person; Todd::Person
    MrBurns::Person; Smithers::Person
    l1::Like; l2::Like; l3::Like; l4::Like
    liker(l1) == Ned;  likee(l1) == Maud
    liker(l2) == Maud; likee(l2) == Rodd
    liker(l3) == Rodd; likee(l3) == Todd
    liker(l4) == Smithers; likee(l4) == MrBurns
end

println("Persons: ", length(carrier(SimpsonsLikes.algebra, :Person)))
println("Likes: ", length(carrier(SimpsonsLikes.algebra, :Like)))
```

    Persons: 6
    Likes: 4

Once a mapping `F` is obtained via cql syntax, the functional API
provides concise sigma and distinct operations:

``` julia
# Σ(F)(I) pushes an instance forward along a mapping
# distinct(I) merges provably equal elements in an instance
# These work with any mapping/instance, e.g.:
#   connections = Σ(FindConnections)(SimpsonsLikes)
#   deduped = distinct(connections)
```

Note: Mappings with `lambda` expressions (used for the `FindConnections`
and `Merge` mappings above) still require the `cql"""..."""` string
syntax. The DSL covers typesides, schemas, and instances. The functional
API (`Σ(F)(I)`, `distinct(I)`) works with any mapping or instance
object.

## Summary

| Concept | Description |
|----|----|
| **Generator equations** | `a = c` directly merges two elements |
| **Sigma (pushforward)** | Pushes an instance along a mapping, merging elements that map to the same target |
| **Connected components** | Map all entities to one entity; sigma computes transitive closure |
| **Quotient** | The result of sigma is the quotient by the equivalence relation induced by the mapping |
| **Deduplication** | Map multiple source entities to one target; sigma unifies the data |

CQL’s sigma operation transforms a difficult graph-theoretic computation
(transitive closure, connected components, record deduplication) into a
simple, declarative mapping. The theorem prover handles all the
bookkeeping of equivalence classes automatically.
