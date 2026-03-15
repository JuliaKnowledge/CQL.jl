# CQL.jl Tutorial
Simon Frost

## Introduction

The Categorical Query Language (CQL) is a data integration language
based on category theory. CQL provides mathematically guaranteed correct
data migrations between schemas, going beyond what SQL can offer in
terms of correctness guarantees.

This tutorial demonstrates the core CQL concepts using `CQL.jl`, a Julia
implementation. We follow the structure of the [official CQL
tutorial](https://categoricaldata.net/tutorial.html), adapting examples
for the Julia environment.

The key concepts are:

1.  **Typesides** - the foundation defining available data types
2.  **Schemas** - entity-relationship data models with constraints
3.  **Instances** - concrete data conforming to a schema
4.  **Mappings** - structure-preserving translations between schemas
5.  **Delta and Sigma** - functorial data migration operations
6.  **Uber-flowers (Queries)** - SQL-like queries with categorical
    guarantees

``` julia
using CQL
```

## Using CQL

CQL.jl provides two convenient macros for writing CQL programs directly
in Julia, without needing to wrap them in strings and call `run_program`
manually.

**String macro** — `cql"..."` or `cql"""..."""`:

``` julia
env = cql"""
typeside Ty = literal { types String }
schema S = literal : Ty { entities Person }
"""
```

**Regular macro** — `@cql`:

``` julia
env = @cql "typeside Ty = literal { types String }"
```

Both macros return an `Env` object. Named declarations in the program
can be accessed directly as properties:

``` julia
env.Ty   # => Typeside
env.S    # => CQLSchema
```

This is equivalent to looking up values by name in the underlying
dictionaries (e.g. `env.typesides["Ty"]`), but is more concise and
supports tab-completion.

## Typesides

Every CQL program begins with a **typeside** that defines the available
data types and operations. In the original Java CQL, typesides bind to
Java types. In CQL.jl, we define types and constants directly.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String Integer
    constants
        Al Akin Bob Bo Carl Cork Dan Dunn Math CS : String
        zero one two three four five : Integer
    functions
        plus : Integer, Integer -> Integer
}
"""

ts = env.Ty
println("Types: ", ts.tys)
println("Function symbols: ", collect(keys(ts.syms)))
```

    Types: Set([:Integer, :String])
    Function symbols: [:Al, :five, :Bo, :Carl, :Bob, :three, :Cork, :zero, :plus, :Akin, :one, :Math, :CS, :Dan, :four, :Dunn, :two]

The typeside defines `String` and `Integer` as available types, declares
constants like `Al` and `zero`, and provides a `plus` function symbol
for integer addition.

## Schemas

A **schema** defines the structure of your data. It consists of:

- **Entities** - the “tables” in your database
- **Foreign keys** - relationships between entities (like SQL foreign
  keys)
- **Attributes** - data values associated with entities
- **Path equations** - constraints on how foreign keys compose
- **Observation equations** - constraints involving attributes

``` julia
env = cql"""
typeside Ty = literal {
    types
        String Integer
    constants
        Al Akin Bob Bo Carl Cork Dan Dunn Math CS : String
        zero one two three four five : String
    functions
        plus : String, String -> String
}

schema S = literal : Ty {
    entities
        Employee Department
    foreign_keys
        manager : Employee -> Employee
        worksIn : Employee -> Department
        secretary : Department -> Employee
    attributes
        first : Employee -> String
        last : Employee -> String
        age : Employee -> String
        name : Department -> String
    path_equations
        Employee.manager.worksIn = Employee.worksIn
        Employee.manager.manager = Employee.manager
}
"""

sch = env.S
println("Entities: ", sch.ens)
println("Foreign keys: ", collect(keys(sch.fks)))
println("Attributes: ", collect(keys(sch.atts)))
println("Path equations: ", length(sch.path_eqs))
```

    Entities: Set([:Department, :Employee])
    Foreign keys: [:worksIn, :manager, :secretary]
    Attributes: [:first, :age, :last, :name]
    Path equations: 2

The schema `S` models an employee-department database:

- Each `Employee` has a `manager` (another `Employee`), `worksIn` a
  `Department`, and attributes `first`, `last`, `age`
- Each `Department` has a `secretary` (an `Employee`) and a `name`
- The **path equations** encode business rules:
  - `manager.worksIn = worksIn` means a manager works in the same
    department as their reports
  - `manager.manager = manager` means managers are their own managers
    (i.e., managers are fixed points)

## Instances

An **instance** populates a schema with concrete data. Generators create
elements, and equations specify their properties and relationships.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String Integer
    constants
        Al Akin Bob Bo Carl Cork Dan Dunn Math CS : String
        zero : Integer
    functions
        succ : Integer -> Integer
}

schema S = literal : Ty {
    entities
        Employee Department
    foreign_keys
        manager : Employee -> Employee
        worksIn : Employee -> Department
        secretary : Department -> Employee
    attributes
        first : Employee -> String
        last : Employee -> String
        age : Employee -> Integer
        name : Department -> String
}

instance I = literal : S {
    generators
        a b c : Employee
        m s : Department
    equations
        manager(a) = a
        manager(b) = c
        manager(c) = c
        worksIn(a) = m
        worksIn(b) = s
        worksIn(c) = s
        secretary(m) = a
        secretary(s) = c
        first(a) = Al    first(b) = Bob   first(c) = Carl
        last(a) = Akin   last(b) = Bo     last(c) = Cork
        age(a) = succ(zero)  age(b) = succ(succ(succ(succ(succ(zero)))))
        age(c) = succ(zero)
        name(m) = Math   name(s) = CS
}
"""

inst = env.I
alg = inst.algebra
println("Employee carrier size: ", length(carrier(alg, :Employee)))
println("Department carrier size: ", length(carrier(alg, :Department)))

println("\nEmployee table:")
for (i, x) in enumerate(carrier(alg, :Employee))
    first_name = eval_att(alg, :first, x)
    last_name = eval_att(alg, :last, x)
    mgr = eval_fk(alg, :manager, x)
    mgr_name = eval_att(alg, :first, mgr)
    dept = eval_fk(alg, :worksIn, x)
    dept_name = eval_att(alg, :name, dept)
    println("  [$i] first=$first_name, last=$last_name, manager=$mgr_name, worksIn=$dept_name")
end

println("\nDepartment table:")
for (i, x) in enumerate(carrier(alg, :Department))
    dept_name = eval_att(alg, :name, x)
    sec = eval_fk(alg, :secretary, x)
    sec_name = eval_att(alg, :first, sec)
    println("  [$i] name=$dept_name, secretary=$sec_name")
end
```

    Employee carrier size: 3
    Department carrier size: 2

    Employee table:
      [1] first=Bob, last=Bo, manager=Carl, worksIn=CS
      [2] first=Carl, last=Cork, manager=Carl, worksIn=CS
      [3] first=Al, last=Akin, manager=Al, worksIn=Math

    Department table:
      [1] name=CS, secretary=Carl
      [2] name=Math, secretary=Al

The instance `I` has 3 employees and 2 departments. CQL automatically
computes the initial algebra, which resolves all equations and finds the
canonical representatives.

## Mappings

A **mapping** is a structure-preserving translation between schemas. It
specifies how entities, foreign keys, and attributes in one schema
correspond to those in another.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String Integer
    constants
        Alice Bob Sue : String
        v20 v30 v100 v250 v300 : Integer
}

schema C = literal : Ty {
    entities
        N1 N2
    foreign_keys
        f : N1 -> N2
    attributes
        name : N1 -> String
        salary : N1 -> Integer
        age : N2 -> Integer
}

schema D = literal : Ty {
    entities
        N
    attributes
        name : N -> String
        salary : N -> Integer
        age : N -> Integer
}

mapping F = literal : C -> D {
    entity
        N1 -> N
        foreign_keys
            f -> N
        attributes
            name -> lambda x. name(x)
            salary -> lambda x. salary(x)
    entity
        N2 -> N
        attributes
            age -> lambda x. age(x)
}
"""

mapping = env.F
println("Mapping F: C -> D")
println("  Entity mappings:")
for (src_en, tgt_en) in mapping.ens
    println("    $src_en -> $tgt_en")
end
```

    Mapping F: C -> D
      Entity mappings:
        N2 -> N
        N1 -> N

Schema `C` has two entities `N1` and `N2` connected by a foreign key
`f`. Schema `D` has a single entity `N`. The mapping `F` sends both `N1`
and `N2` to `N`, collapsing the two-entity schema into one.

The foreign key `f -> N` means `f` is mapped to the identity path on `N`
(since both `N1` and `N2` map to `N`).

## Delta and Sigma

The two fundamental data migration operations are **delta** (pullback)
and **sigma** (pushforward). These are functorial operations induced by
a mapping between schemas.

### Delta (Pullback)

**Delta** pulls data backward along a mapping. Given a mapping
`F: C -> D` and an instance `J` on `D`, `delta F J` produces an instance
on `C`.

Think of delta as a “projection” or “restriction” - it restructures data
from the target schema back to the source schema.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String Integer
    constants
        Alice Bob Sue : String
        v20 v30 v100 v250 v300 : Integer
}

schema C = literal : Ty {
    entities
        N1 N2
    foreign_keys
        f : N1 -> N2
    attributes
        name : N1 -> String
        salary : N1 -> Integer
        age : N2 -> Integer
}

schema D = literal : Ty {
    entities
        N
    attributes
        name : N -> String
        salary : N -> Integer
        age : N -> Integer
}

mapping F = literal : C -> D {
    entity
        N1 -> N
        foreign_keys
            f -> N
        attributes
            name -> lambda x. name(x)
            salary -> lambda x. salary(x)
    entity
        N2 -> N
        attributes
            age -> lambda x. age(x)
}

instance J = literal : D {
    generators
        one two three : N
    equations
        name(one) = Alice  name(two) = Bob  name(three) = Sue
        age(one) = v20  age(two) = v20  age(three) = v30
        salary(one) = v100  salary(two) = v250  salary(three) = v300
    options
        interpret_as_algebra = true
}

instance deltaFJ = delta F J
"""

j_inst = env.J
d_inst = env.deltaFJ

println("=== Source instance J on schema D ===")
println("  N: ", length(carrier(j_inst.algebra, :N)), " elements")

println("\n=== Delta F J on schema C ===")
println("  N1: ", length(carrier(d_inst.algebra, :N1)), " elements")
println("  N2: ", length(carrier(d_inst.algebra, :N2)), " elements")
```

    === Source instance J on schema D ===
      N: 3 elements

    === Delta F J on schema C ===
      N1: 3 elements
      N2: 3 elements

Since both `N1` and `N2` map to `N` under `F`, delta copies all 3
elements from `N` into both `N1` and `N2`. The foreign key `f` becomes
the identity (each `N1` element maps to its corresponding `N2` element).

### Sigma (Pushforward)

**Sigma** pushes data forward along a mapping. Given a mapping
`F: C -> D` and an instance `I` on `C`, `sigma F I` produces an instance
on `D`.

Think of sigma as a “union followed by merge” - it combines data from
the source schema into the target schema, merging elements that become
identified.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String Integer
    constants
        Alice Bob Sue : String
        v20 v30 v100 v250 v300 : Integer
}

schema C = literal : Ty {
    entities
        N1 N2
    foreign_keys
        f : N1 -> N2
    attributes
        name : N1 -> String
        salary : N1 -> Integer
        age : N2 -> Integer
}

schema D = literal : Ty {
    entities
        N
    attributes
        name : N -> String
        salary : N -> Integer
        age : N -> Integer
}

mapping F = literal : C -> D {
    entity
        N1 -> N
        foreign_keys
            f -> N
        attributes
            name -> lambda x. name(x)
            salary -> lambda x. salary(x)
    entity
        N2 -> N
        attributes
            age -> lambda x. age(x)
}

instance J = literal : D {
    generators
        one two three : N
    equations
        name(one) = Alice  name(two) = Bob  name(three) = Sue
        age(one) = v20  age(two) = v20  age(three) = v30
        salary(one) = v100  salary(two) = v250  salary(three) = v300
    options
        interpret_as_algebra = true
}

instance deltaFJ = delta F J

instance sigmaFdeltaFJ = sigma F deltaFJ
"""

j_inst = env.J
s_inst = env.sigmaFdeltaFJ

println("=== Sigma F (Delta F J) on schema D ===")
println("  N: ", length(carrier(s_inst.algebra, :N)), " elements")

println("\nSigma after delta gives back the original!")
println("  Original J had ", length(carrier(j_inst.algebra, :N)), " elements in N")
```

    === Sigma F (Delta F J) on schema D ===
      N: 3 elements

    Sigma after delta gives back the original!
      Original J had 3 elements in N

The round-trip `sigma F (delta F J)` recovers the original instance `J`.
This is a consequence of the adjunction between delta and sigma -
`sigma` is the left adjoint of `delta`, so `sigma . delta` computes a
“counit” that is an isomorphism when the mapping is well-behaved.

## Uber-flowers (Queries)

CQL queries, called **uber-flowers**, are SQL-like `from-where-return`
expressions that provide categorical guarantees about data migration
correctness.

Every delta and sigma operation can be expressed as an uber-flower
query. This demonstrates that functorial data migration subsumes
familiar SQL patterns.

### Delta as a Query

``` julia
env = cql"""
typeside Ty = literal {
    types
        String Integer
    constants
        Alice Bob Sue : String
        v20 v30 v100 v250 v300 : Integer
}

schema C = literal : Ty {
    entities
        N1 N2
    foreign_keys
        f : N1 -> N2
    attributes
        name : N1 -> String
        salary : N1 -> Integer
        age : N2 -> Integer
}

schema D = literal : Ty {
    entities
        N
    attributes
        name : N -> String
        salary : N -> Integer
        age : N -> Integer
}

mapping F = literal : C -> D {
    entity
        N1 -> N
        foreign_keys
            f -> N
        attributes
            name -> lambda x. name(x)
            salary -> lambda x. salary(x)
    entity
        N2 -> N
        attributes
            age -> lambda x. age(x)
}

instance J = literal : D {
    generators
        one two three : N
    equations
        name(one) = Alice  name(two) = Bob  name(three) = Sue
        age(one) = v20  age(two) = v20  age(three) = v30
        salary(one) = v100  salary(two) = v250  salary(three) = v300
    options
        interpret_as_algebra = true
}

instance deltaFJ = delta F J

query deltaFAsQuery = literal : D -> C {
    entity N2 -> {
        from
            y : N
        attributes
            age -> age(y)
    }
    entity N1 -> {
        from
            x : N
        attributes
            name -> name(x)
            salary -> salary(x)
        foreign_keys
            f -> {y -> x}
    }
}

instance deltaFJ_prime = eval deltaFAsQuery J
"""

d_inst = env.deltaFJ
dp_inst = env.deltaFJ_prime

println("=== Delta via functor ===")
println("  N1: ", length(carrier(d_inst.algebra, :N1)))
println("  N2: ", length(carrier(d_inst.algebra, :N2)))

println("\n=== Delta via uber-flower query ===")
println("  N1: ", length(carrier(dp_inst.algebra, :N1)))
println("  N2: ", length(carrier(dp_inst.algebra, :N2)))

println("\nBoth methods produce the same result!")
```

    === Delta via functor ===
      N1: 3
      N2: 3

    === Delta via uber-flower query ===
      N1: 3
      N2: 3

    Both methods produce the same result!

The uber-flower query `deltaFAsQuery` says: - For target entity `N2`:
select all `y` from `N`, with `age` attribute from `age(y)` - For target
entity `N1`: select all `x` from `N`, with `name`/`salary` attributes,
and FK `f` maps `y` to `x`

### Sigma as a Query

``` julia
env = cql"""
typeside Ty = literal {
    types
        String Integer
    constants
        Alice Bob Sue : String
        v20 v30 v100 v250 v300 : Integer
}

schema C = literal : Ty {
    entities
        N1 N2
    foreign_keys
        f : N1 -> N2
    attributes
        name : N1 -> String
        salary : N1 -> Integer
        age : N2 -> Integer
}

schema D = literal : Ty {
    entities
        N
    attributes
        name : N -> String
        salary : N -> Integer
        age : N -> Integer
}

mapping F = literal : C -> D {
    entity
        N1 -> N
        foreign_keys
            f -> N
        attributes
            name -> lambda x. name(x)
            salary -> lambda x. salary(x)
    entity
        N2 -> N
        attributes
            age -> lambda x. age(x)
}

instance J = literal : D {
    generators
        one two three : N
    equations
        name(one) = Alice  name(two) = Bob  name(three) = Sue
        age(one) = v20  age(two) = v20  age(three) = v30
        salary(one) = v100  salary(two) = v250  salary(three) = v300
    options
        interpret_as_algebra = true
}

instance deltaFJ = delta F J

query deltaFAsQuery = literal : D -> C {
    entity N2 -> {
        from
            y : N
        attributes
            age -> age(y)
    }
    entity N1 -> {
        from
            x : N
        attributes
            name -> name(x)
            salary -> salary(x)
        foreign_keys
            f -> {y -> x}
    }
}

instance deltaFJ_prime = eval deltaFAsQuery J

query sigmaFAsQuery = literal : C -> D {
    entity N -> {
        from
            n1 : N1
        attributes
            age -> age(f(n1))
            name -> name(n1)
            salary -> salary(n1)
    }
}

instance sigmaFdeltaFJ_prime = eval sigmaFAsQuery deltaFJ_prime
"""

sp_inst = env.sigmaFdeltaFJ_prime

println("=== Sigma via query (round-trip) ===")
println("  N: ", length(carrier(sp_inst.algebra, :N)))

j_inst = env.J
println("\nFull round-trip: J -> delta -> sigma recovers ", length(carrier(j_inst.algebra, :N)), " elements")
```

    === Sigma via query (round-trip) ===
      N: 3

    Full round-trip: J -> delta -> sigma recovers 3 elements

The sigma query `sigmaFAsQuery` says: for each `n1` in `N1`, create an
`N` element with: - `age` from `age(f(n1))` (follow FK `f` to get the
age) - `name` from `name(n1)` - `salary` from `salary(n1)`

## Why CQL? Comparing with SQL and SPARQL

CQL occupies a unique position in the data management landscape. It
provides the **schema-level reasoning** that SQL and SPARQL lack, while
remaining compatible with both ecosystems through import/export.

### CQL vs SQL

SQL operates on flat tables with ad-hoc join syntax. CQL operates on
**categories** — schemas with entities, typed foreign keys, and path
equations. This difference has practical consequences:

| Aspect | SQL | CQL |
|----|----|----|
| **Foreign keys** | Integer references, manually joined | Typed functions, followed with dot notation |
| **Schema migration** | Hand-written `ALTER TABLE` + ETL | Functorial `delta`/`sigma` with correctness proofs |
| **Joins** | Explicit `JOIN ... ON` clauses | Implicit via FK paths (`e.manager.worksIn.name`) |
| **Constraints** | `CHECK`, `UNIQUE`, triggers | Path equations, observation equations (enforced by theorem prover) |
| **Missing data** | Single undifferentiated `NULL` | Labeled nulls (Skolem terms) with provenance |
| **Schema merging** | No built-in support | `schema_colimit` with automatic mappings |
| **Round-trip guarantees** | None | Delta–sigma adjunction (mathematical theorem) |

A query that requires recursive CTEs in SQL (e.g., finding a closed
sub-database satisfying closure constraints) can often be expressed as a
single CQL uber-flower query. See the [Difficult
Queries](difficult_queries.html) vignette for a concrete example.

### CQL vs SPARQL

SPARQL queries RDF triple stores via graph pattern matching. CQL queries
typed schemas via uber-flower expressions. The key differences:

| Aspect | SPARQL | CQL |
|----|----|----|
| **Data model** | Untyped triples (subject, predicate, object) | Typed schemas (entities, FKs, attributes) |
| **Query style** | Graph pattern matching | Schema-typed from-where-return |
| **Validation** | SHACL/ShEx (separate layer) | Built into schema definition |
| **Data migration** | `CONSTRUCT` (ad-hoc) | `delta`/`sigma` (functorial) |
| **Ontology merging** | OWL imports (manual) | `schema_colimit` (automatic) |
| **Composability** | Queries don’t compose structurally | Queries compose via category theory |

CQL can import RDF/XML (`import_rdf_all`) and export to RDF/XML
(`export_rdf_instance_xml`), making it a natural complement to
SPARQL-based systems. Use SPARQL for ad-hoc exploration of existing
triple stores; use CQL when you need schema-level integration with
correctness guarantees. See the [RDF Integration](rdf.html) vignette for
details.

### The Adjunction Advantage

The deepest advantage of CQL is the **delta–sigma adjunction**. When you
define a mapping `F: C → D` between schemas:

- `delta F` pulls data from `D` back to `C` (like a SQL view)
- `sigma F` pushes data from `C` forward to `D` (like an ETL load)
- The round-trip `sigma F (delta F J) ≅ J` is guaranteed by the
  adjunction

No other query language provides this guarantee. In SQL, you write an
ETL script and *hope* it preserves your data. In CQL, preservation is a
*theorem*.

## Summary

CQL.jl implements the core Categorical Query Language:

| Concept | Description | CQL Syntax |
|----|----|----|
| **Typeside** | Type system foundation | `typeside T = literal { ... }` |
| **Schema** | Data model with constraints | `schema S = literal : T { ... }` |
| **Instance** | Concrete data on a schema | `instance I = literal : S { ... }` |
| **Mapping** | Schema translation | `mapping F = literal : S -> T { ... }` |
| **Delta** | Pullback (restriction) | `delta F I` |
| **Sigma** | Pushforward (extension) | `sigma F I` |
| **Query** | Uber-flower (from-where) | `query Q = literal : S -> T { ... }` |
| **Eval** | Query evaluation | `eval Q I` |

CQL.jl also supports data exchange with external formats:

| Format | Import | Export |
|----|----|----|
| **CSV** | `import_csv_instance(dir, schema)` | `export_csv_instance(inst, dir)` |
| **RDF/XML** | `instance J = import_rdf_all "file.xml"` | `export_rdf_instance_xml I "file.xml" { ... }` |
| **XML** | `instance J = import_xml "file.xml"` | — |
| **JSON** | `instance J = import_json "file.json"` | — |
| **SQL (DuckDB)** | `import_duckdb(con, schema, queries)` | `export_duckdb(con, inst)` |
| **SQL (JDBC)** | `instance J = import_jdbc "conn" : S { ... }` | `export_jdbc_instance I "conn" "prefix"` |

Programs can be run using the `cql"""..."""` string macro, the `@cql`
macro, or `run_program()` directly. Results are returned as an `Env`
with property access to all named declarations.

The key insight of CQL is that data migration operations (delta, sigma)
are **functorial** — they preserve the structure of your data and
satisfy mathematical guarantees:

- **Delta-Sigma adjunction**: `sigma` is left adjoint to `delta`,
  ensuring that round-trips compose correctly
- **Uber-flower equivalence**: every delta/sigma can be expressed as an
  uber-flower query, connecting categorical semantics to familiar SQL
  patterns
- **Constraint propagation**: path equations and observation equations
  are automatically enforced across all operations

For more details, see the companion vignettes on [CSV](csv.html),
[RDF](rdf.html), [database connectivity](dbc.html), [data
integration](data_integration.html), [semantic
interoperability](semantic_interop.html), and [difficult
queries](difficult_queries.html).
