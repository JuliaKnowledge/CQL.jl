# Joinless Queries in CQL
Simon Frost

## Introduction

One of CQL’s most practical advantages over SQL is that **foreign keys
can be followed (dereferenced) directly**, so that many constructions
requiring joins in SQL don’t require joins in CQL. In SQL, navigating a
chain of foreign keys requires explicit `JOIN` clauses for each hop. In
CQL, you simply write `p.instituteOf.biggestDept.deptName` to follow a
chain of foreign keys and read an attribute at the end.

This vignette demonstrates:

1.  A multi-entity schema with chains of foreign keys
2.  A CQL query that filters by navigating a three-hop FK chain
3.  How this translates to a multi-join SQL query
4.  How CQL’s direct FK dereferencing simplifies the query

This example is adapted from the [CQL joinless queries
tutorial](https://categoricaldata.net/joinless.html).

``` julia
using CQL
```

## Schema: Schools, People, and Departments

Consider a database about academic institutions. Each **person** works
at a **school** and belongs to a **department**. Each school has a
designated **biggest department**.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Wisnesky Spivak Chlipala Morrisett Malecha Gross
        Harvard MIT Mathematics CompSci : String
}

schema Schools = literal : Ty {
    entities
        Person
        School
        Dept
    foreign_keys
        instituteOf : Person -> School
        deptOf      : Person -> Dept
        biggestDept : School -> Dept
    attributes
        lastName   : Person -> String
        schoolName : School -> String
        deptName   : Dept   -> String
}
"""

sch = env.Schools
println("Entities: ", sch.ens)
println("Foreign keys: ", collect(keys(sch.fks)))
println("Attributes: ", collect(keys(sch.atts)))
```

    Entities: Set([:Dept, :School, :Person])
    Foreign keys: [:biggestDept, :instituteOf, :deptOf]
    Attributes: [:deptName, :lastName, :schoolName]

The foreign key structure creates a navigable graph:

    Person --instituteOf--> School --biggestDept--> Dept
    Person --deptOf-------> Dept

From any person, we can follow the chain
`instituteOf.biggestDept.deptName` to find the name of the biggest
department at their school — traversing two foreign keys and one
attribute.

## Sample Data: Boston Schools

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Wisnesky Spivak Chlipala Morrisett Malecha Gross
        Harvard MIT Mathematics CompSci : String
}

schema Schools = literal : Ty {
    entities
        Person
        School
        Dept
    foreign_keys
        instituteOf : Person -> School
        deptOf      : Person -> Dept
        biggestDept : School -> Dept
    attributes
        lastName   : Person -> String
        schoolName : School -> String
        deptName   : Dept   -> String
}

instance BostonSchools = literal : Schools {
    generators
        ryan david adam greg gregory jason : Person
        harvard mit : School
        math cs : Dept
    multi_equations
        lastName    -> {ryan Wisnesky, david Spivak, adam Chlipala, greg Morrisett,
                        gregory Malecha, jason Gross}
        schoolName  -> {harvard Harvard, mit MIT}
        deptName    -> {math Mathematics, cs CompSci}
        instituteOf -> {ryan harvard, david mit, adam mit, greg harvard,
                        gregory harvard, jason mit}
        deptOf      -> {ryan math, david math, adam cs, greg cs, gregory cs, jason cs}
        biggestDept -> {harvard math, mit cs}
}
"""

alg = env.BostonSchools.algebra

println("=== Person Table ===")
println("Name         | School  | Department   | School's Biggest Dept")
println("-------------+---------+--------------+---------------------")
for x in carrier(alg, :Person)
    nm = eval_att(alg, :lastName, x)
    sch = eval_fk(alg, :instituteOf, x)
    snm = eval_att(alg, :schoolName, sch)
    dept = eval_fk(alg, :deptOf, x)
    dnm = eval_att(alg, :deptName, dept)
    bd = eval_fk(alg, :biggestDept, sch)
    bdnm = eval_att(alg, :deptName, bd)
    println(rpad(string(nm), 13), "| ", rpad(string(snm), 8), "| ",
            rpad(string(dnm), 13), "| ", bdnm)
end

println("\n=== School Table ===")
println("School  | Biggest Dept")
println("--------+-------------")
for x in carrier(alg, :School)
    snm = eval_att(alg, :schoolName, x)
    bd = eval_fk(alg, :biggestDept, x)
    bdnm = eval_att(alg, :deptName, bd)
    println(rpad(string(snm), 8), "| ", bdnm)
end
```

    === Person Table ===
    Name         | School  | Department   | School's Biggest Dept
    -------------+---------+--------------+---------------------
    Chlipala     | MIT     | CompSci      | CompSci
    Spivak       | MIT     | Mathematics  | CompSci
    Morrisett    | Harvard | CompSci      | Mathematics
    Malecha      | Harvard | CompSci      | Mathematics
    Wisnesky     | Harvard | Mathematics  | Mathematics
    Gross        | MIT     | CompSci      | CompSci

    === School Table ===
    School  | Biggest Dept
    --------+-------------
    MIT     | CompSci
    Harvard | Mathematics

## The Query: Who Works at a “Math School”?

We want to find all people who work at a school whose biggest department
is Mathematics. In SQL, this requires **two joins**:

``` sql
SELECT p.lastName, s.schoolName
FROM Person p
JOIN School s ON p.instituteOf = s.id
JOIN Dept d ON s.biggestDept = d.id
WHERE d.deptName = 'Mathematics'
```

In CQL, this is a single query with **no joins** — just direct FK
dereferencing in the where-clause:

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Wisnesky Spivak Chlipala Morrisett Malecha Gross
        Harvard MIT Mathematics CompSci : String
}

schema Schools = literal : Ty {
    entities
        Person
        School
        Dept
    foreign_keys
        instituteOf : Person -> School
        deptOf      : Person -> Dept
        biggestDept : School -> Dept
    attributes
        lastName   : Person -> String
        schoolName : School -> String
        deptName   : Dept   -> String
}

schema PersonFlat = literal : Ty {
    entities
        Person
    attributes
        lastName   : Person -> String
        schoolName : Person -> String
}

query BiggestDeptIsMath = literal : Schools -> PersonFlat {
    entity Person -> {
        from
            p : Person
        where
            p.instituteOf.biggestDept.deptName = Mathematics
        attributes
            lastName   -> p.lastName
            schoolName -> p.instituteOf.schoolName
    }
}

instance BostonSchools = literal : Schools {
    generators
        ryan david adam greg gregory jason : Person
        harvard mit : School
        math cs : Dept
    multi_equations
        lastName    -> {ryan Wisnesky, david Spivak, adam Chlipala, greg Morrisett,
                        gregory Malecha, jason Gross}
        schoolName  -> {harvard Harvard, mit MIT}
        deptName    -> {math Mathematics, cs CompSci}
        instituteOf -> {ryan harvard, david mit, adam mit, greg harvard,
                        gregory harvard, jason mit}
        deptOf      -> {ryan math, david math, adam cs, greg cs, gregory cs, jason cs}
        biggestDept -> {harvard math, mit cs}
}

instance Result = eval BiggestDeptIsMath BostonSchools
"""

println(env.BiggestDeptIsMath)
```

    query {
      entity Person -> {
        from
          p : Person
        where
          p.instituteOf.biggestDept.deptName = Mathematics
      }
      attributes
        lastName -> p.lastName
        schoolName -> p.instituteOf.schoolName
    }

### Understanding the Query

The key is the where-clause:

    p.instituteOf.biggestDept.deptName = Mathematics

This reads: “starting from person `p`, follow `instituteOf` to their
school, then follow `biggestDept` to that school’s biggest department,
then read `deptName` — and check that it equals `Mathematics`.”

No join tables, no aliases, no ON clauses. Just direct navigation along
the foreign key graph.

The attributes section maps the selected person’s data into the flat
output schema:

- `lastName -> p.lastName` — direct attribute
- `schoolName -> p.instituteOf.schoolName` — follow one FK then read
  attribute

## Query Results

``` julia
alg_r = env.Result.algebra

println("Query: People at schools where biggest dept is Mathematics")
println("Result: ", length(carrier(alg_r, :Person)), " people\n")

println("Name         | School")
println("-------------+---------")
for x in carrier(alg_r, :Person)
    nm = eval_att(alg_r, :lastName, x)
    snm = eval_att(alg_r, :schoolName, x)
    println(rpad(string(nm), 13), "| ", snm)
end
```

    Query: People at schools where biggest dept is Mathematics
    Result: 3 people

    Name         | School
    -------------+---------
    Wisnesky     | Harvard
    Morrisett    | Harvard
    Malecha      | Harvard

Only the three Harvard people survive the filter, because Harvard’s
biggest department is Mathematics while MIT’s is CompSci.

## CQL vs SQL Side-by-Side

To appreciate the difference, here’s the same query in both languages:

**CQL:**

    query BiggestDeptIsMath = literal : Schools -> PersonFlat {
        entity Person -> {
            from p : Person
            where p.instituteOf.biggestDept.deptName = Mathematics
            attributes
                lastName   -> p.lastName
                schoolName -> p.instituteOf.schoolName
        }
    }

**SQL:**

``` sql
SELECT p.lastName, s.schoolName
FROM Person p
JOIN School s ON p.instituteOf = s.id
JOIN Dept d ON s.biggestDept = d.id
WHERE d.deptName = 'Mathematics'
```

| Aspect | SQL | CQL |
|----|----|----|
| **FK navigation** | Explicit JOIN for each hop | Dot notation (`p.instituteOf.biggestDept`) |
| **Join conditions** | Manual ON clauses | Automatic (built into schema) |
| **3-hop path** | 2 JOINs + WHERE | Single where-clause |
| **Type safety** | Runtime errors | Schema-level checking |

As the number of hops increases, the SQL query grows linearly in JOIN
clauses while the CQL path expression simply gets longer dots. For a
5-hop path like `p.a.b.c.d.e`, SQL would need 5 JOIN clauses, while CQL
remains a single expression.

## A Second Query: Department Membership

Let’s write another query that filters by a person’s own department:

``` julia
env2 = cql"""
typeside Ty = literal {
    types
        String
    constants
        Wisnesky Spivak Chlipala Morrisett Malecha Gross
        Harvard MIT Mathematics CompSci : String
}

schema Schools = literal : Ty {
    entities
        Person
        School
        Dept
    foreign_keys
        instituteOf : Person -> School
        deptOf      : Person -> Dept
        biggestDept : School -> Dept
    attributes
        lastName   : Person -> String
        schoolName : School -> String
        deptName   : Dept   -> String
}

schema PersonFlat = literal : Ty {
    entities
        Person
    attributes
        lastName   : Person -> String
        schoolName : Person -> String
}

query CompSciQuery = literal : Schools -> PersonFlat {
    entity Person -> {
        from
            p : Person
        where
            p.deptOf.deptName = CompSci
        attributes
            lastName   -> p.lastName
            schoolName -> p.instituteOf.schoolName
    }
}

instance BostonSchools = literal : Schools {
    generators
        ryan david adam greg gregory jason : Person
        harvard mit : School
        math cs : Dept
    multi_equations
        lastName    -> {ryan Wisnesky, david Spivak, adam Chlipala, greg Morrisett,
                        gregory Malecha, jason Gross}
        schoolName  -> {harvard Harvard, mit MIT}
        deptName    -> {math Mathematics, cs CompSci}
        instituteOf -> {ryan harvard, david mit, adam mit, greg harvard,
                        gregory harvard, jason mit}
        deptOf      -> {ryan math, david math, adam cs, greg cs, gregory cs, jason cs}
        biggestDept -> {harvard math, mit cs}
}

instance CompSciResult = eval CompSciQuery BostonSchools
"""

alg_cs = env2.CompSciResult.algebra

println("Query: People in CompSci department")
println("Result: ", length(carrier(alg_cs, :Person)), " people\n")

println("Name         | School")
println("-------------+---------")
for x in carrier(alg_cs, :Person)
    nm = eval_att(alg_cs, :lastName, x)
    snm = eval_att(alg_cs, :schoolName, x)
    println(rpad(string(nm), 13), "| ", snm)
end
```

    Query: People in CompSci department
    Result: 4 people

    Name         | School
    -------------+---------
    Malecha      | Harvard
    Gross        | MIT
    Chlipala     | MIT
    Morrisett    | Harvard

This query (`p.deptOf.deptName = CompSci`) is a single-hop FK traversal,
equivalent to a SQL query with one JOIN. The CQL syntax is identical in
structure — just a shorter path.

## Julia DSL

The examples above use the `cql"""..."""` string macro. CQL.jl also
provides Julia-native macros. Here is how the Schools schema and the
joinless query look using the DSL:

``` julia
using CQL

Ty = @typeside begin
    String::Ty
    Wisnesky::String; Spivak::String; Chlipala::String; Morrisett::String
    Malecha::String; Gross::String
    Harvard::String; MIT::String; Mathematics::String; CompSci::String
end

Schools = @schema Ty begin
    @entities Person, School, Dept
    instituteOf : Person → School
    deptOf : Person → Dept
    biggestDept : School → Dept
    lastName : Person ⇒ String
    schoolName : School ⇒ String
    deptName : Dept ⇒ String
end

PersonFlat = @schema Ty begin
    @entities Person
    lastName : Person ⇒ String
    schoolName : Person ⇒ String
end

# The @query macro supports dot-path FK chain navigation in @where and @return
BiggestDeptIsMath = @query Schools → PersonFlat begin
    @entity Person begin
        @from p => Person
        @where p.instituteOf.biggestDept.deptName == Mathematics
        lastName => p.lastName
        schoolName => p.instituteOf.schoolName
    end
end

println("Entities: ", Schools.ens)
println("Foreign keys: ", collect(keys(Schools.fks)))
```

    Entities: Set([:Dept, :School, :Person])
    Foreign keys: [:biggestDept, :instituteOf, :deptOf]

The `@where` clause uses dot-path notation
(`p.instituteOf.biggestDept.deptName`) to follow the FK chain directly,
and the attribute return `p.instituteOf.schoolName` follows one FK then
reads an attribute — no joins needed.

## Summary

| Concept | Description |
|----|----|
| **FK dereferencing** | `p.fk1.fk2.att` follows foreign keys then reads an attribute |
| **Where-clauses** | Filter by comparing FK-derived values to constants |
| **No explicit joins** | CQL’s schema already encodes the join structure |
| **Attribute mapping** | `att -> p.fk.att` projects FK-derived values into the output |

CQL’s joinless query style makes multi-table queries more readable and
less error-prone. The schema defines the foreign key structure once, and
queries simply navigate it. This is especially valuable in complex
schemas with many interconnected entities, where SQL queries become a
thicket of JOIN clauses.
