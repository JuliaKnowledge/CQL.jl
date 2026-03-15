# Foreign Key Queries in CQL
Simon Frost

## Introduction

When integrating data, we often need to **reshape** it: the source
database has one structure, but the target needs a different one. A
common case is computing a **join** — finding all pairs of records from
different tables that share a common value. In SQL this requires
explicit `JOIN` clauses. In CQL, joins arise naturally from
**multi-variable queries** with **where-clauses**.

This vignette demonstrates:

1.  A university schema with professors, students, and departments
2.  A target schema with **advisor matches** and a **path equation**
    constraint
3.  A CQL query that computes all professor-student pairs in the same
    department
4.  How path equations in the target schema enforce relational integrity

This example is adapted from the [CQL foreign key
tutorial](https://categoricaldata.net/fk.html).

``` julia
using CQL
```

## Source Schema: A University

The university has three entities: professors, students, and
departments. Each professor works in a department, and each student
majors in a department.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Math CompSci English
        Wisnesky Spivak Chlipala Morrisett : String
}

schema University = literal : Ty {
    entities
        Professor
        Student
        Department
    foreign_keys
        worksIn    : Professor -> Department
        majoringIn : Student   -> Department
    attributes
        profName : Professor  -> String
        studName : Student    -> String
        deptName : Department -> String
}
"""

sch = env.University
println("Entities: ", sch.ens)
println("Foreign keys: ", collect(keys(sch.fks)))
println("Attributes: ", collect(keys(sch.atts)))
```

    Entities: Set([:Professor, :Department, :Student])
    Foreign keys: [:worksIn, :majoringIn]
    Attributes: [:deptName, :studName, :profName]

The foreign key structure is straightforward:

    Professor --worksIn----> Department
    Student   --majoringIn-> Department

Both professors and students point to departments, but there is no
direct link between professors and students.

## Sample Data: University of X

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Math CompSci English
        Wisnesky Spivak Chlipala Morrisett : String
}

schema University = literal : Ty {
    entities
        Professor
        Student
        Department
    foreign_keys
        worksIn    : Professor -> Department
        majoringIn : Student   -> Department
    attributes
        profName : Professor  -> String
        studName : Student    -> String
        deptName : Department -> String
}

instance UniversityOfX = literal : University {
    generators
        prof_w prof_s prof_c prof_m : Professor
        stud_a stud_b stud_c stud_d : Student
        math compsci english : Department
    multi_equations
        profName   -> {prof_w Wisnesky, prof_s Spivak, prof_c Chlipala, prof_m Morrisett}
        studName   -> {stud_a Wisnesky, stud_b Spivak, stud_c Chlipala, stud_d Morrisett}
        deptName   -> {math Math, compsci CompSci, english English}
        worksIn    -> {prof_w math, prof_s math, prof_c compsci, prof_m compsci}
        majoringIn -> {stud_a math, stud_b compsci, stud_c compsci, stud_d english}
}
"""

alg = env.UniversityOfX.algebra

println("=== Professors ===")
println("Name         | Department")
println("-------------+-----------")
for x in carrier(alg, :Professor)
    nm = eval_att(alg, :profName, x)
    dept = eval_fk(alg, :worksIn, x)
    dnm = eval_att(alg, :deptName, dept)
    println(rpad(string(nm), 13), "| ", dnm)
end

println("\n=== Students ===")
println("Name         | Major")
println("-------------+-----------")
for x in carrier(alg, :Student)
    nm = eval_att(alg, :studName, x)
    dept = eval_fk(alg, :majoringIn, x)
    dnm = eval_att(alg, :deptName, dept)
    println(rpad(string(nm), 13), "| ", dnm)
end
```

    === Professors ===
    Name         | Department
    -------------+-----------
    Morrisett    | CompSci
    Wisnesky     | Math
    Spivak       | Math
    Chlipala     | CompSci

    === Students ===
    Name         | Major
    -------------+-----------
    Spivak       | CompSci
    Chlipala     | CompSci
    Morrisett    | English
    Wisnesky     | Math

The data breaks down by department:

- **Math**: Professors Wisnesky and Spivak; Student Wisnesky
- **CompSci**: Professors Chlipala and Morrisett; Students Spivak and
  Chlipala
- **English**: No professors; Student Morrisett

## Target Schema: Advisor Matches

The target schema adds a `Match` entity that pairs a professor with a
student. The key feature is a **path equation** that constrains matches:

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Math CompSci English
        Wisnesky Spivak Chlipala Morrisett : String
}

schema AdvisorMatches = literal : Ty {
    entities
        Professor
        Student
        Department
        Match
    foreign_keys
        worksIn     : Professor -> Department
        majoringIn  : Student   -> Department
        professorOf : Match -> Professor
        studentOf   : Match -> Student
    attributes
        profName : Professor  -> String
        studName : Student    -> String
        deptName : Department -> String
    path_equations
        studentOf.majoringIn = professorOf.worksIn
}
"""

sch = env.AdvisorMatches
println("Entities: ", sch.ens)
println("Foreign keys: ", collect(keys(sch.fks)))
println("Path equations: ", length(sch.path_eqs), " equation(s)")
```

    Entities: Set([:Professor, :Department, :Match, :Student])
    Foreign keys: [:worksIn, :professorOf, :studentOf, :majoringIn]
    Path equations: 1 equation(s)

The path equation `studentOf.majoringIn = professorOf.worksIn` says: for
every match, the student’s department must equal the professor’s
department. This is a **schema-level constraint** — any instance of
`AdvisorMatches` must satisfy it.

                        professorOf
               Match ─────────────────> Professor
                 │                          │
      studentOf  │                          │ worksIn
                 ▼                          ▼
               Student ──────────────> Department
                        majoringIn

The path equation says: both paths from `Match` to `Department` must
agree.

## The Query: Finding Matches

The CQL query computes all valid professor-student pairs by using a
**multi-variable from-clause** with a **where-clause** that enforces the
department constraint:

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Math CompSci English
        Wisnesky Spivak Chlipala Morrisett : String
}

schema University = literal : Ty {
    entities
        Professor
        Student
        Department
    foreign_keys
        worksIn    : Professor -> Department
        majoringIn : Student   -> Department
    attributes
        profName : Professor  -> String
        studName : Student    -> String
        deptName : Department -> String
}

schema AdvisorMatches = literal : Ty {
    entities
        Professor
        Student
        Department
        Match
    foreign_keys
        worksIn     : Professor -> Department
        majoringIn  : Student   -> Department
        professorOf : Match -> Professor
        studentOf   : Match -> Student
    attributes
        profName : Professor  -> String
        studName : Student    -> String
        deptName : Department -> String
    path_equations
        studentOf.majoringIn = professorOf.worksIn
}

query findMatches = literal : University -> AdvisorMatches {
    entity Department -> {
        from
            d : Department
        attributes
            deptName -> d.deptName
    }
    entity Professor -> {
        from
            p : Professor
        attributes
            profName -> p.profName
        foreign_keys
            worksIn -> {d -> p.worksIn}
    }
    entity Student -> {
        from
            s : Student
        attributes
            studName -> s.studName
        foreign_keys
            majoringIn -> {d -> s.majoringIn}
    }
    entity Match -> {
        from
            p : Professor
            s : Student
        where
            p.worksIn = s.majoringIn
        foreign_keys
            professorOf -> {p -> p}
            studentOf   -> {s -> s}
    }
}
"""

println(env.findMatches)
```

    query {
      entity Professor -> {
        from
          p : Professor
      }
      entity Department -> {
        from
          d : Department
      }
      entity Match -> {
        from
          p : Professor
          s : Student
        where
          p.worksIn = s.majoringIn
      }
      entity Student -> {
        from
          s : Student
      }
      foreign_key worksIn -> {
        d -> p.worksIn
      }
      foreign_key professorOf -> {
        p -> p
      }
      foreign_key studentOf -> {
        s -> s
      }
      foreign_key majoringIn -> {
        d -> s.majoringIn
      }
      attributes
        deptName -> d.deptName
        studName -> s.studName
        profName -> p.profName
    }

### Understanding the Query

The query has four entity blocks, one for each target entity:

- **Department**: Copies departments directly (`from d : Department`)
- **Professor**: Copies professors, mapping `worksIn` to the
  corresponding department
- **Student**: Copies students, mapping `majoringIn` to the
  corresponding department
- **Match**: The interesting part — binds **two** source variables
  (`p : Professor`, `s : Student`) and constrains them with
  `p.worksIn = s.majoringIn`

The `Match` entity block performs the equivalent of a SQL join: it
enumerates all professor-student pairs and keeps only those where the
professor’s department equals the student’s major.

The `foreign_keys` section in the `Match` block maps back to the
professor and student:

- `professorOf -> {p -> p}` says the match’s professor is the bound
  variable `p`
- `studentOf -> {s -> s}` says the match’s student is the bound variable
  `s`

## Query Results

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Math CompSci English
        Wisnesky Spivak Chlipala Morrisett : String
}

schema University = literal : Ty {
    entities
        Professor
        Student
        Department
    foreign_keys
        worksIn    : Professor -> Department
        majoringIn : Student   -> Department
    attributes
        profName : Professor  -> String
        studName : Student    -> String
        deptName : Department -> String
}

schema AdvisorMatches = literal : Ty {
    entities
        Professor
        Student
        Department
        Match
    foreign_keys
        worksIn     : Professor -> Department
        majoringIn  : Student   -> Department
        professorOf : Match -> Professor
        studentOf   : Match -> Student
    attributes
        profName : Professor  -> String
        studName : Student    -> String
        deptName : Department -> String
    path_equations
        studentOf.majoringIn = professorOf.worksIn
}

query findMatches = literal : University -> AdvisorMatches {
    entity Department -> {
        from
            d : Department
        attributes
            deptName -> d.deptName
    }
    entity Professor -> {
        from
            p : Professor
        attributes
            profName -> p.profName
        foreign_keys
            worksIn -> {d -> p.worksIn}
    }
    entity Student -> {
        from
            s : Student
        attributes
            studName -> s.studName
        foreign_keys
            majoringIn -> {d -> s.majoringIn}
    }
    entity Match -> {
        from
            p : Professor
            s : Student
        where
            p.worksIn = s.majoringIn
        foreign_keys
            professorOf -> {p -> p}
            studentOf   -> {s -> s}
    }
}

instance UniversityOfX = literal : University {
    generators
        prof_w prof_s prof_c prof_m : Professor
        stud_a stud_b stud_c stud_d : Student
        math compsci english : Department
    multi_equations
        profName   -> {prof_w Wisnesky, prof_s Spivak, prof_c Chlipala, prof_m Morrisett}
        studName   -> {stud_a Wisnesky, stud_b Spivak, stud_c Chlipala, stud_d Morrisett}
        deptName   -> {math Math, compsci CompSci, english English}
        worksIn    -> {prof_w math, prof_s math, prof_c compsci, prof_m compsci}
        majoringIn -> {stud_a math, stud_b compsci, stud_c compsci, stud_d english}
}

instance Matches = eval findMatches UniversityOfX
"""

alg = env.Matches.algebra

println("=== Advisor Matches ===")
println("Professor    | Student      | Department")
println("-------------+--------------+-----------")
for x in carrier(alg, :Match)
    p = eval_fk(alg, :professorOf, x)
    s = eval_fk(alg, :studentOf, x)
    pn = eval_att(alg, :profName, p)
    sn = eval_att(alg, :studName, s)
    d = eval_fk(alg, :worksIn, p)
    dn = eval_att(alg, :deptName, d)
    println(rpad(string(pn), 13), "| ", rpad(string(sn), 13), "| ", dn)
end

println("\nTotal matches: ", length(carrier(alg, :Match)))
```

    === Advisor Matches ===
    Professor    | Student      | Department
    -------------+--------------+-----------
    Spivak       | Wisnesky     | Math
    Wisnesky     | Wisnesky     | Math
    Chlipala     | Chlipala     | CompSci
    Morrisett    | Spivak       | CompSci
    Morrisett    | Chlipala     | CompSci
    Chlipala     | Spivak       | CompSci

    Total matches: 6

The query found 6 matches:

- **Math** (2 professors x 1 student = 2 matches): Wisnesky-Wisnesky,
  Spivak-Wisnesky
- **CompSci** (2 professors x 2 students = 4 matches): Chlipala-Spivak,
  Chlipala-Chlipala, Morrisett-Spivak, Morrisett-Chlipala
- **English** (0 professors x 1 student = 0 matches): Student Morrisett
  has no potential advisors

### Verifying the Path Equation

The path equation `studentOf.majoringIn = professorOf.worksIn` holds for
every match:

``` julia
println("Verifying path equation: studentOf.majoringIn = professorOf.worksIn\n")

all_ok = true
for x in carrier(alg, :Match)
    p = eval_fk(alg, :professorOf, x)
    s = eval_fk(alg, :studentOf, x)
    prof_dept = eval_fk(alg, :worksIn, p)
    stud_dept = eval_fk(alg, :majoringIn, s)
    ok = prof_dept == stud_dept
    all_ok &= ok

    pn = eval_att(alg, :profName, p)
    sn = eval_att(alg, :studName, s)
    dn = eval_att(alg, :deptName, prof_dept)
    println("  ", pn, " <-> ", sn, ": prof dept = ", dn,
            ", stud dept = ", eval_att(alg, :deptName, stud_dept),
            ok ? " ✓" : " ✗")
end

println("\nAll matches satisfy path equation: ", all_ok)
```

    Verifying path equation: studentOf.majoringIn = professorOf.worksIn

      Spivak <-> Wisnesky: prof dept = Math, stud dept = Math ✓
      Wisnesky <-> Wisnesky: prof dept = Math, stud dept = Math ✓
      Chlipala <-> Chlipala: prof dept = CompSci, stud dept = CompSci ✓
      Morrisett <-> Spivak: prof dept = CompSci, stud dept = CompSci ✓
      Morrisett <-> Chlipala: prof dept = CompSci, stud dept = CompSci ✓
      Chlipala <-> Spivak: prof dept = CompSci, stud dept = CompSci ✓

    All matches satisfy path equation: true

## CQL vs SQL

The equivalent SQL query requires an explicit join:

``` sql
SELECT p.profName, s.studName, d.deptName
FROM Professor p
JOIN Student s ON p.worksIn = s.majoringIn
JOIN Department d ON p.worksIn = d.id
```

But the SQL approach has no way to express the path equation constraint
at the schema level. In SQL, you could insert a match where the
professor and student are in different departments — the constraint
exists only in application logic. In CQL, the path equation
`studentOf.majoringIn = professorOf.worksIn` is part of the schema
itself, and any instance must satisfy it.

| Aspect | SQL | CQL |
|----|----|----|
| **Join computation** | Explicit `JOIN` clause | Multi-variable `from` + `where` |
| **Integrity constraint** | Application-level logic | Path equation in schema |
| **FK mapping** | Manual column references | Typed `foreign_keys` block |
| **Result structure** | Flat rows | Structured entities with navigable FKs |

## The Query as a Functor

From a categorical perspective, the query `findMatches` is a **functor**
from the category of `University` instances to the category of
`AdvisorMatches` instances. Each entity block defines how to compute the
target entity’s elements from the source, and the foreign key mappings
define how the target’s relationships are computed.

The `Match` entity block is particularly interesting: it takes the
**product** of professors and students (all pairs), then filters by the
where-clause. This is exactly a **fiber product** (pullback) over the
department — professors and students that map to the same department.

    Match = Professor ×_Department Student

This categorical interpretation guarantees that the result automatically
satisfies the path equation, because the where-clause
`p.worksIn = s.majoringIn` directly enforces it.

## Summary

| Concept | Description |
|----|----|
| **Multi-variable from** | `from p : Professor, s : Student` binds multiple source variables |
| **Where-clause join** | `p.worksIn = s.majoringIn` filters pairs by shared FK target |
| **FK mapping** | `professorOf -> {p -> p}` maps target FKs to source terms |
| **Path equations** | `studentOf.majoringIn = professorOf.worksIn` constrains the target schema |
| **Fiber product** | The Match entity computes a categorical pullback over Department |

CQL’s query language makes joins a natural consequence of multi-variable
binding and where-clause filtering. Combined with path equations in the
target schema, this ensures that the result is not just structurally
correct but also satisfies relational integrity constraints that SQL
cannot express at the schema level.
