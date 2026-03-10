# Path Equations in CQL
CQL.jl

## Introduction

Many data integration tasks involve constructing databases of tables
connected by foreign keys that must satisfy **business rules** (data
integrity constraints). In CQL, these constraints are expressed as
**path equations** — equalities between compositions of foreign keys in
a schema.

This vignette demonstrates:

1.  What path equations are and how they constrain schemas
2.  How CQL’s theorem prover **enforces** path equations automatically
3.  How path equations can cause **identification** of elements
4.  A multi-entity example from the [CQL
    documentation](https://categoricaldata.net/eqs.html)

``` julia
using CQL
```

## What Are Path Equations?

A **path** in a schema is a sequence of foreign key applications. For
example, if employees have a `manager` foreign key (pointing to another
employee), then `manager.manager` is the path “the manager’s manager.”

A **path equation** asserts that two paths starting from the same entity
always reach the same target. For instance:

- `boss.boss = boss` means “your boss’s boss is your boss” (the boss
  relation is idempotent)
- `manager.worksIn = worksIn` means “your manager works in the same
  department as you”

Path equations are declared in the `path_equations` section of a schema
definition.

## Simple Example: Idempotent Boss

Let’s start with a minimal example: a single entity `Person` with a
foreign key `boss` and a path equation stating that `boss` is
**idempotent** — taking the boss of a boss gives the same person as just
taking the boss.

### Schema Definition

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Al Bob Carl : String
}

schema BossDB = literal : Ty {
    entities
        Person
    foreign_keys
        boss : Person -> Person
    attributes
        name : Person -> String
    path_equations
        Person.boss.boss = Person.boss
}
"""

sch = env.BossDB
println("Entities: ", sch.ens)
println("Foreign keys: ", collect(keys(sch.fks)))
println("Path equations: ", length(sch.path_eqs))
```

    Entities: Set([:Person])
    Foreign keys: [:boss]
    Path equations: 1

The path equation `Person.boss.boss = Person.boss` means: for every
person `p`, `boss(boss(p)) = boss(p)`. In plain English, your boss is
always a “top-level” person — they are their own boss.

### Data That Satisfies the Constraint

Here is a valid instance: Al’s boss is Bob, Bob is his own boss, and
Carl is his own boss.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Al Bob Carl : String
}

schema BossDB = literal : Ty {
    entities
        Person
    foreign_keys
        boss : Person -> Person
    attributes
        name : Person -> String
    path_equations
        Person.boss.boss = Person.boss
}

instance I = literal : BossDB {
    generators
        a b c : Person
    equations
        name(a) = Al name(b) = Bob name(c) = Carl
        boss(a) = b boss(b) = b boss(c) = c
}
"""

alg = env.I.algebra

println("Persons: ", length(carrier(alg, :Person)))
println()
println("Name       | Boss")
println("-----------+----------")
for x in carrier(alg, :Person)
    nm = eval_att(alg, :name, x)
    b = eval_fk(alg, :boss, x)
    bnm = eval_att(alg, :name, b)
    println(rpad(string(nm), 11), "| ", bnm)
end
```

    Persons: 3

    Name       | Boss
    -----------+----------
    Carl       | Carl
    Al         | Bob
    Bob        | Bob

Let’s verify the path equation `boss.boss = boss` holds for every
person:

``` julia
println("Verifying: boss(boss(x)) = boss(x) for all x\n")
all_ok = true
for x in carrier(alg, :Person)
    nm = eval_att(alg, :name, x)
    b1 = eval_fk(alg, :boss, x)
    b2 = eval_fk(alg, :boss, b1)
    ok = b1 == b2
    global all_ok = all_ok && ok
    println("  ", nm, ": boss=", eval_att(alg, :name, b1),
            ", boss.boss=", eval_att(alg, :name, b2), " -> ", ok ? "OK" : "FAIL")
end
println("\nAll satisfied: ", all_ok)
```

    Verifying: boss(boss(x)) = boss(x) for all x

      Carl: boss=Carl, boss.boss=Carl -> OK
      Al: boss=Bob, boss.boss=Bob -> OK
      Bob: boss=Bob, boss.boss=Bob -> OK

    All satisfied: true

The theorem prover verified this instance is consistent with the path
equation and built the initial algebra.

## How Path Equations Force Identifications

The real power of path equations becomes apparent when the data
*doesn’t* naturally satisfy them. Instead of rejecting the data, CQL’s
theorem prover **identifies** (merges) elements until the equations
hold. This is called computing the **initial algebra** — the smallest
model consistent with both the data and the constraints.

### Example: Forced Merging

Consider: Al’s boss is Bob, Bob’s boss is Carl, and Carl is his own
boss. The chain `boss(boss(Al)) = boss(Carl) = Carl`, but
`boss(Al) = Bob`. So the path equation `boss.boss = boss` requires
`Carl = Bob` — the prover must **merge** Bob and Carl.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Al Bob Carl : String
}

schema BossDB = literal : Ty {
    entities
        Person
    foreign_keys
        boss : Person -> Person
    attributes
        name : Person -> String
    path_equations
        Person.boss.boss = Person.boss
}

instance J = literal : BossDB {
    generators
        a b c : Person
    equations
        name(a) = Al name(b) = Bob name(c) = Carl
        boss(a) = b boss(b) = c boss(c) = c
}
"""

alg_J = env.J.algebra
println("Persons before: 3 generators")
println("Persons after:  ", length(carrier(alg_J, :Person)), " (prover merged elements)")
println()
for x in carrier(alg_J, :Person)
    nm = eval_att(alg_J, :name, x)
    b = eval_fk(alg_J, :boss, x)
    bnm = eval_att(alg_J, :name, b)
    println("  ", repr_x(alg_J, x), ": name=", nm, ", boss=", repr_x(alg_J, b))
end
```

    Persons before: 3 generators
    Persons after:  2 (prover merged elements)

      a: name=Al, boss=a.boss
      a.boss: name=Carl, boss=a.boss

The prover reduced 3 generators to 2 elements by identifying Bob and
Carl. This is because:

- `boss(boss(a)) = boss(c) = c`, but `boss(a) = b`
- Path equation requires `boss(boss(a)) = boss(a)`, i.e., `c = b`
- So Bob and Carl are merged into a single equivalence class

Let’s verify the path equation now holds:

``` julia
println("Verifying: boss(boss(x)) = boss(x) for all x\n")
for x in carrier(alg_J, :Person)
    b1 = eval_fk(alg_J, :boss, x)
    b2 = eval_fk(alg_J, :boss, b1)
    println("  ", repr_x(alg_J, x), ": boss.boss == boss? ", b1 == b2)
end
```

    Verifying: boss(boss(x)) = boss(x) for all x

      a: boss.boss == boss? true
      a.boss: boss.boss == boss? true

## Multi-Entity Example: Employees and Departments

This example is adapted from the [CQL path equations
tutorial](https://categoricaldata.net/eqs.html). It demonstrates path
equations across multiple entities with interconnected foreign keys.

### Schema with Business Rules

The schema has two entities (`Employee` and `Department`) connected by
three foreign keys, with two path equations encoding business rules:

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Al Bob Bo Carl Math CS : String
}

schema EmpDept = literal : Ty {
    entities
        Employee
        Department
    foreign_keys
        manager   : Employee -> Employee
        worksIn   : Employee -> Department
        secretary : Department -> Employee
    attributes
        first last : Employee -> String
        name       : Department -> String
    path_equations
        Employee.manager.worksIn = Employee.worksIn
        Department.secretary.worksIn = Department
}
"""

sch = env.EmpDept
println("Entities: ", sch.ens)
println("Foreign keys: ", collect(keys(sch.fks)))
println("Path equations: ", length(sch.path_eqs))
```

    Entities: Set([:Department, :Employee])
    Foreign keys: [:worksIn, :manager, :secretary]
    Path equations: 2

The two path equations encode:

| Path Equation | Business Rule |
|----|----|
| `manager.worksIn = worksIn` | Every employee’s manager works in the same department as the employee |
| `secretary.worksIn = Department` | Every department’s secretary works in that department |

### Populating with Data

We populate the schema with three employees and two departments. Since
this example combines multiple entities with cross-entity path
equations, we use `interpret_as_algebra` mode which directly interprets
the data as an algebra.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Al Bob Bo Carl Math CS : String
}

schema EmpDept = literal : Ty {
    entities
        Employee
        Department
    foreign_keys
        manager   : Employee -> Employee
        worksIn   : Employee -> Department
        secretary : Department -> Employee
    attributes
        first last : Employee -> String
        name       : Department -> String
    path_equations
        Employee.manager.worksIn = Employee.worksIn
        Department.secretary.worksIn = Department
}

instance I = literal : EmpDept {
    generators
        a b c : Employee
        m s : Department
    multi_equations
        manager   -> {a b, b b, c c}
        worksIn   -> {a m, b m, c s}
        secretary -> {m b, s c}
        first     -> {a Al, b Bob, c Carl}
        last      -> {b Bo}
        name      -> {m Math, s CS}
    options
        interpret_as_algebra = true
}
"""

alg = env.I.algebra

println("=== Employee Table ===")
println("Name       | Last   | Manager  | Works In")
println("-----------+--------+----------+---------")
for x in carrier(alg, :Employee)
    nm = eval_att(alg, :first, x)
    lst = eval_att(alg, :last, x)
    mgr = eval_fk(alg, :manager, x)
    mgr_nm = eval_att(alg, :first, mgr)
    dept = eval_fk(alg, :worksIn, x)
    dept_nm = eval_att(alg, :name, dept)
    println(rpad(string(nm), 11), "| ", rpad(string(lst), 7), "| ",
            rpad(string(mgr_nm), 9), "| ", dept_nm)
end

println("\n=== Department Table ===")
println("Name       | Secretary")
println("-----------+----------")
for x in carrier(alg, :Department)
    nm = eval_att(alg, :name, x)
    sec = eval_fk(alg, :secretary, x)
    sec_nm = eval_att(alg, :first, sec)
    println(rpad(string(nm), 11), "| ", sec_nm)
end
```

    === Employee Table ===
    Name       | Last   | Manager  | Works In
    -----------+--------+----------+---------
    Al         | a.last | Bob      | Math
    Bob        | Bo     | Bob      | Math
    Carl       | c.last | Carl     | CS

    === Department Table ===
    Name       | Secretary
    -----------+----------
    Math       | Bob
    CS         | Carl

### Verifying the Path Equations

Let’s check that both business rules hold for every row:

``` julia
println("=== Checking Business Rules ===\n")

println("Rule 1: manager.worksIn = worksIn")
println("  (every employee's manager works in the same department)")
all_ok = true
for x in carrier(alg, :Employee)
    nm = eval_att(alg, :first, x)
    own_dept = eval_fk(alg, :worksIn, x)
    mgr = eval_fk(alg, :manager, x)
    mgr_dept = eval_fk(alg, :worksIn, mgr)
    ok = own_dept == mgr_dept
    global all_ok = all_ok && ok
    status = ok ? "OK" : "VIOLATED"
    println("  ", nm, ": ", status)
end

println("\nRule 2: secretary.worksIn = Department")
println("  (every department's secretary works in that department)")
for x in carrier(alg, :Department)
    nm = eval_att(alg, :name, x)
    sec = eval_fk(alg, :secretary, x)
    sec_dept = eval_fk(alg, :worksIn, sec)
    ok = sec_dept == x
    all_ok = all_ok && ok
    status = ok ? "OK" : "VIOLATED"
    println("  ", nm, ": ", status)
end

println("\nAll constraints satisfied: ", all_ok)
```

    === Checking Business Rules ===

    Rule 1: manager.worksIn = worksIn
      (every employee's manager works in the same department)
      Al: OK
      Bob: OK
      Carl: OK

    Rule 2: secretary.worksIn = Department
      (every department's secretary works in that department)
      Math: OK
      CS: OK

    All constraints satisfied: true

The data satisfies both path equations. Notice how the constraints
interact:

- **Al** (a): manager is Bob (b), both work in Math (m) — Rule 1
  satisfied
- **Bob** (b): manager is himself, works in Math — Rule 1 trivially
  satisfied
- **Carl** (c): manager is himself, works in CS — Rule 1 trivially
  satisfied
- **Math** (m): secretary is Bob (b), who works in Math — Rule 2
  satisfied
- **CS** (s): secretary is Carl (c), who works in CS — Rule 2 satisfied

### Missing Attributes and Skolem Terms

Notice that some attribute values were not specified (e.g., `last` for
employees a and c). CQL represents these as **Skolem terms** — symbolic
placeholders indicating that a value exists but is unknown:

``` julia
println("Attribute values (including Skolem terms):\n")
for x in carrier(alg, :Employee)
    nm = eval_att(alg, :first, x)
    lst = eval_att(alg, :last, x)
    println("  ", nm, ": last = ", lst, lst isa CQLSk ? "  (Skolem term)" : "")
end
```

    Attribute values (including Skolem terms):

      Al: last = a.last  (Skolem term)
      Bob: last = Bo
      Carl: last = c.last  (Skolem term)

Skolem terms are CQL’s way of handling **labeled nulls** — they maintain
referential integrity while acknowledging incomplete data.

## Path Equations vs. No Path Equations

To highlight the role of path equations, compare two schemas: one with
constraints and one without.

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Al Bob Math CS : String
}

schema Unconstrained = literal : Ty {
    entities
        Employee
        Department
    foreign_keys
        manager   : Employee -> Employee
        worksIn   : Employee -> Department
        secretary : Department -> Employee
    attributes
        first : Employee -> String
        name  : Department -> String
}

schema Constrained = literal : Ty {
    entities
        Employee
        Department
    foreign_keys
        manager   : Employee -> Employee
        worksIn   : Employee -> Department
        secretary : Department -> Employee
    attributes
        first : Employee -> String
        name  : Department -> String
    path_equations
        Employee.manager.worksIn = Employee.worksIn
        Department.secretary.worksIn = Department
}
"""

println("Unconstrained schema:")
println("  Path equations: ", length(env.Unconstrained.path_eqs))
println("  Any FK assignment is valid\n")

println("Constrained schema:")
println("  Path equations: ", length(env.Constrained.path_eqs))
println("  FKs must satisfy business rules")
```

    Unconstrained schema:
      Path equations: 0
      Any FK assignment is valid

    Constrained schema:
      Path equations: 2
      FKs must satisfy business rules

The unconstrained schema accepts *any* combination of manager, worksIn,
and secretary assignments. The constrained schema only accepts data
where managers share their employee’s department and secretaries work in
their department. This is the difference between a raw relational schema
and one with enforced business logic.

## Summary

| Concept | Description |
|----|----|
| **Path** | A sequence of foreign key applications (e.g., `manager.worksIn`) |
| **Path equation** | An equality between two paths from the same entity |
| **Enforcement** | CQL’s theorem prover computes the initial algebra, merging elements as needed |
| **Skolem terms** | Labeled nulls for unspecified attribute values |
| **Business rules** | Real-world constraints expressed as path equations |

Path equations are the key mechanism by which CQL schemas encode and
enforce data integrity constraints. Unlike SQL triggers or
application-level checks, path equations are **mathematical** — they are
part of the schema definition and are guaranteed to hold in every valid
instance. The theorem prover either verifies consistency or
automatically computes the necessary identifications to make the
equations hold.

For a more advanced use of path equations in queries, see the [Difficult
Queries](difficult_queries.html) vignette, which shows how CQL can
extract sub-databases satisfying path equation constraints — a task that
is notoriously difficult in SQL.
