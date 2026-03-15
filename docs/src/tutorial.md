# Tutorial

This tutorial walks through the core concepts of CQL.jl: typesides, schemas, instances, mappings, and data migration.

## Typesides

A *typeside* defines the foundation types and functions available to schemas and instances. The simplest useful typeside declares just `String`:

```@example tutorial
using CQL

env = cql"""
typeside Ty = literal {
    types
        String
}
"""

env.Ty
```

## Schemas

A *schema* defines the structure of data: entities, foreign keys between entities, and attributes from entities to types.

```@example tutorial
env = cql"""
typeside Ty = literal {
    types
        String
        Int
}

schema Dept = literal : Ty {
    entities
        Employee
        Department
    foreign_keys
        worksIn : Employee -> Department
    attributes
        ename : Employee -> String
        dname : Department -> String
        budget : Department -> Int
}
"""

env.Dept
```

## Instances

An *instance* populates a schema with concrete data: generators (rows) and equations (values).

```@example tutorial
env = cql"""
typeside Ty = literal {
    types
        String
        Int
    constants
        Alice Bob Carol : String
        "100" "250" : Int
}

schema S = literal : Ty {
    entities
        Employee
        Department
    foreign_keys
        worksIn : Employee -> Department
    attributes
        ename : Employee -> String
        dname : Department -> String
}

instance I = literal : S {
    generators
        e1 e2 e3 : Employee
        d1 d2 : Department
    equations
        e1.worksIn = d1
        e2.worksIn = d1
        e3.worksIn = d2
        e1.ename = Alice
        e2.ename = Bob
        e3.ename = Carol
        d1.dname = Alice
        d2.dname = Bob
}
"""

env.I
```

## Mappings and Delta Migration

A *mapping* is a structure-preserving morphism between schemas. Given a mapping F: S -> T, the *delta* migration pulls back an instance on T to an instance on S.

```@example tutorial
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Alice Bob : String
}

schema Source = literal : Ty {
    entities
        Person
    attributes
        name : Person -> String
}

schema Target = literal : Ty {
    entities
        Employee
        Department
    foreign_keys
        worksIn : Employee -> Department
    attributes
        ename : Employee -> String
        dname : Department -> String
}

mapping F = literal : Source -> Target {
    entity
        Person -> Employee
    attributes
        name -> ename
}

instance J = literal : Target {
    generators
        e1 e2 : Employee
        d1 : Department
    equations
        e1.worksIn = d1
        e2.worksIn = d1
        e1.ename = Alice
        e2.ename = Bob
        d1.dname = Alice
}

instance Delta_J = delta F J
"""

env.Delta_J
```

## Queries

CQL queries (uber-flowers) are a generalization of relational queries with categorical guarantees. They map instances on one schema to instances on another.

```@example tutorial
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Alice Bob : String
}

schema S = literal : Ty {
    entities
        Employee
        Department
    foreign_keys
        worksIn : Employee -> Department
    attributes
        ename : Employee -> String
        dname : Department -> String
}

instance I = literal : S {
    generators
        e1 e2 : Employee
        d1 : Department
    equations
        e1.worksIn = d1
        e2.worksIn = d1
        e1.ename = Alice
        e2.ename = Bob
        d1.dname = Alice
}

schema T = literal : Ty {
    entities
        EmployeeWithDept
    attributes
        emp_name : EmployeeWithDept -> String
        dept_name : EmployeeWithDept -> String
}

query Q = literal : S -> T {
    entity
        EmployeeWithDept -> {
            from
                e : Employee
            attributes
                emp_name -> e.ename
                dept_name -> e.worksIn.dname
        }
}

instance Result = eval Q I
"""

env.Result
```

## Sigma Migration

While delta pulls data back along a mapping, *sigma* pushes data forward. Given a mapping F: S -> T, sigma computes a pushforward that merges generators according to the mapping.

```@example tutorial
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Alice Bob : String
}

schema S = literal : Ty {
    entities
        Person
    attributes
        name : Person -> String
}

schema T = literal : Ty {
    entities
        Employee
        Department
    foreign_keys
        worksIn : Employee -> Department
    attributes
        ename : Employee -> String
        dname : Department -> String
}

mapping G = literal : S -> T {
    entity
        Person -> Employee
    attributes
        name -> ename
}

instance IS = literal : S {
    generators
        p1 p2 : Person
    equations
        p1.name = Alice
        p2.name = Bob
}

instance Sigma_IS = sigma G IS
"""

env.Sigma_IS
```
