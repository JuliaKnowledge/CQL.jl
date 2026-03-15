# CQL.jl

**Categorical Query Language for Julia** — a data integration language grounded in category theory.

CQL.jl provides a complete implementation of the [Categorical Query Language](https://www.categoricaldata.net/), enabling data integration with formal guarantees. The language uses functorial data migration to transform, merge, and query data across heterogeneous schemas.

## Features

- **Typesides**: Foundation types, constants, functions, and equations
- **Schemas**: Entities, foreign keys, attributes, and path equations
- **Instances**: Concrete data conforming to a schema, with generators and equations
- **Mappings**: Structure-preserving schema-to-schema morphisms
- **Transforms**: Instance-to-instance morphisms
- **Queries (uber-flowers)**: Generalized relational queries with categorical guarantees
- **Data migration**: Delta (pullback), Sigma (pushforward), and CoEval (right adjoint)
- **Schema colimits**: Merging multiple schemas via categorical colimit
- **CSV import/export**: Read and write instances as CSV files
- **Catlab integration**: Convert CQL schemas and instances to Catlab's acset framework

## Installation

```julia
using Pkg
Pkg.add(url="https://github.com/ecorecipes/CQL.jl")
```

## Quick Start

```@example quickstart
using CQL

env = cql"""
typeside Ty = literal {
    types
        String
        Int
    constants
        Alice Bob : String
        "100" "250" : Int
}

schema S = literal : Ty {
    entities
        Employee
        Department
    foreign_keys
        worksIn : Employee -> Department
    attributes
        name : Employee -> String
        budget : Department -> Int
}

instance I = literal : S {
    generators
        e1 e2 : Employee
        d1 : Department
    equations
        e1.worksIn = d1
        e2.worksIn = d1
        e1.name = Alice
        e2.name = Bob
        d1.budget = "250"
}
"""

env.I
```
