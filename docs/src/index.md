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
Pkg.add(url="https://github.com/JuliaKnowledge/CQL.jl")
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

### Julia DSL

The same example using Julia-native macros with Unicode operators:

```@example quickstart
Ty = @typeside begin
    String::Ty
    Int::Ty
    Alice::String; Bob::String
    "100"::Int; "250"::Int
end

S = @schema Ty begin
    @entities Employee, Department
    worksIn : Employee → Department
    name : Employee ⇒ String
    budget : Department ⇒ Int
end

I = @instance S begin
    e1::Employee; e2::Employee; d1::Department
    worksIn(e1) == d1
    worksIn(e2) == d1
    name(e1) == Alice
    name(e2) == Bob
    budget(d1) == "250"
end

I
```

Both approaches produce identical results. The DSL also provides Unicode operators for data migration:

```julia
Δ(F)(J)       # delta (pullback)
Σ(F)(I)       # sigma (pushforward)
Q(I)          # query evaluation
Q1 ∘ Q2       # composition
I1 ⊔ I2       # coproduct
```
