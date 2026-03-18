# CQL.jl

[![Dev Documentation](https://img.shields.io/badge/docs-dev-blue.svg)](https://JuliaKnowledge.github.io/CQL.jl/dev/)

A Julia implementation of the **Categorical Query Language** (CQL) — a data integration language grounded in category theory that provides mathematically guaranteed correct data migrations between schemas via functorial operations, built on [Catlab.jl](https://github.com/AlgebraicJulia/Catlab.jl).

## Features

- **Typesides**: Foundation types, constants, user-defined functions, and equational theories (including Knuth-Bendix completion)
- **Schemas**: Entity-relationship models with foreign keys, attributes, path equations, and observation equations
- **Instances**: Concrete data conforming to a schema, constructed via chase-like saturation of generators and equations
- **Mappings**: Structure-preserving schema morphisms with identity and composition
- **Delta and Sigma**: Functorial data migration — pullback (restriction) and pushforward (extension) with adjunction guarantees
- **Queries (uber-flowers)**: Generalized relational queries with categorical correctness, supporting composition via `[Q₁ ; Q₂]`
- **Schema colimits**: Merging multiple schemas by identifying entities, with inclusion mappings and universal property
- **Chase**: Constraint enforcement via equality and tuple generating dependencies (EGDs/TGDs)
- **CoEval**: Right adjoint to query evaluation for backward data migration
- **Import/export**: CSV, JDBC, ODBC, RDF, and XML data sources

## Quick Start

```julia
using CQL

env = cql"""
typeside Ty = literal {
    types String Integer
    constants Al Bob : String  CS Math : String
}

schema S = literal : Ty {
    entities Employee Department
    foreign_keys mgr : Employee -> Employee
                 dept : Employee -> Department
                 sec : Department -> Employee
    path_equations
        Employee.mgr.mgr = Employee.mgr
        Department.sec.dept = Department
    attributes ename : Employee -> String
               dname : Department -> String
}

instance I = literal : S {
    generators e1 e2 e3 : Employee  d1 d2 : Department
    equations
        mgr(e1) = e2  mgr(e2) = e2  mgr(e3) = e2
        dept(e1) = d1  dept(e2) = d1  dept(e3) = d2
        sec(d1) = e2  sec(d2) = e3
        ename(e1) = Al  ename(e2) = Bob  ename(e3) = Al
        dname(d1) = CS  dname(d2) = Math
}

query Q = literal : S -> S {
    entity Employee -> {
        from e:Employee d:Department
        where dept(e) = d
        attributes ename -> ename(e)
        foreign_keys mgr -> {e -> mgr(e)  d -> dept(mgr(e))}
                     dept -> {d -> d}
    }
    entity Department -> {
        from d:Department
        attributes dname -> dname(d)
        foreign_keys sec -> {e -> sec(d)  d -> d}
    }
}

instance J = eval Q I
"""

# Access results
env.I   # => CQLInstance
env.J   # => CQLInstance (query result)
```

## Vignettes

| # | Vignette | Description |
|---|----------|-------------|
| 1 | [CQL.jl Tutorial](vignettes/01_tutorial/01_tutorial.md) | Core concepts: typesides, schemas, instances, mappings, queries |
| 2 | [Foreign Key Queries](vignettes/02_foreign_key/02_foreign_key.md) | Multi-entity queries with path equations |
| 3 | [Path Equations](vignettes/03_path_equations/03_path_equations.md) | Enforcing data integrity constraints with category theory |
| 4 | [Joinless Queries](vignettes/04_joinless/04_joinless.md) | Following foreign keys without SQL joins |
| 5 | [Denormalization](vignettes/05_denormalization/05_denormalization.md) | Schema extension with redundant attributes and observation equations |
| 6 | [Quotients and Merging](vignettes/06_quotient/06_quotient.md) | Computing equivalence classes with Sigma data migration |
| 7 | [Unit Conversion](vignettes/07_unitconv/07_unitconv.md) | Type-safe data transformation with user-defined functions |
| 8 | [CQL vs SQL: Difficult Queries](vignettes/08_difficult_queries/08_difficult_queries.md) | When SQL struggles and CQL shines |
| 9 | [CSV Import/Export](vignettes/09_csv/09_csv.md) | Working with CSV data in CQL |
| 10 | [Database Connectivity](vignettes/10_dbc/10_dbc.md) | Importing and exporting CQL instances via DuckDB |
| 11 | [RDF Integration](vignettes/11_rdf/11_rdf.md) | Exporting, importing, and querying RDF data |
| 12 | [Categorical Data Integration](vignettes/12_data_integration/12_data_integration.md) | Normalizing, enriching, and migrating data with functorial pipelines |
| 13 | [Semantic Interoperability](vignettes/13_semantic_interop/13_semantic_interop.md) | Integrating IFC, BRICK, and REC with schema colimits and the chase |
| 14 | [Algebraic Property Graphs](vignettes/14_apg/14_apg.md) | Typed property graphs with categorical semantics |
| 15 | [Knowledge Graphs](vignettes/15_knowledge_graphs/15_knowledge_graphs.md) | Bridging RDF and property graphs with functorial data migration |
| 16 | [Ecological Data Integration](vignettes/16_ecology/16_ecology.md) | Modeling a marine food web with CQL |
| 17 | [Epidemiological Data Integration](vignettes/17_epidemiology/17_epidemiology.md) | Schema migration, query composition, and data fusion for outbreak surveillance |
| 18 | [Causal Databases](vignettes/18_causal_databases/18_causal_databases.md) | Category theory for causal knowledge representation and reasoning |
| 19 | [From Causal SQL to Semantic Spacetime](vignettes/19_causal_spacetime/19_causal_spacetime.md) | Schema morphisms between CSQL and SemanticSpacetime via CQL |

## Formal Verification

The [`proofs/`](proofs/) directory contains 10 Lean 4 files formalising the core category-theoretic claims of CQL.jl, verified against [Mathlib](https://leanprover-community.github.io/mathlib4_docs/). All 55 results are fully machine-checked with no `sorry` statements.

| File | Content |
|------|---------|
| `SchemaCategory` | Schemas and mappings form a category |
| `TransformCategory` | Instances and transforms form a category |
| `DeltaSigmaAdjunction` | Σ_F ⊣ Δ_F: unit/counit, triangle identities, naturality, round-trips, full faithfulness |
| `QueryFunctor` | Queries form a category; evaluation is functorial |
| `SchemaColimit` | Schema colimits satisfy the universal property |
| `Chase` | The chase computes a least fixpoint (Knaster-Tarski) |
| `EquationalReasoning` | Congruence closure is a sound closure operator |
| `CoEval` | The eval-coeval adjunction for queries |
| `InitialAlgebra` | Instance construction yields initial algebras (no junk, no confusion) |
| `InstanceCoproduct` | Instance coproducts with universal property |

A narrative walkthrough is available as [CqlProofs.md](proofs/CqlProofs.md) ([HTML](proofs/CqlProofs.html), [PDF](proofs/CqlProofs.pdf)).

## Installation

This package is not yet registered in the Julia General registry. Install directly from GitHub:

```julia
using Pkg
Pkg.add(url="https://github.com/JuliaKnowledge/CQL.jl")
```

## Related

- [CQL (Java)](https://github.com/CategoricalData/CQL) — the reference CQL implementation and IDE
- [cql-haskell](https://github.com/CategoricalData/CQL) — Haskell CQL implementation
- [Catlab.jl](https://github.com/AlgebraicJulia/Catlab.jl) — applied category theory in Julia
- [categoricaldata.net](https://categoricaldata.net/) — CQL documentation and resources

## References

- D. I. Spivak, *Functorial data migration*, Inform. Comput. 217 (2012), pp. 31–51, [arXiv:1009.1166](https://arxiv.org/abs/1009.1166).
- P. Wisnesky, R. Breiner, D. I. Spivak, *Algebraic databases*, Theory Appl. Categ. 32 (2017), [arXiv:1602.03501](https://arxiv.org/abs/1602.03501).
- K. Brown, D. I. Spivak, R. Wisnesky, *Categorical data integration for computational science*, Comput. Materials Sci. 164 (2019), [arXiv:1903.10579](https://arxiv.org/abs/1903.10579).

## License

This project is licensed under the [GNU Affero General Public License v3.0](LICENSE), consistent with the [reference Java CQL implementation](https://github.com/CategoricalData/CQL). For commercial licensing options, please see https://github.com/CategoricalData/CQL.
