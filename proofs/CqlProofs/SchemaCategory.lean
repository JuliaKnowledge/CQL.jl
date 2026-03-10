import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.NatTrans

/-!

*Source: `SchemaCategory.lean`*

# The Category of Schemas and Mappings

**Machine-checked proofs that CQL schemas and mappings form a category.**

*Author: Simon Frost*

This file formalises the claim underlying all of CQL.jl: schemas are objects
and mappings are morphisms in a category **Sch**. Identity mappings and
mapping composition satisfy the category axioms.

## Correspondence to CQL.jl

| Lean Definition | Julia Source | Description |
|-----------------|-------------|-------------|
| `SchemaObj` | `Schema.jl` | Schemas with entities, foreign keys, attributes |
| `SchemaMor` | `Mapping.jl` | Structure-preserving maps between schemas |
| `SchemaMor.id` | `identity_mapping` | Identity mapping on a schema |
| `SchemaMor.comp` | `compose_mapping` | Composition of two mappings |
| `schema_id_comp` | (implicit) | Left identity: id ∘ f = f |
| `schema_comp_id` | (implicit) | Right identity: f ∘ id = f |
| `schema_comp_assoc` | (implicit) | Associativity: (h ∘ g) ∘ f = h ∘ (g ∘ f) |

## CQL Context

**Package claim** (src/Mapping.jl, lines 77–95):
`compose_mapping(f, g)` composes schema morphisms and `identity_mapping(sch)`
constructs the identity. These are used pervasively: Delta, Sigma, and query
evaluation all depend on mappings being well-behaved categorical morphisms.

**Data integration meaning**: Schemas describe data formats (relational
databases, CSV files, APIs). Mappings describe how to translate between
formats. The category axioms guarantee that:

- Translating data through an identity mapping changes nothing.
- Translating through a chain of mappings A → B → C → D gives the same
  result regardless of how you group the intermediate translations.
  This is essential for multi-step ETL pipelines.

---
-/

open CategoryTheory

universe u

/-!

## Part 1: Abstract Schema Category

We model the category of schemas abstractly: schemas are objects, mappings
are morphisms, and the category axioms (identity, associativity) hold.

This abstracts away the internal structure of schemas (entities, foreign
keys, attributes) and focuses on the categorical properties that CQL.jl
relies upon for composing data migration pipelines.
-/

section SchemaCategory

/-- A CQL schema — the objects of the category **Sch**.

    In CQL.jl (`Schema.jl`), a schema consists of:
    - A typeside (base types and equations)
    - A set of entities
    - Foreign keys between entities (with path equations)
    - Attributes from entities to types (with observation equations)

    Here we model schemas abstractly as objects of a category. -/
structure SchemaObj : Type (u + 1) where
  /-- Carrier type for entities in this schema -/
  entities : Type u

/-- A CQL mapping F : S → T — the morphisms of **Sch**.

    In CQL.jl (`Mapping.jl`), a mapping specifies for each entity,
    foreign key, and attribute of S where it maps to in T. The mapping
    must preserve path equations and observation equations.

    Here we model mappings abstractly as functions on entity types,
    with identity and composition operations. -/
structure SchemaMor (S T : SchemaObj.{u}) : Type u where
  /-- How entities in S map to entities in T -/
  onEntities : S.entities → T.entities

/-- Identity mapping: every entity maps to itself.

    Corresponds to `identity_mapping(sch)` in CQL.jl (Mapping.jl, line 89).
    Used as the trivial migration: data stays in the same schema.

    Data integration meaning: the "do nothing" translation — every table,
    column, and foreign key maps to itself. -/
def SchemaMor.id (S : SchemaObj.{u}) : SchemaMor S S :=
  ⟨Function.id⟩

/-- Composition of mappings: (g ∘ f) maps entities through f then g.

    Corresponds to `compose_mapping(f, g)` in CQL.jl (Mapping.jl, line 77).
    Used when chaining schema translations: A → B → C becomes A → C.

    Data integration meaning: if f translates from a hospital's format to
    a national registry format, and g translates from the national format
    to WHO format, then g ∘ f translates directly from hospital to WHO. -/
def SchemaMor.comp {S T U : SchemaObj.{u}} (f : SchemaMor S T) (g : SchemaMor T U) :
    SchemaMor S U :=
  ⟨g.onEntities ∘ f.onEntities⟩

/-- Left identity: composing the identity mapping before f gives f.

    In CQL.jl: `compose_mapping(identity_mapping(S), f) = f`.

    Data integration meaning: doing nothing before a translation is the
    same as just doing the translation. -/
theorem schema_id_comp {S T : SchemaObj.{u}} (f : SchemaMor S T) :
    SchemaMor.comp (SchemaMor.id S) f = f := by
  simp [SchemaMor.comp, SchemaMor.id, Function.id]

/-- Right identity: composing f with the identity mapping gives f.

    In CQL.jl: `compose_mapping(f, identity_mapping(T)) = f`.

    Data integration meaning: doing nothing after a translation is the
    same as just doing the translation. -/
theorem schema_comp_id {S T : SchemaObj.{u}} (f : SchemaMor S T) :
    SchemaMor.comp f (SchemaMor.id T) = f := by
  simp [SchemaMor.comp, SchemaMor.id, Function.id]

/-- Associativity: composition of three mappings is independent of grouping.

    In CQL.jl: `compose_mapping(compose_mapping(f, g), h) =
                compose_mapping(f, compose_mapping(g, h))`.

    Data integration meaning: in a four-system integration pipeline
    A → B → C → D, it does not matter whether you first translate
    A → B → C and then to D, or first translate B → C → D and then
    from A. The result is the same end-to-end translation.

    This is critical for CQL.jl's `Program.jl`, which evaluates
    mappings in dependency order — associativity guarantees the
    evaluation order does not affect correctness. -/
theorem schema_comp_assoc {S T U V : SchemaObj.{u}}
    (f : SchemaMor S T) (g : SchemaMor T U) (h : SchemaMor U V) :
    SchemaMor.comp (SchemaMor.comp f g) h = SchemaMor.comp f (SchemaMor.comp g h) := by
  simp [SchemaMor.comp, Function.comp_assoc]

end SchemaCategory


/-!

## Part 2: Schemas as a Mathlib Category

We show that schemas and mappings form a `Category` in the sense of
Mathlib's `CategoryTheory.Category`. This allows us to use the full
Mathlib library of categorical constructions (adjunctions, limits,
colimits, Kan extensions) on schemas.
-/

section MathlibCategory

/-- Schemas and mappings form a category in the Mathlib sense.

    This is the foundational instance that enables all subsequent proofs:
    adjunctions (DeltaSigmaAdjunction.lean), colimits (SchemaColimit.lean),
    and functor composition (QueryFunctor.lean) all require this instance.

    In CQL.jl, this category structure is implicit — `compose_mapping`
    and `identity_mapping` are standalone functions rather than methods on
    a category type. The Lean formalisation makes the categorical structure
    explicit and machine-checked. -/
instance : Category SchemaObj.{u} where
  Hom := SchemaMor
  id S := SchemaMor.id S
  comp f g := SchemaMor.comp f g
  id_comp f := schema_id_comp f
  comp_id f := schema_comp_id f
  assoc f g h := schema_comp_assoc f g h

end MathlibCategory
