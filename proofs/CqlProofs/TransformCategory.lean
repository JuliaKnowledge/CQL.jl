import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

/-!

*Source: `TransformCategory.lean`*

# The Category of Instances and Transforms

**Machine-checked proofs that CQL instances over a fixed schema form a
category, with transforms as morphisms.**

*Author: Simon Frost*

This file formalises the claim that for any schema S, the collection of
S-instances and transforms between them forms a category **Inst(S)**.
Identity transforms and transform composition satisfy the category axioms.

## Correspondence to CQL.jl

| Lean Definition | Julia Source | Description |
|-----------------|-------------|-------------|
| `InstObj` | `Instance.jl` | Instances conforming to a schema |
| `InstMor` | `Transform.jl` | Structure-preserving maps between instances |
| `InstMor.id` | `identity_transform` | Identity transform |
| `InstMor.comp` | `compose_transform` | Transform composition |
| `inst_id_comp` | (implicit) | Left identity: id ∘ t = t |
| `inst_comp_id` | (implicit) | Right identity: t ∘ id = t |
| `inst_comp_assoc` | (implicit) | Associativity |

## CQL Context

**Package claim** (src/Transform.jl, lines 59–72):
`compose_transform(f, g)` composes instance morphisms and
`identity_transform(inst)` constructs the identity. Transforms are the
morphisms that Delta and Sigma functors act on (DataMigration.jl), making
the category structure essential for functoriality.

**Data integration meaning**: Instances are concrete datasets conforming to
a schema. Transforms are data-level mappings: they describe how to send
each record in one dataset to a record in another, preserving all
relationships (foreign keys, attribute values). The category structure
guarantees that chaining such record-level mappings is well-behaved.

---
-/

open CategoryTheory

universe u

/-!

## Part 1: Instance Category over a Fixed Schema

Given a schema S, the category **Inst(S)** has:
- Objects: instances (databases) conforming to S
- Morphisms: transforms (record-level mappings preserving structure)
-/

section InstanceCategory

/-- A CQL instance over a fixed schema — the objects of **Inst(S)**.

    In CQL.jl (`Instance.jl`), an instance consists of:
    - An algebra: carrier sets for each entity, interpretations for FKs and attributes
    - A presentation: generators, Skolem constants, equations
    - A schema reference

    Here we model instances abstractly by their carrier. -/
structure InstObj : Type (u + 1) where
  /-- Carrier type of generators in this instance -/
  carrier : Type u

/-- A CQL transform t : I → J — the morphisms of **Inst(S)**.

    In CQL.jl (`Transform.jl`), a transform maps generators of I to
    entity-side terms of J, and Skolems of I to type-side terms of J,
    preserving all equations.

    Here we model transforms abstractly as functions on carriers. -/
structure InstMor (I J : InstObj.{u}) : Type u where
  /-- How generators of I map to elements of J -/
  onGenerators : I.carrier → J.carrier

/-- Identity transform: every generator maps to itself.

    Corresponds to `identity_transform(inst)` in CQL.jl (Transform.jl, line 67).
    Used in adjunction unit/counit constructions and as the trivial migration.

    Data integration meaning: each record stays exactly where it is. -/
def InstMor.id (I : InstObj.{u}) : InstMor I I :=
  ⟨Function.id⟩

/-- Composition of transforms: (g ∘ f) maps generators through f then g.

    Corresponds to `compose_transform(f, g)` in CQL.jl (Transform.jl, line 59).
    Used when chaining instance-level migrations.

    Data integration meaning: if f sends hospital records to a national
    registry, and g sends national records to a research database,
    then g ∘ f sends hospital records directly to the research database. -/
def InstMor.comp {I J K : InstObj.{u}} (f : InstMor I J) (g : InstMor J K) :
    InstMor I K :=
  ⟨g.onGenerators ∘ f.onGenerators⟩

/-- Left identity: id ∘ t = t. -/
theorem inst_id_comp {I J : InstObj.{u}} (f : InstMor I J) :
    InstMor.comp (InstMor.id I) f = f := by
  simp [InstMor.comp, InstMor.id, Function.id]

/-- Right identity: t ∘ id = t. -/
theorem inst_comp_id {I J : InstObj.{u}} (f : InstMor I J) :
    InstMor.comp f (InstMor.id J) = f := by
  simp [InstMor.comp, InstMor.id, Function.id]

/-- Associativity of transform composition.

    Critical for CQL.jl's evaluation of transform chains, e.g.,
    `sigma F (sigma G t)` vs `sigma (compose_mapping G F) t`. -/
theorem inst_comp_assoc {I J K L : InstObj.{u}}
    (f : InstMor I J) (g : InstMor J K) (h : InstMor K L) :
    InstMor.comp (InstMor.comp f g) h = InstMor.comp f (InstMor.comp g h) := by
  simp [InstMor.comp, Function.comp_assoc]

end InstanceCategory


/-!

## Part 2: Instances as a Mathlib Category

This instance enables us to apply Mathlib's categorical machinery
(adjunctions, limits) to the category of instances, which is needed
for the Delta-Sigma adjunction proofs in `DeltaSigmaAdjunction.lean`.
-/

section MathlibCategory

instance : Category InstObj.{u} where
  Hom := InstMor
  id I := InstMor.id I
  comp f g := InstMor.comp f g
  id_comp f := inst_id_comp f
  comp_id f := inst_comp_id f
  assoc f g h := inst_comp_assoc f g h

end MathlibCategory
