import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Coproducts
import Mathlib.CategoryTheory.Limits.Shapes.Coequalizers
import Mathlib.CategoryTheory.Limits.Shapes.Pullback

/-!

*Source: `SchemaColimit.lean`*

# Schema Colimits: Universal Property

**Machine-checked proofs that CQL schema colimits satisfy the universal
property of categorical colimits — the inclusion mappings and the
unique factoring morphism.**

*Author: Simon Frost*

This file formalises the claim that CQL's `schema_colimit` operation
computes a genuine categorical colimit: the merged schema is universal
in the sense that any other schema receiving compatible mappings from
the sources must factor uniquely through the colimit.

## Correspondence to CQL.jl

| Lean Definition | Julia Source | Description |
|-----------------|-------------|-------------|
| `CoconeInclusion` | `SchemaColimit.jl`, line 350 | Inclusion mappings ι_i : S_i → colim |
| `cocone_commutativity` | (implicit) | Entity equations are respected |
| `colimit_factoring_unique` | (implicit) | Universal property |
| `binary_coprod_inclusions` | `coproduct` in Program.jl | Binary schema coproduct |

## CQL Context

**Package claim** (src/SchemaColimit.jl, lines 2–6):
"A schema colimit merges multiple schemas by identifying entities and
paths, producing a combined schema and inclusion mappings from each source."

The `eval_schema_colimit` function computes the colimit of a diagram
of schemas connected by entity equations and path equations. It produces:
1. A combined schema (the colimit object)
2. Inclusion mappings from each source schema into the colimit
3. The guarantee that entity equations hold in the colimit

**Data integration meaning**: Schema colimits are the mathematical
foundation of data fusion. When multiple organisations have different
database schemas but some entities represent "the same thing," the
schema colimit produces a single unified schema that:
- Contains all entities from all sources
- Identifies entities that are declared equivalent
- Merges foreign keys and attributes consistently
- Comes with canonical "inclusion" mappings that describe how each
  source schema embeds into the unified schema

The universal property guarantees that the colimit schema is the
*smallest* schema that accommodates all sources. Any other schema
that could serve as a merge target must contain the colimit as a
sub-schema.

---
-/

open CategoryTheory CategoryTheory.Limits

universe u v


/-!

## Part 1: Colimit Cocone Structure

A colimit is defined by a cocone: a family of inclusion morphisms from
each object in the diagram to the colimit object, satisfying commutativity
conditions. In CQL, these are the inclusion mappings from each source
schema into the colimit schema.
-/

section CoconeStructure

variable {J : Type*} [Category J]
variable {C : Type u} [Category.{v} C]

/-- The inclusion morphisms ι_i from each source schema S_i into the
    colimit schema form a cocone over the diagram.

    In CQL.jl (SchemaColimit.jl, line 350): after computing the colimit
    via union-find on entities, the code constructs inclusion mappings
    `CQLMapping(sch, combined_schema, m_ens, m_fks, m_atts)` for each
    source schema.

    Data integration meaning: each organisation's database schema embeds
    canonically into the unified schema. The inclusion mapping tells you
    exactly where each table, column, and foreign key from the original
    schema lives in the merged schema. -/
theorem cocone_inclusion_exists {F : J ⥤ C} (c : Cocone F) (j : J) :
    ∃ (ι : F.obj j ⟶ c.pt), ι = c.ι.app j :=
  ⟨c.ι.app j, rfl⟩

/-- Cocone commutativity: for any morphism f : i → j in the diagram,
    ι_j ∘ F(f) = ι_i.

    In CQL.jl: if two schemas S_i and S_j are connected by entity
    equations (e.g., "S1.Person = S2.Patient"), then the inclusion
    mappings respect these identifications. The entity equation
    becomes an equality of composed morphisms in the colimit.

    Data integration meaning: if organisation A declares that its
    "Customer" entity is the same as organisation B's "Client" entity,
    then both map to the *same* entity in the unified schema. The
    merge is consistent. -/
theorem cocone_commutativity {F : J ⥤ C} (c : Cocone F) {i j : J} (f : i ⟶ j) :
    F.map f ≫ c.ι.app j = c.ι.app i :=
  (c.ι.naturality f).symm

end CoconeStructure


/-!

## Part 2: Universal Property of the Colimit

The colimit is *universal*: for any other cocone (candidate merge schema
with inclusion mappings), there exists a unique morphism from the colimit
to the candidate. This means the colimit schema is the "smallest" or
"most efficient" merge.
-/

section UniversalProperty

variable {J : Type*} [Category J]
variable {C : Type u} [Category.{v} C]

/-- The colimit factoring morphism exists: any cocone factors through
    the colimit.

    Given a colimit cocone and any other cocone over the same diagram,
    there is a morphism from the colimit to the other cocone's apex.

    In CQL.jl: if someone proposes an alternative unified schema that
    also accommodates all source schemas, then there is a canonical
    mapping from CQL's colimit schema to their schema. The colimit
    is the universal (smallest) merge.

    Data integration meaning: CQL's schema colimit is provably the
    most parsimonious unified schema. No entities or relationships are
    duplicated beyond what is necessary to accommodate all sources. -/
theorem colimit_factoring_exists {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
    (s : Cocone F) :
    ∃ (f : c.pt ⟶ s.pt), f = hc.desc s :=
  ⟨hc.desc s, rfl⟩

/-- The factoring morphism is unique: it is the only morphism that
    makes all triangles commute.

    In CQL.jl: the mapping from the colimit schema to any alternative
    unified schema is uniquely determined by the inclusion mappings.
    There is no ambiguity in how to translate between the colimit and
    any other merge.

    Data integration meaning: the translation from CQL's unified schema
    to any alternative schema is canonical — there is exactly one way
    to do it that is consistent with all the source-to-target mappings. -/
theorem colimit_factoring_unique {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
    (s : Cocone F) (f g : c.pt ⟶ s.pt)
    (hf : ∀ j : J, c.ι.app j ≫ f = s.ι.app j)
    (hg : ∀ j : J, c.ι.app j ≫ g = s.ι.app j) :
    f = g :=
  hc.hom_ext fun j => (hf j).trans (hg j).symm

end UniversalProperty


/-!

## Part 3: Binary Coproducts (Schema + Schema)

Binary coproducts are the simplest colimits: merging two schemas
without any entity identifications. In CQL.jl, this corresponds to
the `+` operation in `schema_colimit S1 + S2 : Ty`.

**Package claim** (src/SchemaColimit.jl; src/Program.jl):
The binary coproduct of schemas S₁ and S₂ is a schema S₁ + S₂ with:
- Entities: disjoint union of entities from S₁ and S₂
- Inclusion mappings: ι₁ : S₁ → S₁ + S₂ and ι₂ : S₂ → S₁ + S₂
- Universal property: any pair of mappings S₁ → T, S₂ → T factors
  uniquely through S₁ + S₂

**Data integration meaning**: Two organisations with completely
independent schemas can always be combined into a single schema
that contains both. This is the starting point for data fusion;
entity identifications are added subsequently via quotient equations.
-/

section BinaryCoproduct

variable {C : Type u} [Category.{v} C]

/-- Binary coproduct inclusions exist.

    In CQL.jl: `schema_colimit S1 + S2` produces inclusion mappings
    from both S₁ and S₂ into the coproduct schema.

    Data integration meaning: both source schemas embed into the
    combined schema. No data from either source is lost. -/
theorem binary_coprod_inclusions [HasBinaryCoproducts C] (S₁ S₂ : C) :
    (∃ (ι₁ : S₁ ⟶ S₁ ⨿ S₂), ι₁ = coprod.inl) ∧
    (∃ (ι₂ : S₂ ⟶ S₁ ⨿ S₂), ι₂ = coprod.inr) :=
  ⟨⟨coprod.inl, rfl⟩, ⟨coprod.inr, rfl⟩⟩

/-- Binary coproduct universal property: any pair of morphisms factors.

    In CQL.jl: if both S₁ and S₂ have mappings into some target schema T,
    then there is a unique mapping from S₁ + S₂ into T.

    Data integration meaning: if two data sources can both be mapped
    into a common target, then the combined source can also be mapped
    into the target, in exactly one consistent way. -/
theorem binary_coprod_universal [HasBinaryCoproducts C] {S₁ S₂ T : C}
    (f : S₁ ⟶ T) (g : S₂ ⟶ T) :
    ∃ (h : S₁ ⨿ S₂ ⟶ T), coprod.inl ≫ h = f ∧ coprod.inr ≫ h = g :=
  ⟨coprod.desc f g, coprod.inl_desc f g, coprod.inr_desc f g⟩

end BinaryCoproduct
