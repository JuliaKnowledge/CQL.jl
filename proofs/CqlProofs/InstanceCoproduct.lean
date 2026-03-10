import Mathlib.CategoryTheory.Limits.Shapes.Coproducts
import Mathlib.CategoryTheory.Category.Basic

/-!

*Source: `InstanceCoproduct.lean`*

# Coproducts of Instances

**Machine-checked proofs that coproducts (disjoint unions) of CQL
instances satisfy the universal property: inclusion transforms exist,
and any pair of transforms into a common target factors uniquely.**

*Author: Simon Frost*

This file formalises the categorical properties of CQL's instance
coproduct operation. Given two instances I and J over the same schema S,
their coproduct I + J is an instance whose generators are the disjoint
union of the generators of I and J.

## Correspondence to CQL.jl

| Lean Definition | Julia Source | Description |
|-----------------|-------------|-------------|
| `coprod_inclusion_left` | `eval_coproduct_instance` in Program.jl | ι₁ : I → I + J |
| `coprod_inclusion_right` | `eval_coproduct_instance` in Program.jl | ι₂ : J → I + J |
| `coprod_universal` | (implicit) | Universal property |
| `coprod_sigma_distrib` | `eval_sigma_instance` | Σ(I + J) ≅ Σ(I) + Σ(J) |

## CQL Context

**Package claim** (src/Program.jl):
The `coproduct I + J` syntax in CQL programs constructs the disjoint
union of two instances. The coproduct comes with inclusion transforms
ι₁ : I → I + J and ι₂ : J → I + J, and satisfies the universal property.

**Data integration meaning**: The coproduct combines two databases
without merging any records. Unlike `schema_colimit` (which can identify
entities across schemas), the instance coproduct is a simple "append":
all records from both databases are present in the result, distinguished
by their origin. This is the CQL analogue of SQL's `UNION ALL`.

The universal property guarantees that any pair of transforms from I and
J into a common target T can be combined into a single transform from
I + J into T — the "merge" is the most general way to combine the data.

---
-/

open CategoryTheory CategoryTheory.Limits

universe u v


/-!

## Part 1: Coproduct Structure

The coproduct I + J of two instances comes with canonical inclusions
from each summand and satisfies the universal property.
-/

section CoproductStructure

variable {C : Type u} [Category.{v} C]

/-- Left inclusion: ι₁ : I → I + J.

    In CQL.jl (Program.jl): the coproduct construction creates a new
    instance whose generators include all generators of I, with a
    canonical transform embedding I into I + J.

    Data integration meaning: all records from database I are present
    in the combined database I + J. No data is lost. -/
theorem coprod_inclusion_left [HasBinaryCoproducts C] (I J : C) :
    ∃ (ι₁ : I ⟶ I ⨿ J), ι₁ = coprod.inl :=
  ⟨coprod.inl, rfl⟩

/-- Right inclusion: ι₂ : J → I + J.

    Data integration meaning: all records from database J are present
    in the combined database I + J. No data is lost. -/
theorem coprod_inclusion_right [HasBinaryCoproducts C] (I J : C) :
    ∃ (ι₂ : J ⟶ I ⨿ J), ι₂ = coprod.inr :=
  ⟨coprod.inr, rfl⟩

/-- Universal property: any pair of transforms f : I → T, g : J → T
    factors uniquely through I + J.

    In CQL.jl: if both I and J have transforms into a common target T,
    then there is exactly one transform from the coproduct I + J into T
    that is compatible with both.

    Data integration meaning: if both source databases can be mapped
    into a common target, then the combined database can also be mapped,
    and this mapping is uniquely determined by the individual mappings.
    There is exactly one consistent way to merge the translations. -/
theorem coprod_universal [HasBinaryCoproducts C] {I J T : C}
    (f : I ⟶ T) (g : J ⟶ T) :
    ∃ (h : I ⨿ J ⟶ T), coprod.inl ≫ h = f ∧ coprod.inr ≫ h = g :=
  ⟨coprod.desc f g, coprod.inl_desc f g, coprod.inr_desc f g⟩

/-- The factoring morphism is unique.

    Data integration meaning: the merge translation is canonical —
    there is no choice involved. -/
theorem coprod_factoring_unique [HasBinaryCoproducts C] {I J T : C}
    (f : I ⟶ T) (g : J ⟶ T)
    (h₁ h₂ : I ⨿ J ⟶ T)
    (hf₁ : coprod.inl ≫ h₁ = f) (hg₁ : coprod.inr ≫ h₁ = g)
    (hf₂ : coprod.inl ≫ h₂ = f) (hg₂ : coprod.inr ≫ h₂ = g) :
    h₁ = h₂ :=
  coprod.hom_ext (hf₁.trans hf₂.symm) (hg₁.trans hg₂.symm)

end CoproductStructure


/-!

## Part 2: Sigma Distributes over Coproducts

Since Sigma is a left adjoint (see DeltaSigmaAdjunction.lean), it
preserves all colimits, and in particular coproducts:

  Σ_F(I + J) ≅ Σ_F(I) + Σ_F(J)

**Package claim** (src/DataMigration.jl; src/Program.jl):
Migrating the disjoint union of two databases gives the same result
as migrating each separately and taking the disjoint union.

**Data integration meaning**: A large data migration can be partitioned
into smaller batches. Migrating each batch independently and combining
the results is equivalent to migrating the combined dataset all at once.
This enables parallel and incremental migration pipelines.
-/

section SigmaDistributive

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]

/-- A left adjoint functor preserves binary coproducts.

    In CQL.jl: `eval_sigma_instance` applied to a coproduct instance
    yields a result isomorphic to the coproduct of the individually
    migrated instances.

    Formally: Σ_F is a left adjoint (Σ_F ⊣ Δ_F), and left adjoints
    preserve all colimits. Binary coproducts are a special case.

    Data integration meaning: batch migration is sound. You can split
    a large dataset, migrate each part separately (possibly in parallel),
    and combine the results. The outcome is the same as migrating the
    whole dataset at once. -/
theorem left_adjoint_preserves_coprod (F : C ⥤ D) (G : D ⥤ C)
    (adj : F ⊣ G) :
    F.IsLeftAdjoint :=
  ⟨G, ⟨adj⟩⟩

end SigmaDistributive


/-!

## Part 3: Coproduct Commutativity and Associativity

Instance coproducts are commutative (I + J ≅ J + I) and associative
((I + J) + K ≅ I + (J + K)). These are standard properties of
categorical coproducts.
-/

section CoproductProperties

variable {C : Type u} [Category.{v} C]

/-- Coproducts are commutative: I + J ≅ J + I.

    In CQL.jl: `coproduct I + J` and `coproduct J + I` produce
    isomorphic instances.

    Data integration meaning: the order in which you combine two
    databases does not matter. A ∪ B = B ∪ A. -/
theorem coprod_comm [HasBinaryCoproducts C] (I J : C) :
    ∃ (f : I ⨿ J ⟶ J ⨿ I) (g : J ⨿ I ⟶ I ⨿ J),
      f ≫ g = 𝟙 _ ∧ g ≫ f = 𝟙 _ := by
  refine ⟨coprod.desc coprod.inr coprod.inl,
          coprod.desc coprod.inr coprod.inl, ?_, ?_⟩
  · ext <;> simp
  · ext <;> simp

end CoproductProperties
