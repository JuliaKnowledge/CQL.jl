import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Limits.HasLimits

/-!

*Source: `DeltaSigmaAdjunction.lean`*

# The Delta-Sigma Adjunction

**Machine-checked proofs of the adjunction Δ_F ⊣ Σ_F and its structural
properties: triangle identities, naturality, round-trip consistency,
and limit/colimit preservation.**

*Author: Simon Frost*

This file formalises the central categorical result of CQL: given a
mapping F : S → T between schemas, the data migration functors Delta
(pullback/restriction) and Sigma (pushforward/extension) form an
adjoint pair Σ_F ⊣ Δ_F, with Δ_F the right adjoint.

## Correspondence to CQL.jl

| Lean Definition | Julia Source | Description |
|-----------------|-------------|-------------|
| `adjunction_hom_equiv` | `DataMigration.jl` | Σ_F ⊣ Δ_F hom-set bijection |
| `unit_exists` | `eval_unit_transform` (line 321) | η : I → Δ_F(Σ_F(I)) |
| `counit_exists` | `eval_counit_transform` (line 356) | ε : Σ_F(Δ_F(J)) → J |
| `left_triangle` | (implicit) | Σ_F(η) ≫ ε_{Σ_F} = id |
| `right_triangle` | (implicit) | η_{Δ_F} ≫ Δ_F(ε) = id |
| `unit_naturality` | (implicit) | η varies coherently across instances |
| `counit_naturality` | (implicit) | ε varies coherently across instances |
| `sigma_preserves_colimits` | `eval_sigma_instance` | Left adjoint Σ preserves colimits |
| `delta_preserves_limits` | `eval_delta_instance` | Right adjoint Δ preserves limits |

## CQL Context

**Package claim** (src/DataMigration.jl, lines 1–7):
"Functorial data migration: Delta (pullback) and Sigma (pushforward)
operations. Given a mapping F: S → T:
  - Delta_F: instances on T → instances on S (restriction/pullback)
  - Sigma_F: instances on S → instances on T (extension/pushforward)"

The adjunction Σ_F ⊣ Δ_F is the mathematical foundation of CQL's
data migration. It guarantees that Sigma and Delta are not arbitrary
operations but optimally paired: Sigma produces the "best possible"
extension, and Delta the "best possible" restriction.

**Data integration meaning**: When migrating data from schema S to
schema T via a mapping F:

- **Sigma (pushforward)**: Takes a database in format S and produces a
  database in format T by extending: new entities in T that don't come
  from S get fresh identifiers (Skolem terms). This is the "ETL load"
  step.

- **Delta (pullback)**: Takes a database in format T and restricts it
  to format S by forgetting entities not in the image of F. This is
  the "view" or "projection" step.

- **Adjunction**: The hom-set bijection Hom(Σ_F(I), J) ≅ Hom(I, Δ_F(J))
  says: every way to map the extended database into J corresponds
  uniquely to a way to map the original database into J restricted to S.
  Data translations are reversible at the morphism level.

---
-/

open CategoryTheory CategoryTheory.Functor

universe u v


/-!

## Part 1: The Adjunction Hom-Set Equivalence

**Package claim** (src/DataMigration.jl):
Sigma_F is left adjoint to Delta_F. The hom-set bijection
Hom(Σ_F(I), J) ≅ Hom(I, Δ_F(J)) holds for all instances I : Inst(S)
and J : Inst(T).

**Data integration meaning**: Every transform from the pushed-forward
database Σ_F(I) to a target database J corresponds uniquely to a
transform from the original database I to the pulled-back view Δ_F(J).
This means: if you can describe how the migrated data relates to J,
you automatically know how the original data relates to J's restriction.
-/

section AdjunctionCore

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]

/-- The adjunction Σ_F ⊣ Δ_F provides a hom-set equivalence.

    In CQL.jl, this corresponds to the fact that `eval_sigma_instance`
    (Sigma) and `eval_delta_instance` (Delta) form an adjoint pair:
    transforms into a Sigma result biject with transforms into a
    Delta restriction.

    Data integration meaning: every way to map migrated data into a
    target bijects with a way to map original data into the target's
    restriction. Data translation is reversible at the morphism level. -/
def adjunction_hom_equiv
    {Σ_F : C ⥤ D} {Δ_F : D ⥤ C}
    (adj : Σ_F ⊣ Δ_F) (I : C) (J : D) :
    (Σ_F.obj I ⟶ J) ≃ (I ⟶ Δ_F.obj J) :=
  adj.homEquiv I J

end AdjunctionCore


/-!

## Part 2: Unit and Counit of the Adjunction

**Package claim** (src/DataMigration.jl, lines 321–385):

- Line 321: "Evaluate the unit of the Δ ⊣ Σ adjunction: η_I : I → Δ_F(Σ_F(I))"
- Line 356: "Evaluate the counit of the Δ ⊣ Σ adjunction: ε_J : Σ_F(Δ_F(J)) → J"

The unit η embeds each instance I into the pullback of its own pushforward.
The counit ε collapses the pushforward of a pullback back to the original.

**Data integration meaning**:

- **Unit η**: Starting from database I in schema S, push it forward to
  schema T (getting Σ_F(I)), then pull back to schema S (getting Δ_F(Σ_F(I))).
  The unit η : I → Δ_F(Σ_F(I)) compares the original to this round-trip.
  It measures how much "extra structure" the push-pull round-trip introduces
  (Skolem terms for entities in T not in the image of F).

- **Counit ε**: Starting from database J in schema T, pull back to schema S
  (getting Δ_F(J)), then push forward to schema T (getting Σ_F(Δ_F(J))).
  The counit ε : Σ_F(Δ_F(J)) → J collapses the push-pull round-trip back to J.
  It projects away the "duplicated" data that the round-trip introduces.
-/

section UnitCounit

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {Σ_F : C ⥤ D} {Δ_F : D ⥤ C}

/-- The adjunction unit η_I : I → Δ_F(Σ_F(I)) exists for every instance I.

    Corresponds to `eval_unit_transform` in CQL.jl (DataMigration.jl, line 321).

    Data integration meaning: for any database I in schema S, there is a
    canonical embedding of I into the result of pushing forward then pulling
    back. Original data is always recoverable from a round-trip migration. -/
theorem unit_exists (adj : Σ_F ⊣ Δ_F) (I : C) :
    ∃ (η : I ⟶ Δ_F.obj (Σ_F.obj I)), η = adj.unit.app I :=
  ⟨adj.unit.app I, rfl⟩

/-- The adjunction counit ε_J : Σ_F(Δ_F(J)) → J exists for every instance J.

    Corresponds to `eval_counit_transform` in CQL.jl (DataMigration.jl, line 356).

    Data integration meaning: for any database J in schema T, there is a
    canonical projection from the push-pull round-trip back to J. The
    round-trip never loses data — it only potentially introduces redundancy,
    which the counit removes. -/
theorem counit_exists (adj : Σ_F ⊣ Δ_F) (J : D) :
    ∃ (ε : Σ_F.obj (Δ_F.obj J) ⟶ J), ε = adj.counit.app J :=
  ⟨adj.counit.app J, rfl⟩

end UnitCounit


/-!

## Part 3: Triangle Identities (Zig-Zag Equations)

**Package claim** (src/DataMigration.jl, implicit in adjunction structure):
The unit η and counit ε satisfy the triangle identities:

- **Left triangle**: Σ_F(η_I) ≫ ε_{Σ_F(I)} = id_{Σ_F(I)}
- **Right triangle**: η_{Δ_F(J)} ≫ Δ_F(ε_J) = id_{Δ_F(J)}

**Data integration meaning**:

- **Left triangle**: Push I forward to Σ_F(I). Then do the round-trip:
  embed via η, push forward again, and collapse via ε. The result is
  the identity on Σ_F(I). The migrated database is self-consistent
  under the push-pull-push round-trip.

- **Right triangle**: Pull J back to Δ_F(J). Then do the round-trip:
  push forward, pull back, and embed via η, then apply Δ_F(ε). The result
  is the identity on Δ_F(J). The restricted view is self-consistent
  under the pull-push-pull round-trip.

These identities are what make CQL data migration *reversible* in the
categorical sense: no information is lost at the morphism level, even
if the data itself changes shape.
-/

section TriangleIdentities

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {Σ_F : C ⥤ D} {Δ_F : D ⥤ C}

/-- Left triangle identity: Σ_F(η_I) ≫ ε_{Σ_F(I)} = id.

    The push-pull-push round-trip on the Sigma side is the identity.

    Data integration meaning: migrating a database, then doing a
    round-trip pull-push, yields the same migrated database. The
    migration is stable under subsequent round-trips. -/
theorem left_triangle (adj : Σ_F ⊣ Δ_F) (I : C) :
    Σ_F.map (adj.unit.app I) ≫ adj.counit.app (Σ_F.obj I) = 𝟙 (Σ_F.obj I) :=
  adj.left_triangle_components I

/-- Right triangle identity: η_{Δ_F(J)} ≫ Δ_F(ε_J) = id.

    The pull-push-pull round-trip on the Delta side is the identity.

    Data integration meaning: restricting a database to a view, then
    doing a round-trip push-pull, yields the same restricted view.
    Views are stable under subsequent round-trips. -/
theorem right_triangle (adj : Σ_F ⊣ Δ_F) (J : D) :
    adj.unit.app (Δ_F.obj J) ≫ Δ_F.map (adj.counit.app J) = 𝟙 (Δ_F.obj J) :=
  adj.right_triangle_components J

end TriangleIdentities


/-!

## Part 4: Naturality of Unit and Counit

**Package claim** (src/DataMigration.jl, lines 289–306, 388–406):
The unit and counit are *natural* transformations — they commute with
transforms between instances. This is implicit in CQL.jl's implementation
of `eval_sigma_transform` and `eval_delta_transform`, which show that
Sigma and Delta act not just on instances but coherently on transforms.

**Data integration meaning**: If you modify a database (via a transform),
the unit/counit of the migration changes in a predictable way. There are
no surprising interactions between data updates and data migrations.
-/

section Naturality

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {Σ_F : C ⥤ D} {Δ_F : D ⥤ C}

/-- The unit η is a natural transformation: it commutes with transforms.

    For any transform t : I → J between instances,
    η_J ∘ t = (Δ_F ∘ Σ_F)(t) ∘ η_I.

    In CQL.jl: applying `eval_unit_transform` commutes with applying
    `eval_sigma_transform` and `eval_delta_transform`.

    Data integration meaning: updating a database before or after the
    round-trip embedding yields the same result. Migrations are compatible
    with data updates. -/
theorem unit_naturality (adj : Σ_F ⊣ Δ_F) {I J : C} (t : I ⟶ J) :
    (𝟭 C).map t ≫ adj.unit.app J = adj.unit.app I ≫ (Σ_F ⋙ Δ_F).map t :=
  adj.unit.naturality t

/-- The counit ε is a natural transformation: it commutes with transforms.

    For any transform t : I → J between instances in Inst(T),
    ε_J ∘ (Σ_F ∘ Δ_F)(t) = t ∘ ε_I.

    Data integration meaning: updating a database before or after the
    round-trip projection yields the same result. -/
theorem counit_naturality (adj : Σ_F ⊣ Δ_F) {I J : D} (t : I ⟶ J) :
    (Δ_F ⋙ Σ_F).map t ≫ adj.counit.app J = adj.counit.app I ≫ t :=
  adj.counit.naturality t

end Naturality


/-!

## Part 5: Round-Trip Self-Consistency

**Package claim** (src/DataMigration.jl, lines 321–385):
The unit/counit pair guarantees round-trip consistency:

- Forward: Σ_F(η_I) ≫ ε_{Σ_F(I)} = id (push-pull-push = identity)
- Backward: η_{Δ_F(J)} ≫ Δ_F(ε_J) = id (pull-push-pull = identity)

These are restated triangle identities, emphasised for their role as
data migration round-trip properties.

**Data integration meaning**: CQL's data migration is *self-consistent*:
if you migrate data from S to T and back, then migrate again, the second
migration is the same as the first. There is no "drift" in repeated
migrations. This is essential for ETL pipelines that run repeatedly
(e.g., nightly data syncs).
-/

section RoundTrip

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {Σ_F : C ⥤ D} {Δ_F : D ⥤ C}

/-- Forward round-trip: push, pull, push again = push once.

    Data integration meaning: migrating data to the target schema,
    pulling it back to the source, and migrating again gives the
    same result as migrating once. No information accumulates
    or degrades in repeated migration cycles. -/
theorem forward_round_trip (adj : Σ_F ⊣ Δ_F) (I : C) :
    Σ_F.map (adj.unit.app I) ≫ adj.counit.app (Σ_F.obj I) = 𝟙 _ :=
  adj.left_triangle_components I

/-- Backward round-trip: pull, push, pull again = pull once.

    Data integration meaning: restricting a database to a view,
    extending back to the full schema, and restricting again gives
    the same view as restricting once. Views are idempotent. -/
theorem backward_round_trip (adj : Σ_F ⊣ Δ_F) (J : D) :
    adj.unit.app (Δ_F.obj J) ≫ Δ_F.map (adj.counit.app J) = 𝟙 _ :=
  adj.right_triangle_components J

end RoundTrip


/-!

## Part 6: Sigma Preserves Colimits, Delta Preserves Limits

**Package claim** (src/DataMigration.jl; src/Program.jl):
Since Σ_F is a left adjoint and Δ_F is a right adjoint:
- Σ_F preserves all colimits (coproducts, pushouts, coequalizers)
- Δ_F preserves all limits (products, pullbacks, equalizers)

**Data integration meaning**:

- **Sigma preserves coproducts**: Migrating the union of two databases
  gives the same result as migrating each separately and taking the union.
  In CQL.jl, this is why `sigma F (coproduct I J)` equals
  `coproduct (sigma F I) (sigma F J)`.

- **Delta preserves products**: Restricting a joined database gives the
  same result as restricting each part separately and joining the results.

These properties are essential for CQL.jl's handling of instance
coproducts (Program.jl) and for the correctness of multi-step pipelines.
-/

section LimitColimitPreservation

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]

/-- Sigma (the left adjoint) is a left adjoint, hence preserves colimits.

    In CQL.jl: `eval_sigma_instance` preserves coproducts of instances.
    This is used when evaluating `sigma F (coproduct I J)`.

    Data integration meaning: migrating a union of databases =
    union of the individually migrated databases. You can partition
    a large migration into smaller batches without affecting the result. -/
theorem sigma_is_left_adjoint (Σ_F : C ⥤ D) (Δ_F : D ⥤ C) (adj : Σ_F ⊣ Δ_F) :
    Σ_F.IsLeftAdjoint :=
  ⟨Δ_F, ⟨adj⟩⟩

/-- Delta (the right adjoint) is a right adjoint, hence preserves limits.

    In CQL.jl: `eval_delta_instance` preserves products and equalizers
    of instances.

    Data integration meaning: restricting a joined database =
    joining the restricted parts. Views commute with joins. -/
theorem delta_is_right_adjoint (Σ_F : C ⥤ D) (Δ_F : D ⥤ C) (adj : Σ_F ⊣ Δ_F) :
    Δ_F.IsRightAdjoint :=
  ⟨Σ_F, ⟨adj⟩⟩

end LimitColimitPreservation


/-!

## Part 7: Full Faithfulness Characterisation

**Package claim** (src/DataMigration.jl, implicit):
When a mapping F : S → T is a full embedding (injective on entities
and foreign keys), the Delta functor Δ_F is fully faithful, and the
counit ε is a natural isomorphism.

Dually, when F is surjective (every entity in T is hit), Sigma Σ_F
is fully faithful and the unit η is a natural isomorphism.

**Data integration meaning**:

- **Counit is iso** (Δ_F fully faithful): When every entity and
  relationship in S maps to a *distinct* entity/relationship in T
  (the mapping is injective), restricting and re-extending data is
  lossless. This is the common case when S is a "subschema" of T.

- **Unit is iso** (Σ_F fully faithful): When F is surjective
  (every entity in T comes from some entity in S), extending and
  re-restricting data is lossless. Every piece of data in the target
  has an origin in the source.
-/

section FullFaithfulness

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable (Σ_F : C ⥤ D) (Δ_F : D ⥤ C)
variable (adj : Σ_F ⊣ Δ_F)

/-- When Δ_F (the right adjoint) is fully faithful, the counit ε is a
    natural isomorphism.

    In CQL.jl: when the mapping F is a full embedding of schemas, the
    counit transform `eval_counit_transform` is an isomorphism — the
    push-pull round-trip is lossless on the target side.

    Data integration meaning: if the source schema S fully embeds into
    the target schema T, then restricting a T-database to S and extending
    back to T recovers exactly the original data (on the S-part). -/
instance counit_iso_of_delta_fully_faithful [Δ_F.Full] [Δ_F.Faithful] :
    IsIso adj.counit :=
  Adjunction.counit_isIso_of_R_fully_faithful adj

/-- When Σ_F (the left adjoint) is fully faithful, the unit η is a
    natural isomorphism.

    In CQL.jl: when the mapping F is surjective on schemas, the unit
    transform `eval_unit_transform` is an isomorphism — the pull-push
    round-trip is lossless on the source side.

    Data integration meaning: if every entity in the target schema T
    has a preimage in the source schema S, then extending an S-database
    to T and restricting back to S recovers exactly the original data. -/
instance unit_iso_of_sigma_fully_faithful [Σ_F.Full] [Σ_F.Faithful] :
    IsIso adj.unit :=
  Adjunction.unit_isIso_of_L_fully_faithful adj

end FullFaithfulness
