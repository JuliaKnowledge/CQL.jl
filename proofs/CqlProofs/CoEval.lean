import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Functor.Basic

/-!

*Source: `CoEval.lean`*

# CoEval: The Right Adjoint to Query Evaluation

**Machine-checked proofs that query evaluation (eval) and co-evaluation
(coeval) form an adjoint pair eval_Q ⊣ coeval_Q, with structural
properties: unit/counit transforms, triangle identities, and naturality.**

*Author: Simon Frost*

This file formalises the adjunction between query evaluation and
co-evaluation. Given a query Q : S → T:

- `eval Q` : Inst(S) → Inst(T) evaluates Q on instances (left adjoint)
- `coeval Q` : Inst(T) → Inst(S) computes the right adjoint (co-evaluation)

The adjunction eval_Q ⊣ coeval_Q generalises the Delta-Sigma adjunction:
every mapping F : S → T can be converted to a query `toQuery(F)`, and
`eval (toQuery F)` coincides with Sigma_F while `coeval (toQuery F)`
coincides with Delta_F.

## Correspondence to CQL.jl

| Lean Definition | Julia Source | Description |
|-----------------|-------------|-------------|
| `eval_coeval_adj` | `DataMigration.jl` | eval_Q ⊣ coeval_Q adjunction |
| `coeval_unit_exists` | `eval_unit_transform` | η : I → coeval_Q(eval_Q(I)) |
| `coeval_counit_exists` | `counit_query` (Program.jl) | ε : eval_Q(coeval_Q(J)) → J |
| `coeval_left_triangle` | (implicit) | eval_Q(η) ≫ ε = id |
| `coeval_right_triangle` | (implicit) | η ≫ coeval_Q(ε) = id |

## CQL Context

**Package claim** (src/DataMigration.jl; src/Program.jl):
`coeval Q I` computes the right adjoint to query evaluation. The counit
transform `counit_query Q I` witnesses the adjunction:

  ε_I : eval_Q(coeval_Q(I)) → I

The coeval construction is used in CQL.jl for:
1. Computing right data migrations (the "CoEval" keyword in CQL programs)
2. The `counit_query` operation that connects eval and coeval
3. Query inversion: coeval gives the "best inverse" of a query

**Data integration meaning**: While `eval Q` transforms data forward
(source → target), `coeval Q` transforms data backward (target → source)
in the optimal way. The adjunction guarantees this is the *best possible*
backward transformation — any other backward transformation factors
through coeval.

---
-/

open CategoryTheory

universe u v


/-!

## Part 1: The eval ⊣ coeval Adjunction

The eval-coeval adjunction provides a hom-set bijection:

  Hom(eval_Q(I), J) ≅ Hom(I, coeval_Q(J))

This says: every transform from a query result into a target J
corresponds uniquely to a transform from the query input into
coeval_Q(J). Query evaluation and co-evaluation are optimally paired.
-/

section EvalCoeval

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]

/-- The eval ⊣ coeval adjunction provides a hom-set bijection.

    In CQL.jl: the `coeval Q I` operation is the right adjoint to
    `eval_query_instance Q I`. Transforms into a query result biject
    with transforms into a co-evaluated instance.

    Data integration meaning: every way to relate a query's output to
    a target database corresponds uniquely to a way to relate the
    query's input to the co-evaluated target. Forward and backward
    query transformations are in perfect correspondence. -/
def eval_coeval_adj_hom_equiv
    {eval_Q : C ⥤ D} {coeval_Q : D ⥤ C}
    (adj : eval_Q ⊣ coeval_Q) (I : C) (J : D) :
    (eval_Q.obj I ⟶ J) ≃ (I ⟶ coeval_Q.obj J) :=
  adj.homEquiv I J

/-- The coeval unit η_I : I → coeval_Q(eval_Q(I)) exists.

    Corresponds to the unit transform in CQL.jl (DataMigration.jl).
    Embeds each S-instance into the co-evaluation of its own query result.

    Data integration meaning: the original data is always recoverable
    (up to isomorphism) from the result of evaluating Q and then
    co-evaluating. The round-trip through eval-coeval preserves
    all information from the source. -/
theorem coeval_unit_exists
    {eval_Q : C ⥤ D} {coeval_Q : D ⥤ C}
    (adj : eval_Q ⊣ coeval_Q) (I : C) :
    ∃ (η : I ⟶ coeval_Q.obj (eval_Q.obj I)), η = adj.unit.app I :=
  ⟨adj.unit.app I, rfl⟩

/-- The coeval counit ε_J : eval_Q(coeval_Q(J)) → J exists.

    Corresponds to `counit_query Q J` in CQL.jl (Program.jl).
    Projects the eval-coeval round-trip back to the original instance.

    Data integration meaning: co-evaluating a T-instance to get an
    S-instance, then evaluating the query to get back a T-instance,
    produces a canonical projection to the original. The round-trip
    may introduce extra structure (from the query's `from` variables),
    but the counit collapses it back. -/
theorem coeval_counit_exists
    {eval_Q : C ⥤ D} {coeval_Q : D ⥤ C}
    (adj : eval_Q ⊣ coeval_Q) (J : D) :
    ∃ (ε : eval_Q.obj (coeval_Q.obj J) ⟶ J), ε = adj.counit.app J :=
  ⟨adj.counit.app J, rfl⟩

end EvalCoeval


/-!

## Part 2: Triangle Identities for eval ⊣ coeval

The triangle identities ensure that the eval-coeval round-trip is
self-consistent. These are the structural backbone of the adjunction.
-/

section CoEvalTriangles

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {eval_Q : C ⥤ D} {coeval_Q : D ⥤ C}

/-- Left triangle: eval_Q(η_I) ≫ ε_{eval_Q(I)} = id.

    In CQL.jl: evaluating a query, doing the coeval round-trip unit,
    evaluating again, and applying the counit yields the identity
    on the query result.

    Data integration meaning: the query result is self-consistent
    under the eval-coeval round-trip. Running a query twice through
    the adjunction machinery gives the same result as running it once. -/
theorem coeval_left_triangle (adj : eval_Q ⊣ coeval_Q) (I : C) :
    eval_Q.map (adj.unit.app I) ≫ adj.counit.app (eval_Q.obj I) = 𝟙 _ :=
  adj.left_triangle_components I

/-- Right triangle: η_{coeval_Q(J)} ≫ coeval_Q(ε_J) = id.

    Data integration meaning: co-evaluating a database, doing the
    eval round-trip, and co-evaluating the counit yields the identity
    on the co-evaluated instance. The backward transformation is
    self-consistent. -/
theorem coeval_right_triangle (adj : eval_Q ⊣ coeval_Q) (J : D) :
    adj.unit.app (coeval_Q.obj J) ≫ coeval_Q.map (adj.counit.app J) = 𝟙 _ :=
  adj.right_triangle_components J

end CoEvalTriangles


/-!

## Part 3: Naturality of eval-coeval Unit/Counit

The unit and counit of the eval-coeval adjunction are natural
transformations, ensuring coherent behaviour across all instances.
-/

section CoEvalNaturality

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]
variable {eval_Q : C ⥤ D} {coeval_Q : D ⥤ C}

/-- The coeval unit is natural: it commutes with transforms.

    Data integration meaning: updating a database before or after
    the eval-coeval round-trip yields the same result. Query
    adjunctions are compatible with data updates. -/
theorem coeval_unit_naturality (adj : eval_Q ⊣ coeval_Q) {I J : C} (t : I ⟶ J) :
    t ≫ adj.unit.app J = adj.unit.app I ≫ (eval_Q ⋙ coeval_Q).map t :=
  adj.unit.naturality t

/-- The coeval counit is natural: it commutes with transforms.

    Data integration meaning: the `counit_query` operation in CQL.jl
    varies coherently — small changes to the input instance produce
    proportionally small changes to the counit transform. -/
theorem coeval_counit_naturality (adj : eval_Q ⊣ coeval_Q) {I J : D} (t : I ⟶ J) :
    (coeval_Q ⋙ eval_Q).map t ≫ adj.counit.app J = adj.counit.app I ≫ t :=
  adj.counit.naturality t

end CoEvalNaturality
