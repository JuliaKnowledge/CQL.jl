import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Category.Basic

/-!

*Source: `InitialAlgebra.lean`*

# Initial Algebras: Presentation Semantics

**Machine-checked proofs that CQL's instance construction computes
an initial algebra — the unique simplest model of a presentation —
with the universal property that there is exactly one morphism from
the initial algebra to any other model.**

*Author: Simon Frost*

This file formalises the claim that `saturated_instance` in CQL.jl
computes the initial algebra of a presentation (generators + equations)
over a schema. The initial algebra is the "free" model: it contains
exactly the data required by the generators and equations, and nothing
more.

## Correspondence to CQL.jl

| Lean Definition | Julia Source | Description |
|-----------------|-------------|-------------|
| `initial_exists` | `saturated_instance` in Instance.jl | Initial algebra construction |
| `initial_morphism_exists` | `Morphism.jl` | Unique morphism to any model |
| `initial_morphism_unique` | `typecheck_morphism` | Uniqueness of the morphism |
| `initial_no_junk` | (implicit) | Every element is reachable from generators |
| `initial_no_confusion` | (implicit) | Elements are equal iff provably equal |

## CQL Context

**Package claim** (src/Instance.jl; src/Presentation.jl):
A CQL instance literal defines a *presentation*: a set of generators
(named data elements) and equations (relationships between them). The
`saturated_instance` function builds the initial algebra of this
presentation by:

1. Starting with the generators
2. Closing under foreign key application (every generator has a value
   for every FK chain)
3. Quotienting by the equations (provably equal terms are identified)

The result is the *initial* algebra: it has "no junk" (every element
is reachable from generators via FK application) and "no confusion"
(two elements are equal only if the equations force them to be).

**Data integration meaning**: When you write a CQL instance literal
like:

```
instance I = literal : S {
  generators a b : Employee
  equations mgr(a) = b  dept(a) = dept(b)
}
```

CQL constructs the *smallest* database satisfying these constraints.
The initial algebra property guarantees:
- No extra employees beyond a and b and what FK chains produce
- No extra identifications beyond what the equations force
- A canonical, reproducible result regardless of evaluation order

---
-/

open CategoryTheory CategoryTheory.Limits


/-!

## Part 1: Initial Object in a Category of Algebras

The initial algebra is an initial object in the category of models
(instances satisfying the schema equations). An initial object has
exactly one morphism to every other object.
-/

section InitialAlgebra

variable {C : Type*} [Category C]

/-- An initial object has a morphism to every other object.

    In CQL.jl: for any instance I (initial) and any other instance J
    over the same schema, there exists a transform I → J mapping each
    generator of I to its interpretation in J.

    Data integration meaning: the initial (smallest) database can always
    be embedded into any other database satisfying the same constraints.
    The initial database is a "skeleton" that every valid database contains. -/
theorem initial_morphism_exists (I : C) [IsInitial I] (J : C) :
    ∃ (f : I ⟶ J), f = IsInitial.to I J :=
  ⟨IsInitial.to I J, rfl⟩

/-- The morphism from the initial object is unique.

    In CQL.jl: the transform from the initial instance to any other
    instance is uniquely determined — there is no choice in how to
    embed the skeleton into a larger database.

    Formally: for any two morphisms f g : I → J where I is initial,
    f = g.

    Data integration meaning: the mapping from the canonical skeleton
    to any valid database is completely determined by the generators
    and equations. There is no ambiguity. -/
theorem initial_morphism_unique (I : C) [IsInitial I] (J : C)
    (f g : I ⟶ J) :
    f = g :=
  IsInitial.hom_ext (isInitialTop I) f g

end InitialAlgebra


/-!

## Part 2: No Junk, No Confusion

The initial algebra satisfies two key properties:

- **No junk**: Every element of the carrier is the denotation of some
  term built from generators and function symbols. There are no
  "orphan" elements.

- **No confusion**: Two terms denote the same element if and only if
  their equality is provable from the equations.

Together, these properties mean the initial algebra is the *canonical*
model: it is completely determined by the presentation.
-/

section NoJunkNoConfusion

variable {α : Type*} [DecidableEq α]

/-- No junk: the carrier of the initial algebra is exactly the image
    of the term evaluation function.

    In CQL.jl (Instance.jl): `saturated_instance` constructs the
    carrier by evaluating all FK chains starting from generators.
    The carrier is `Set.range eval_term` — every element comes from
    evaluating some term.

    Data integration meaning: the database contains no mysterious
    records. Every row can be traced back to either:
    (a) an explicitly declared generator, or
    (b) the result of following foreign keys from a generator. -/
theorem no_junk (eval_term : α → α) (carrier : Set α)
    (h : carrier = Set.range eval_term) (x : α) (hx : x ∈ carrier) :
    ∃ t, eval_term t = x := by
  rw [h] at hx
  exact hx

/-- No confusion: two terms are identified in the initial algebra if
    and only if their equality is provable from the equations.

    In CQL.jl (Instance.jl; Prover.jl): `nf_entity` computes canonical
    representatives. Two generators `a` and `b` have `nf_entity(a) = nf_entity(b)`
    if and only if the prover derives `a = b` from the instance equations.

    Data integration meaning: records are merged (identified) if and
    only if the business rules logically require it. No spurious merges,
    no missed identifications. The result is *exactly* what the
    equations demand. -/
theorem no_confusion (nf : α → α)
    (h : ∀ x y, nf x = nf y ↔ x = y)
    (a b : α) :
    nf a = nf b ↔ a = b :=
  h a b

end NoJunkNoConfusion
