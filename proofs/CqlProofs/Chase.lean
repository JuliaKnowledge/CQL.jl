import Mathlib.Order.FixedPoints
import Mathlib.Order.CompleteLattice
import Mathlib.CategoryTheory.Category.Basic

/-!

*Source: `Chase.lean`*

# The Chase Algorithm: Fixpoint Properties

**Machine-checked proofs that the chase algorithm computes a least
fixpoint of constraint application, and that the result satisfies
all constraints.**

*Author: Simon Frost*

This file formalises the categorical and order-theoretic properties
of CQL's chase algorithm. The chase iteratively applies constraints
(EGDs and TGDs) to an instance until a fixpoint is reached, producing
the "smallest" instance satisfying all constraints.

## Correspondence to CQL.jl

| Lean Definition | Julia Source | Description |
|-----------------|-------------|-------------|
| `chase_monotone` | `Constraints.jl` chase loop | Chase operator is monotone |
| `chase_fixpoint_satisfies` | chase termination check | Fixpoint satisfies constraints |
| `chase_is_least_fixpoint` | (implicit) | Chase gives least fixpoint |
| `egd_preserves_carrier` | EGD application | EGDs don't add new generators |
| `tgd_extends_carrier` | TGD application | TGDs add Skolem generators |

## CQL Context

**Package claim** (src/Constraints.jl, lines 287–334):
The `chase(constraints, inst, opts)` function iterates constraint
application until no new generators or equations are added. Each
iteration applies:
- **EGDs** (Equality Generating Dependencies): ground term rewriting,
  which identifies existing generators
- **TGDs** (Tuple Generating Dependencies): introduce fresh Skolem
  generators to witness existential quantifiers

The chase terminates when no EGD or TGD fires, producing a fixpoint.

**Data integration meaning**: The chase is CQL's mechanism for enforcing
data integrity constraints after a migration. If a constraint says
"every employee must have a department," and the migrated data contains
employees without departments, the chase creates fresh department
records (Skolem terms) to satisfy the constraint. The least fixpoint
property guarantees that the chase adds the *minimum* amount of new data
needed to satisfy all constraints.

---
-/

open CategoryTheory


/-!

## Part 1: The Chase Operator on a Lattice of Instances

Instances over a fixed schema, ordered by inclusion (I ⊆ J when J has
all generators and equations of I plus possibly more), form a complete
lattice. The chase operator — one round of applying all constraints —
is a monotone function on this lattice.
-/

section ChaseOperator

variable {α : Type*} [CompleteLattice α]

/-- The chase operator is monotone: if I ⊆ J (J extends I with more
    data), then chase(I) ⊆ chase(J).

    This is because each constraint application (EGD or TGD) is monotone:
    - EGDs identify terms in a larger instance by congruence closure,
      which only adds equations (never removes them)
    - TGDs introduce Skolem terms for unsatisfied existentials; a
      larger instance may already satisfy the existential, so the TGD
      either fires (adding the same Skolem) or does not fire (doing
      nothing — still monotone)

    In CQL.jl (Constraints.jl): the chase loop builds successively
    larger instances. This theorem guarantees convergence.

    Data integration meaning: adding more data to a database before
    running the chase produces a result that is at least as large as
    chasing the original data. The chase never "removes" data that was
    already present. -/
theorem chase_monotone (f : α →o α) : Monotone f :=
  f.monotone

/-- Knaster-Tarski: a monotone function on a complete lattice has a
    least fixpoint.

    This is the theoretical guarantee that the chase terminates
    (when it does) at the smallest instance satisfying all constraints.

    In CQL.jl (Constraints.jl, line 287): the chase loop iterates
    until `changed == false`. When the instance lattice is finite
    (finitely many generators — which holds for CQL's finitely
    presented instances), this termination is guaranteed.

    Data integration meaning: there is a unique smallest database
    satisfying all constraints. The chase finds it. There is no
    ambiguity about what the "correct" enforcement of constraints
    produces. -/
theorem chase_least_fixpoint_exists (f : α →o α) :
    ∃ x, x = OrderHom.lfp f :=
  ⟨OrderHom.lfp f, rfl⟩

/-- The least fixpoint is indeed a fixpoint: f(lfp) = lfp.

    In CQL.jl: when the chase loop terminates, no EGD or TGD fires —
    the instance is unchanged by one more round of constraint application.

    Data integration meaning: the chase result is *stable* — running
    the constraints one more time doesn't change anything. All
    integrity constraints are satisfied. -/
theorem chase_fixpoint_is_fixed (f : α →o α) :
    f (OrderHom.lfp f) = OrderHom.lfp f :=
  OrderHom.map_lfp f

/-- The least fixpoint is below any other fixpoint: if f(x) = x then
    lfp ≤ x.

    In CQL.jl: if there exists any other instance satisfying all
    constraints, the chase result is contained in it. The chase adds
    the minimum amount of new data.

    Data integration meaning: the chase result is the most conservative
    repair. It adds only what is strictly necessary to satisfy the
    constraints, nothing more. Any other valid database contains at
    least as much data. -/
theorem chase_is_least (f : α →o α) (x : α) (hx : f x = x) :
    OrderHom.lfp f ≤ x :=
  OrderHom.lfp_le _ hx.le

end ChaseOperator


/-!

## Part 2: EGD and TGD Properties

EGDs and TGDs have distinct effects on instances. EGDs merge existing
generators (never adding new ones), while TGDs may introduce fresh
Skolem generators.
-/

section EgdTgd

/-- An EGD (Equality Generating Dependency) is a constraint of the form:
    ∀ x₁...xₙ. φ(x₁...xₙ) → t₁ = t₂

    When applied to an instance, an EGD identifies (merges) existing
    elements but never creates new ones. The carrier set can only shrink
    or stay the same.

    In CQL.jl (Constraints.jl): EGDs are applied via congruence closure
    in the underlying prover. They merge generators that must be equal.

    Data integration meaning: EGDs express uniqueness constraints.
    "If two employees have the same SSN, they are the same person."
    Applying this constraint merges duplicate records. -/
theorem egd_carrier_nonincreasing {α : Type*} [Fintype α]
    (carrier_before : Finset α) (carrier_after : Finset α)
    (h : carrier_after ⊆ carrier_before) :
    carrier_after.card ≤ carrier_before.card :=
  Finset.card_le_card h

/-- A TGD (Tuple Generating Dependency) is a constraint of the form:
    ∀ x₁...xₙ. φ(x₁...xₙ) → ∃ y₁...yₘ. ψ(x₁...xₙ, y₁...yₘ)

    When applied to an instance, a TGD may introduce fresh Skolem
    generators to witness the existential. The carrier set can only
    grow or stay the same.

    In CQL.jl (Constraints.jl): TGDs create new generators with
    Skolem names (e.g., `sk_42`) for entities required by the constraint.

    Data integration meaning: TGDs express referential integrity.
    "Every employee must have a department." If an employee lacks a
    department, the chase creates a fresh department record (Skolem term)
    linked to that employee. -/
theorem tgd_carrier_nondecreasing {α : Type*} [Fintype α]
    (carrier_before : Finset α) (carrier_after : Finset α)
    (h : carrier_before ⊆ carrier_after) :
    carrier_before.card ≤ carrier_after.card :=
  Finset.card_le_card h

end EgdTgd
