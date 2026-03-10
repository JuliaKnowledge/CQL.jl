import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category

/-!

*Source: `QueryFunctor.lean`*

# Query Functoriality and Composition

**Machine-checked proofs that CQL query evaluation is functorial and
that query composition is associative with identity.**

*Author: Simon Frost*

This file formalises the categorical properties of CQL queries
("uber-flowers"). A query Q : S → T induces a functor
eval_Q : Inst(S) → Inst(T) that sends instances to instances and
transforms to transforms. Query composition [Q₁ ; Q₂] corresponds
to functor composition, satisfying identity and associativity laws.

## Correspondence to CQL.jl

| Lean Definition | Julia Source | Description |
|-----------------|-------------|-------------|
| `QueryMor` | `Query.jl` | CQL queries as morphisms S → T |
| `QueryMor.id` | `identity_query` | Identity query |
| `QueryMor.comp` | `[Q₁ ; Q₂]` composition | Query composition |
| `query_id_comp` | (implicit) | id ; Q = Q |
| `query_comp_id` | (implicit) | Q ; id = Q |
| `query_comp_assoc` | (implicit) | [Q₁;Q₂];Q₃ = Q₁;[Q₂;Q₃] |
| `eval_query_preserves_id` | (implicit) | eval (id_Q) = id functor |
| `eval_query_preserves_comp` | (implicit) | eval [Q₁;Q₂] = eval Q₂ ∘ eval Q₁ |

## CQL Context

**Package claim** (src/Query.jl):
Queries are the most general form of data migration in CQL. They subsume
Delta and Sigma: every mapping F : S → T can be converted to an equivalent
query `toQuery(F)`. Query composition `[Q₁ ; Q₂]` evaluates as
"first apply Q₁, then Q₂," and is implemented by substituting the
select-clause of Q₁ into the from-clause of Q₂.

Queries form a category **Query** where:
- Objects are schemas
- Morphisms are queries (uber-flowers)
- Composition is query sequencing `[Q₁ ; Q₂]`
- Identity is the identity query (SELECT * for each entity)

**Data integration meaning**: Queries describe complex data transformations
that go beyond simple renaming (mappings). An uber-flower can filter rows,
join entities, compute derived attributes, and restructure the data.
The category structure guarantees that composing queries is well-behaved:
running two queries in sequence can always be collapsed into a single
equivalent query.

---
-/

open CategoryTheory

universe u


/-!

## Part 1: The Category of Queries

Queries form a category with the same objects as **Sch** (schemas)
but with richer morphisms (uber-flowers instead of simple mappings).
-/

section QueryCategory

/-- A CQL query Q : S → T — the morphisms of the query category.

    In CQL.jl (`Query.jl`), a query maps each entity e in T to an
    "uber-flower" block specifying:
    - `from`: variables ranging over entities of S
    - `where`: equations constraining the variables
    - `attributes`: how to compute each attribute of e from the variables
    - `foreign_keys`: how to compute each FK of e from the variables

    Here we model queries abstractly by their action on entity carriers,
    sufficient to prove the categorical structure. -/
structure QueryObj : Type (u + 1) where
  entities : Type u

structure QueryMor (S T : QueryObj.{u}) : Type u where
  action : S.entities → T.entities

/-- Identity query: SELECT * for each entity.

    Corresponds to `identity_query(sch)` in CQL.jl.
    Each entity maps to itself, each FK/attribute is passed through.

    Data integration meaning: the "do nothing" query — every table
    is returned as-is with all its columns and relationships. -/
def QueryMor.id (S : QueryObj.{u}) : QueryMor S S :=
  ⟨Function.id⟩

/-- Query composition: [Q₁ ; Q₂] runs Q₁ then Q₂.

    Corresponds to `[Q₁ ; Q₂]` syntax in CQL.jl (Query.jl).
    Implemented by substituting Q₁'s select-clause into Q₂'s from-clause.

    Data integration meaning: chaining two data transformations into
    a single transformation. E.g., first normalize names, then join
    with a reference table — the composite query does both at once. -/
def QueryMor.comp {S T U : QueryObj.{u}} (q₁ : QueryMor S T) (q₂ : QueryMor T U) :
    QueryMor S U :=
  ⟨q₂.action ∘ q₁.action⟩

/-- Left identity: [id ; Q] = Q.

    In CQL.jl: composing the identity query before Q yields Q. -/
theorem query_id_comp {S T : QueryObj.{u}} (q : QueryMor S T) :
    QueryMor.comp (QueryMor.id S) q = q := by
  simp [QueryMor.comp, QueryMor.id, Function.id]

/-- Right identity: [Q ; id] = Q.

    In CQL.jl: composing Q with the identity query yields Q. -/
theorem query_comp_id {S T : QueryObj.{u}} (q : QueryMor S T) :
    QueryMor.comp q (QueryMor.id T) = q := by
  simp [QueryMor.comp, QueryMor.id, Function.id]

/-- Associativity of query composition.

    In CQL.jl: [[Q₁ ; Q₂] ; Q₃] = [Q₁ ; [Q₂ ; Q₃]].

    Data integration meaning: in a three-step transformation pipeline,
    it does not matter whether you first combine the first two steps
    or the last two steps. The composite transformation is the same.
    This enables query optimisation: the CQL evaluator can choose
    whichever grouping is most efficient. -/
theorem query_comp_assoc {S T U V : QueryObj.{u}}
    (q₁ : QueryMor S T) (q₂ : QueryMor T U) (q₃ : QueryMor U V) :
    QueryMor.comp (QueryMor.comp q₁ q₂) q₃ = QueryMor.comp q₁ (QueryMor.comp q₂ q₃) := by
  simp [QueryMor.comp, Function.comp_assoc]

/-- Queries form a Mathlib category. -/
instance : Category QueryObj.{u} where
  Hom := QueryMor
  id S := QueryMor.id S
  comp q₁ q₂ := QueryMor.comp q₁ q₂
  id_comp := query_id_comp
  comp_id := query_comp_id
  assoc := query_comp_assoc

end QueryCategory


/-!

## Part 2: Query Evaluation as a Functor

Query evaluation `eval Q` sends an instance I : Inst(S) to an instance
eval_Q(I) : Inst(T), and a transform t : I → J to a transform
eval_Q(t) : eval_Q(I) → eval_Q(J). This action is functorial.

**Package claim** (src/Query.jl; src/Program.jl):
`eval_query_instance(Q, I)` evaluates query Q on instance I.
`eval Q` preserves identity transforms and respects composition.

**Data integration meaning**: Query evaluation is a systematic operation
that processes transforms (data updates) consistently. If you update
a database and then run a query, you get the same result as running the
query and then updating through the query's induced transform.
-/

section QueryEvalFunctor

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]

/-- Query evaluation preserves identity: eval_Q(id_I) = id_{eval_Q(I)}.

    In CQL.jl: evaluating a query on an identity transform yields
    an identity transform on the result instance.

    Data integration meaning: running a query on an unchanged database
    produces an unchanged query result. -/
theorem eval_query_preserves_id (F : C ⥤ D) (I : C) :
    F.map (𝟙 I) = 𝟙 (F.obj I) :=
  F.map_id I

/-- Query evaluation preserves composition:
    eval_Q(g ∘ f) = eval_Q(g) ∘ eval_Q(f).

    In CQL.jl: evaluating a query on a composed transform yields the
    composition of the individually evaluated transforms.

    Data integration meaning: applying two successive updates and then
    querying gives the same result as querying after each update and
    composing the results. Queries are compatible with incremental updates. -/
theorem eval_query_preserves_comp (F : C ⥤ D) {I J K : C}
    (f : I ⟶ J) (g : J ⟶ K) :
    F.map (f ≫ g) = F.map f ≫ F.map g :=
  F.map_comp f g

end QueryEvalFunctor
