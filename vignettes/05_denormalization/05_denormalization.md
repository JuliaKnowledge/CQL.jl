# Denormalization in CQL
Simon Frost

## Introduction

In relational databases, **normalization** eliminates redundancy: each
fact is stored in exactly one place. But for performance or convenience,
we sometimes **denormalize** — adding redundant columns that repeat
information derivable from the normalized form.

The danger of denormalization is **data inconsistency**: if the
redundant copy gets out of sync with the source of truth, the database
contradicts itself. In CQL, **observation equations** ensure that
redundant attributes are always consistent with the data they derive
from.

This vignette demonstrates:

1.  A **normalized** schema with properly separated entities
2.  A **denormalized** extension with a redundant attribute
3.  **Observation equations** that enforce consistency between the
    redundant and source data
4.  Programmatic verification that the denormalized data is consistent

This example is adapted from the [CQL denormalization
tutorial](https://categoricaldata.net/denorm.html).

``` julia
using CQL
```

## The Normalized Schema

Consider a database tracking males and females, where each male has a
mother (a female). The normalized schema stores each person’s name in
their own entity:

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Albert George Charles Elaine Francine : String
}

schema NormalizedSchema = literal : Ty {
    entities
        Male
        Female
    foreign_keys
        mother : Male -> Female
    attributes
        female_name : Female -> String
        male_name   : Male   -> String
}
"""

sch = env.NormalizedSchema
println("Entities: ", sch.ens)
println("Foreign keys: ", collect(keys(sch.fks)))
println("Attributes: ", collect(keys(sch.atts)))
```

    Entities: Set([:Male, :Female])
    Foreign keys: [:mother]
    Attributes: [:female_name, :male_name]

In this normalized form, to find a male’s mother’s name, you must
**follow the foreign key** `mother` and then read `female_name`. The
mother’s name is stored in exactly one place (the `Female` entity).

## Normalized Data

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Albert George Charles Elaine Francine : String
}

schema NormalizedSchema = literal : Ty {
    entities
        Male
        Female
    foreign_keys
        mother : Male -> Female
    attributes
        female_name : Female -> String
        male_name   : Male   -> String
}

instance NormalizedData = literal : NormalizedSchema {
    generators
        Al Bob Charlie : Male
        Ellie Fran : Female
    equations
        male_name(Al) = Albert  mother(Al) = Ellie
        male_name(Bob) = George  mother(Bob) = Ellie
        male_name(Charlie) = Charles  mother(Charlie) = Fran
        female_name(Ellie) = Elaine
        female_name(Fran) = Francine
}
"""

alg = env.NormalizedData.algebra

println("=== Male Table ===")
println("Name       | Mother")
println("-----------+----------")
for x in carrier(alg, :Male)
    nm = eval_att(alg, :male_name, x)
    mom = eval_fk(alg, :mother, x)
    mom_nm = eval_att(alg, :female_name, mom)
    println(rpad(string(nm), 11), "| ", mom_nm)
end

println("\n=== Female Table ===")
println("Name")
println("-----------")
for x in carrier(alg, :Female)
    println(eval_att(alg, :female_name, x))
end
```

    === Male Table ===
    Name       | Mother
    -----------+----------
    Albert     | Elaine
    Charles    | Francine
    George     | Elaine

    === Female Table ===
    Name
    -----------
    Elaine
    Francine

Notice that to display each male’s mother’s name, we had to follow the
foreign key (`eval_fk`) and then read the attribute (`eval_att`). This
is the normalized way — no redundancy, but requires a join.

## The Denormalized Schema

Now suppose we want a **denormalized** schema that adds a `mother_name`
attribute directly to `Male`, so we can read the mother’s name without
following a foreign key. The denormalized schema **imports** the
normalized one and adds the redundant attribute:

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Albert George Charles Elaine Francine : String
}

schema NormalizedSchema = literal : Ty {
    entities
        Male
        Female
    foreign_keys
        mother : Male -> Female
    attributes
        female_name : Female -> String
        male_name   : Male   -> String
}

schema DeNormalizedSchema = literal : Ty {
    imports
        NormalizedSchema
    attributes
        mother_name : Male -> String
    observation_equations
        forall m:Male. mother_name(m) = female_name(mother(m))
}
"""

sch_denorm = env.DeNormalizedSchema
println("Entities: ", sch_denorm.ens)
println("Attributes: ", collect(keys(sch_denorm.atts)))
println("Observation equations: ", length(sch_denorm.obs_eqs))
```

    Entities: Set([:Male, :Female])
    Attributes: [:mother_name, :female_name, :male_name]
    Observation equations: 1

### What Is the Observation Equation?

The observation equation:

    forall m:Male. mother_name(m) = female_name(mother(m))

states that for every male `m`, the redundant attribute `mother_name(m)`
must equal `female_name(mother(m))` — the name obtained by following the
`mother` foreign key and reading `female_name`. This is a **type-level
constraint** (it constrains attribute values, not entity-level paths).

Unlike path equations (which constrain foreign key compositions),
observation equations constrain the relationship between **attributes**
and **foreign key paths**. They are the mathematical formalization of
the rule “the denormalized copy must match the normalized source.”

## Denormalized Data

We populate the denormalized schema, providing the `mother_name` values
that must be consistent with the observation equation:

``` julia
env = cql"""
typeside Ty = literal {
    types
        String
    constants
        Albert George Charles Elaine Francine : String
}

schema NormalizedSchema = literal : Ty {
    entities
        Male
        Female
    foreign_keys
        mother : Male -> Female
    attributes
        female_name : Female -> String
        male_name   : Male   -> String
}

schema DeNormalizedSchema = literal : Ty {
    imports
        NormalizedSchema
    attributes
        mother_name : Male -> String
    observation_equations
        forall m:Male. mother_name(m) = female_name(mother(m))
}

instance DeNormalizedData = literal : DeNormalizedSchema {
    generators
        Al Bob Charlie : Male
        Ellie Fran : Female
    multi_equations
        male_name   -> {Al Albert, Bob George, Charlie Charles}
        mother      -> {Al Ellie, Bob Ellie, Charlie Fran}
        female_name -> {Ellie Elaine, Fran Francine}
        mother_name -> {Al Elaine, Bob Elaine, Charlie Francine}
    options
        interpret_as_algebra = true
}
"""

alg_d = env.DeNormalizedData.algebra

println("=== Denormalized Male Table ===")
println("Name       | Mother (FK) | mother_name (redundant)")
println("-----------+-------------+------------------------")
for x in carrier(alg_d, :Male)
    nm = eval_att(alg_d, :male_name, x)
    mom = eval_fk(alg_d, :mother, x)
    mom_nm_fk = eval_att(alg_d, :female_name, mom)
    mom_nm_attr = eval_att(alg_d, :mother_name, x)
    println(rpad(string(nm), 11), "| ", rpad(string(mom_nm_fk), 12), "| ", mom_nm_attr)
end
```

    === Denormalized Male Table ===
    Name       | Mother (FK) | mother_name (redundant)
    -----------+-------------+------------------------
    Albert     | Elaine      | Elaine
    George     | Elaine      | Elaine
    Charles    | Francine    | Francine

The `mother_name` column is now directly available on each male row,
without needing to follow the foreign key. Both the `Mother (FK)` column
(computed via join) and the `mother_name` column show the same values.

## Verifying the Observation Equation

Let’s programmatically verify that the observation equation holds for
every male:

``` julia
println("Verifying: mother_name(m) = female_name(mother(m))\n")

all_ok = true
for x in carrier(alg_d, :Male)
    nm = eval_att(alg_d, :male_name, x)
    mother_name_val = eval_att(alg_d, :mother_name, x)
    mom = eval_fk(alg_d, :mother, x)
    derived_val = eval_att(alg_d, :female_name, mom)
    ok = string(mother_name_val) == string(derived_val)
    global all_ok = all_ok && ok
    println("  ", nm, ": mother_name=", mother_name_val,
            ", female_name(mother)=", derived_val,
            " -> ", ok ? "CONSISTENT" : "INCONSISTENT")
end
println("\nAll consistent: ", all_ok)
```

    Verifying: mother_name(m) = female_name(mother(m))

      Albert: mother_name=Elaine, female_name(mother)=Elaine -> CONSISTENT
      George: mother_name=Elaine, female_name(mother)=Elaine -> CONSISTENT
      Charles: mother_name=Francine, female_name(mother)=Francine -> CONSISTENT

    All consistent: true

## What Happens with Inconsistent Data?

If we tried to populate `mother_name` with values that don’t match the
observation equation, the data would be **inconsistent** with the
schema’s constraints. For example, if Albert’s `mother_name` were
`"Francine"` but his mother is Ellie (whose name is `"Elaine"`), this
would violate the observation equation.

Let’s demonstrate detecting such inconsistency:

``` julia
# Create intentionally inconsistent data
env2 = cql"""
typeside Ty = literal {
    types
        String
    constants
        Albert George Charles Elaine Francine Wrong : String
}

schema NormalizedSchema = literal : Ty {
    entities
        Male
        Female
    foreign_keys
        mother : Male -> Female
    attributes
        female_name : Female -> String
        male_name   : Male   -> String
}

schema DeNormalizedSchema = literal : Ty {
    imports
        NormalizedSchema
    attributes
        mother_name : Male -> String
    observation_equations
        forall m:Male. mother_name(m) = female_name(mother(m))
}

instance BadData = literal : DeNormalizedSchema {
    generators
        Al Bob : Male
        Ellie : Female
    multi_equations
        male_name   -> {Al Albert, Bob George}
        mother      -> {Al Ellie, Bob Ellie}
        female_name -> {Ellie Elaine}
        mother_name -> {Al Wrong, Bob Elaine}
    options
        interpret_as_algebra = true
}
"""

bad_alg = env2.BadData.algebra

println("=== Checking observation equation on potentially bad data ===\n")
for x in carrier(bad_alg, :Male)
    nm = eval_att(bad_alg, :male_name, x)
    mn = eval_att(bad_alg, :mother_name, x)
    mom = eval_fk(bad_alg, :mother, x)
    derived = eval_att(bad_alg, :female_name, mom)
    ok = string(mn) == string(derived)
    status = ok ? "OK" : "VIOLATION: $(mn) != $(derived)"
    println("  ", nm, ": ", status)
end
```

    === Checking observation equation on potentially bad data ===

      Albert: VIOLATION: Wrong != Elaine
      George: OK

The inconsistency is detected: Albert’s `mother_name` says `"Wrong"` but
`female_name(mother(Albert))` is `"Elaine"`. In a full CQL system with
theorem proving, such data would either be rejected or the inconsistency
would be resolved by identifying `"Wrong"` with `"Elaine"`.

## Normalized vs. Denormalized: A Comparison

``` julia
sch_n = env.NormalizedSchema
sch_d = env.DeNormalizedSchema

println("Normalized Schema:")
println("  Entities: ", sch_n.ens)
println("  Attributes: ", collect(keys(sch_n.atts)))
println("  Observation equations: ", length(sch_n.obs_eqs))
println("  To get mother's name: follow FK, then read attribute (join required)")

println("\nDenormalized Schema:")
println("  Entities: ", sch_d.ens)
println("  Attributes: ", collect(keys(sch_d.atts)))
println("  Observation equations: ", length(sch_d.obs_eqs))
println("  To get mother's name: read mother_name directly (no join)")
```

    Normalized Schema:
      Entities: Set([:Male, :Female])
      Attributes: [:female_name, :male_name]
      Observation equations: 0
      To get mother's name: follow FK, then read attribute (join required)

    Denormalized Schema:
      Entities: Set([:Male, :Female])
      Attributes: [:mother_name, :female_name, :male_name]
      Observation equations: 1
      To get mother's name: read mother_name directly (no join)

## Julia DSL

The examples above use the `cql"""..."""` string macro. CQL.jl also
provides Julia-native macros. Here is how the NormalizedSchema and
instance look using the DSL:

``` julia
using CQL

Ty = @typeside begin
    String::Ty
    Albert::String; George::String; Charles::String
    Elaine::String; Francine::String
end

NormalizedSchema = @schema Ty begin
    @entities Male, Female
    mother : Male → Female
    female_name : Female ⇒ String
    male_name : Male ⇒ String
end

NormalizedData = @instance NormalizedSchema begin
    Al::Male; Bob::Male; Charlie::Male
    Ellie::Female; Fran::Female
    male_name(Al) == Albert; male_name(Bob) == George; male_name(Charlie) == Charles
    mother(Al) == Ellie; mother(Bob) == Ellie; mother(Charlie) == Fran
    female_name(Ellie) == Elaine; female_name(Fran) == Francine
end

alg = NormalizedData.algebra
for x in carrier(alg, :Male)
    nm = eval_att(alg, :male_name, x)
    mom = eval_fk(alg, :mother, x)
    mom_nm = eval_att(alg, :female_name, mom)
    println("  $nm: mother = $mom_nm")
end
```

      Albert: mother = Elaine
      Charles: mother = Francine
      George: mother = Elaine

Note: The denormalized schema with `observation_equations` and `imports`
still requires the `cql"""..."""` syntax, as the DSL does not yet
support observation equations or schema imports.

## Summary

| Concept | Description |
|----|----|
| **Normalization** | Each fact stored once; no redundancy; requires joins |
| **Denormalization** | Redundant copies for convenience; risk of inconsistency |
| **Observation equation** | `forall x:E. att1(x) = att2(fk(x))` — enforces that redundant data matches source |
| **Schema imports** | A denormalized schema can extend a normalized one, inheriting all structure |

CQL’s observation equations provide a **mathematical guarantee** that
denormalized data stays consistent. Rather than relying on application
logic or database triggers to keep redundant copies in sync, the
constraint is part of the schema definition itself. The CQL system can
either:

- **Verify** that data satisfies the equation (detecting
  inconsistencies)
- **Compute** the redundant values automatically from the source data
  (via theorem proving)

This makes denormalization **safe** — the convenience of redundant
columns without the risk of silent data corruption.
