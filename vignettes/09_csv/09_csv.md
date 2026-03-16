# CQL.jl CSV Import/Export
Simon Frost

## Introduction

Real-world data often lives in CSV files. CQL.jl provides functions to
import CSV files into CQL instances and export CQL instances back to
CSV, enabling a bridge between tabular data and CQL’s categorical data
integration framework.

This tutorial demonstrates how to:

1.  **Import** CSV files into CQL instances
2.  **Inspect** imported data using CQL’s algebra API
3.  **Export** CQL instances to CSV files
4.  **Round-trip** data through import and export
5.  **Integrate** CSV data with CQL operations (queries, data migration)

This vignette is based on the [official CQL CSV
tutorial](https://categoricaldata.net/csv.html), adapted for the Julia
environment.

``` julia
using CQL
```

## CSV Format

CQL uses a simple directory-based CSV format. Each entity in a schema
corresponds to a CSV file named `EntityName.csv`. The CSV files have:

- An **`id`** column containing a unique identifier for each row
- Columns for each **foreign key**, containing the `id` of the target
  row
- Columns for each **attribute**, containing the attribute value

For example, a schema with entities `Animal` and `Habitat` would expect:

    data/
      Animal.csv     # id, livesIn (FK to Habitat), species, legs
      Habitat.csv    # id, name, climate

## Defining a Schema

First, we define a schema describing the structure of our data. We use
the `sql` typeside which provides standard SQL types like `String`.

``` julia
env = cql"""
typeside Ty = sql

schema AnimalDB = literal : Ty {
    entities
        Animal Habitat
    foreign_keys
        livesIn : Animal -> Habitat
    attributes
        species : Animal -> String
        legs : Animal -> String
        name : Habitat -> String
        climate : Habitat -> String
}
"""

sch = env.AnimalDB
println("Entities: ", sch.ens)
println("Foreign keys: ", collect(keys(sch.fks)))
println("Attributes: ", collect(keys(sch.atts)))
```

    Entities: Set([:Animal, :Habitat])
    Foreign keys: [:livesIn]
    Attributes: [:species, :legs, :climate, :name]

The schema has two entities: `Animal` and `Habitat`. Each animal lives
in a habitat (via the `livesIn` foreign key) and has a `species` and
number of `legs`. Each habitat has a `name` and `climate`.

## Creating Sample CSV Data

Let’s create CSV files representing a small animal database. In
practice, these files would come from an existing data source.

``` julia
data_dir = joinpath(mktempdir(), "AnimalDB")
mkdir(data_dir)

# Habitat data
open(joinpath(data_dir, "Habitat.csv"), "w") do io
    println(io, "\"id\",\"name\",\"climate\"")
    println(io, "\"0\",\"Forest\",\"Temperate\"")
    println(io, "\"1\",\"Ocean\",\"Tropical\"")
    println(io, "\"2\",\"Desert\",\"Arid\"")
end

# Animal data (livesIn references Habitat IDs)
open(joinpath(data_dir, "Animal.csv"), "w") do io
    println(io, "\"id\",\"livesIn\",\"species\",\"legs\"")
    println(io, "\"0\",\"0\",\"Deer\",\"4\"")
    println(io, "\"1\",\"0\",\"Owl\",\"2\"")
    println(io, "\"2\",\"1\",\"Dolphin\",\"0\"")
    println(io, "\"3\",\"2\",\"Camel\",\"4\"")
    println(io, "\"4\",\"1\",\"Shark\",\"0\"")
end

# Show the files
println("=== Habitat.csv ===")
println(read(joinpath(data_dir, "Habitat.csv"), String))
println("=== Animal.csv ===")
println(read(joinpath(data_dir, "Animal.csv"), String))
```

    === Habitat.csv ===
    "id","name","climate"
    "0","Forest","Temperate"
    "1","Ocean","Tropical"
    "2","Desert","Arid"

    === Animal.csv ===
    "id","livesIn","species","legs"
    "0","0","Deer","4"
    "1","0","Owl","2"
    "2","1","Dolphin","0"
    "3","2","Camel","4"
    "4","1","Shark","0"

Note how the `livesIn` column in `Animal.csv` contains IDs that
reference rows in `Habitat.csv`. For example, animal `0` (Deer) has
`livesIn=0`, meaning it lives in habitat `0` (Forest).

## Importing CSV Data

The `import_csv_instance` function reads CSV files from a directory and
constructs a CQL instance on the given schema.

``` julia
inst = import_csv_instance(data_dir, sch)
println(inst)
```

    instance {
      presentation {
      generators
        Animal_0 : Animal
        Animal_3 : Animal
        Habitat_2 : Habitat
        Habitat_1 : Habitat
        Animal_1 : Animal
        Habitat_0 : Habitat
        Animal_2 : Animal
        Animal_4 : Animal
      equations
        Animal_0.legs = 4
        Habitat_0.climate = Temperate
        Animal_3.livesIn = Habitat_2
        Animal_4.legs = 0
        Animal_4.livesIn = Habitat_1
        Animal_1.species = Owl
        Animal_4.species = Shark
        Animal_0.species = Deer
        Animal_2.species = Dolphin
        Animal_2.legs = 0
        Animal_1.legs = 2
        Habitat_0.name = Forest
        Animal_3.species = Camel
        Animal_3.legs = 4
        Habitat_2.climate = Arid
        Habitat_1.climate = Tropical
        Habitat_1.name = Ocean
        Habitat_2.name = Desert
        Animal_0.livesIn = Habitat_0
        Animal_1.livesIn = Habitat_0
        Animal_2.livesIn = Habitat_1
    }

      algebra {
        Animal (5 rows)
          Animal_0: livesIn=Habitat_0, species=Deer, legs=4
          Animal_3: livesIn=Habitat_2, species=Camel, legs=4
          Animal_1: livesIn=Habitat_0, species=Owl, legs=2
          Animal_2: livesIn=Habitat_1, species=Dolphin, legs=0
          Animal_4: livesIn=Habitat_1, species=Shark, legs=0
        Habitat (3 rows)
          Habitat_2: climate=Arid, name=Desert
          Habitat_1: climate=Tropical, name=Ocean
          Habitat_0: climate=Temperate, name=Forest
      }
    }

The import creates a **saturated instance** where each CSV row becomes a
generator, foreign key references become FK equations, and attribute
values become attribute equations. This is equivalent to using
`interpret_as_algebra = true` in CQL.

## Exploring Imported Data

We can inspect the imported data using CQL’s algebra API:

``` julia
alg = inst.algebra

println("Animals: ", length(carrier(alg, :Animal)), " rows")
println("Habitats: ", length(carrier(alg, :Habitat)), " rows")

println("\n--- Animal Table ---")
for x in carrier(alg, :Animal)
    sp = eval_att(alg, :species, x)
    lg = eval_att(alg, :legs, x)
    hab = eval_fk(alg, :livesIn, x)
    hab_name = eval_att(alg, :name, hab)
    hab_climate = eval_att(alg, :climate, hab)
    println("  $(repr_x(alg, x)): species=$sp, legs=$lg, habitat=$hab_name ($hab_climate)")
end

println("\n--- Habitat Table ---")
for x in carrier(alg, :Habitat)
    nm = eval_att(alg, :name, x)
    cl = eval_att(alg, :climate, x)
    println("  $(repr_x(alg, x)): name=$nm, climate=$cl")
end
```

    Animals: 5 rows
    Habitats: 3 rows

    --- Animal Table ---
      Animal_0: species=Deer, legs=4, habitat=Forest (Temperate)
      Animal_3: species=Camel, legs=4, habitat=Desert (Arid)
      Animal_1: species=Owl, legs=2, habitat=Forest (Temperate)
      Animal_2: species=Dolphin, legs=0, habitat=Ocean (Tropical)
      Animal_4: species=Shark, legs=0, habitat=Ocean (Tropical)

    --- Habitat Table ---
      Habitat_2: name=Desert, climate=Arid
      Habitat_1: name=Ocean, climate=Tropical
      Habitat_0: name=Forest, climate=Temperate

The algebra gives us programmatic access to the relational data. We can
follow foreign keys (`eval_fk`) and read attributes (`eval_att`) just as
we would query a database.

## Exporting to CSV

The `export_csv_instance` function writes a CQL instance back to CSV
files:

``` julia
export_dir = joinpath(mktempdir(), "Exported")
export_csv_instance(inst, export_dir)

println("Exported files: ", readdir(export_dir))

println("\n=== Exported Animal.csv ===")
println(read(joinpath(export_dir, "Animal.csv"), String))
println("=== Exported Habitat.csv ===")
println(read(joinpath(export_dir, "Habitat.csv"), String))
```

    Exported files: ["Animal.csv", "Habitat.csv"]

    === Exported Animal.csv ===
    "id","livesIn","legs","species"
    "0","5","4","Deer"
    "1","5","2","Owl"
    "2","6","0","Dolphin"
    "3","7","4","Camel"
    "4","6","0","Shark"

    === Exported Habitat.csv ===
    "id","climate","name"
    "5","Temperate","Forest"
    "6","Tropical","Ocean"
    "7","Arid","Desert"

The export assigns globally unique integer IDs to all carrier elements,
ensuring that foreign key references are unambiguous across entities.
The column order is deterministic (sorted alphabetically for FKs and
attributes).

## Round-trip Verification

We can verify that importing the exported data recovers the same
instance:

``` julia
inst2 = import_csv_instance(export_dir, sch)
alg2 = inst2.algebra

println("Original: ", length(carrier(alg, :Animal)), " animals, ",
        length(carrier(alg, :Habitat)), " habitats")
println("Re-imported: ", length(carrier(alg2, :Animal)), " animals, ",
        length(carrier(alg2, :Habitat)), " habitats")

# Verify attribute values match
original_species = sort([string(eval_att(alg, :species, x)) for x in carrier(alg, :Animal)])
reimported_species = sort([string(eval_att(alg2, :species, x)) for x in carrier(alg2, :Animal)])
println("\nOriginal species: ", original_species)
println("Re-imported species: ", reimported_species)
println("Data matches: ", original_species == reimported_species)
```

    Original: 5 animals, 3 habitats
    Re-imported: 5 animals, 3 habitats

    Original species: ["Camel", "Deer", "Dolphin", "Owl", "Shark"]
    Re-imported species: ["Camel", "Deer", "Dolphin", "Owl", "Shark"]
    Data matches: true

The carrier sizes and attribute values are preserved through the
round-trip. Generator names may differ (since export assigns new numeric
IDs), but the algebraic structure is identical.

## Integrating CSV Data with CQL Operations

The real power of CQL comes from combining imported CSV data with
categorical operations. Here we demonstrate using an **uber-flower
query** to transform the imported animal data.

### Flattening with a Query

Suppose we want to “denormalize” the animal database into a flat table
that combines animal and habitat information into a single entity.

We define the original schema, the flat target schema, and a query all
in one CQL program. The query says: for each `Animal`, create a `Record`
with the animal’s `species` and `legs`, plus the `name` and `climate`
from its habitat (following the `livesIn` foreign key).

``` julia
full_env = cql"""
typeside Ty = sql

schema AnimalDB = literal : Ty {
    entities
        Animal Habitat
    foreign_keys
        livesIn : Animal -> Habitat
    attributes
        species : Animal -> String
        legs : Animal -> String
        name : Habitat -> String
        climate : Habitat -> String
}

schema FlatAnimal = literal : Ty {
    entities
        Record
    attributes
        species : Record -> String
        legs : Record -> String
        habitat : Record -> String
        climate : Record -> String
}

query Flatten = literal : AnimalDB -> FlatAnimal {
    entity Record -> {
        from
            a : Animal
        attributes
            species -> species(a)
            legs -> legs(a)
            habitat -> name(livesIn(a))
            climate -> climate(livesIn(a))
    }
}
"""

# Import CSV data using the schema from the full environment
inst = import_csv_instance(data_dir, full_env.AnimalDB)

# Evaluate the query on the imported instance
flat_inst = CQL.eval_query_instance(full_env.Flatten, inst, default_options())
flat_alg = flat_inst.algebra

println("Flattened records: ", length(carrier(flat_alg, :Record)))
println("\n--- Flat Animal Table ---")
for x in carrier(flat_alg, :Record)
    sp = eval_att(flat_alg, :species, x)
    lg = eval_att(flat_alg, :legs, x)
    hab = eval_att(flat_alg, :habitat, x)
    cl = eval_att(flat_alg, :climate, x)
    println("  species=$sp, legs=$lg, habitat=$hab, climate=$cl")
end
```

    Flattened records: 5

    --- Flat Animal Table ---
      species=Owl, legs=2, habitat=Forest, climate=Temperate
      species=Deer, legs=4, habitat=Forest, climate=Temperate
      species=Shark, legs=0, habitat=Ocean, climate=Tropical
      species=Dolphin, legs=0, habitat=Ocean, climate=Tropical
      species=Camel, legs=4, habitat=Desert, climate=Arid

The query produces 5 records (one per animal), each with denormalized
habitat information.

### Exporting Query Results

We can export the flattened result to CSV:

``` julia
flat_export_dir = joinpath(mktempdir(), "FlatExport")
export_csv_instance(flat_inst, flat_export_dir)

println("=== Exported Record.csv ===")
println(read(joinpath(flat_export_dir, "Record.csv"), String))
```

    === Exported Record.csv ===
    "id","climate","habitat","legs","species"
    "0","Temperate","Forest","4","Deer"
    "1","Arid","Desert","4","Camel"
    "2","Temperate","Forest","2","Owl"
    "3","Tropical","Ocean","0","Dolphin"
    "4","Tropical","Ocean","0","Shark"

This completes the pipeline: **CSV files** $\rightarrow$ **CQL
instance** $\rightarrow$ **query transformation** $\rightarrow$ **CSV
export**.

## Data Migration with CSV

CQL’s functorial data migration operations (delta and sigma) also work
with imported CSV data. Here we demonstrate a **sigma** (pushforward)
migration that merges two entities into one.

``` julia
mig_env = cql"""
typeside Ty = sql

schema AnimalDB = literal : Ty {
    entities
        Animal Habitat
    foreign_keys
        livesIn : Animal -> Habitat
    attributes
        species : Animal -> String
        legs : Animal -> String
        name : Habitat -> String
        climate : Habitat -> String
}

schema SimpleDB = literal : Ty {
    entities
        Thing
    attributes
        label : Thing -> String
}

mapping M = literal : AnimalDB -> SimpleDB {
    entity
        Animal -> Thing
        foreign_keys
            livesIn -> Thing
        attributes
            species -> lambda x. label(x)
            legs -> lambda x. label(x)
    entity
        Habitat -> Thing
        attributes
            name -> lambda x. label(x)
            climate -> lambda x. label(x)
}
"""

# Import CSV and migrate
inst = import_csv_instance(data_dir, mig_env.AnimalDB)
migrated = eval_sigma_instance(mig_env.M, inst, default_options())
migrated_alg = migrated.algebra

println("Original: ", length(carrier(inst.algebra, :Animal)), " animals + ",
        length(carrier(inst.algebra, :Habitat)), " habitats")
println("After sigma: ", length(carrier(migrated_alg, :Thing)), " things")

# Export migrated data
sigma_dir = joinpath(mktempdir(), "SigmaExport")
export_csv_instance(migrated, sigma_dir)
println("\n=== Exported Thing.csv ===")
println(read(joinpath(sigma_dir, "Thing.csv"), String))
```

    Original: 5 animals + 3 habitats
    After sigma: 3 things

    === Exported Thing.csv ===
    "id","label"
    "0","Temperate"
    "1","Arid"
    "2","0"

The sigma migration merges all animals and habitats into a single
`Thing` entity. Animals and habitats that are related (an animal lives
in a habitat) get identified, demonstrating CQL’s ability to compute
categorical colimits.

## Summary

CQL.jl provides two functions for CSV integration:

| Function                             | Description                        |
|--------------------------------------|------------------------------------|
| `import_csv_instance(dir, schema)`   | Read CSV files into a CQL instance |
| `export_csv_instance(instance, dir)` | Write a CQL instance to CSV files  |

**CSV file format:**

- One file per entity: `EntityName.csv`
- First column: `id` (unique row identifier)
- Foreign key columns: contain IDs referencing target entity rows
- Attribute columns: contain attribute values

**Key points:**

- Imported instances use **saturated algebra** (direct interpretation,
  no theorem proving)
- Missing attribute values become **Skolem terms** (nulls)
- Foreign key values must reference valid IDs in the target entity
- Exported files use **globally unique IDs** across all entities
- Imported data works seamlessly with CQL queries, delta, and sigma
  operations

## Julia DSL

The examples above use the `cql"""..."""` string macro for schema and
query definitions. CQL.jl also provides Julia-native macros. Here is how
the AnimalDB schema and flattening query look using the DSL:

``` julia
using CQL

Ty_sql = cql"""typeside Ty = sql""".Ty  # sql typeside still uses cql syntax

AnimalDB = @schema Ty_sql begin
    @entities Animal, Habitat
    livesIn : Animal → Habitat
    species : Animal ⇒ String
    legs : Animal ⇒ String
    name : Habitat ⇒ String
    climate : Habitat ⇒ String
end

println("AnimalDB entities: ", AnimalDB.ens)
println("Foreign keys: ", collect(keys(AnimalDB.fks)))
```

    AnimalDB entities: Set([:Animal, :Habitat])
    Foreign keys: [:livesIn]

Note: CSV import (`import_csv_instance`) and export
(`export_csv_instance`) are Julia functions that work with schema
objects directly, so they are already “native Julia.” The `@schema`
macro defines the schema structure, while the import/export functions
handle the data I/O.
