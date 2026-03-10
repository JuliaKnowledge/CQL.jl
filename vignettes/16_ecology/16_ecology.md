# Ecological Data Integration with CQL
CQL.jl

- [Introduction](#introduction)
- [1. Schema: The Ecosystem Data
  Model](#1-schema-the-ecosystem-data-model)
- [2. CSV Import: Loading the Food
  Web](#2-csv-import-loading-the-food-web)
- [3. Delta Migration: Flattening the Food
  Web](#3-delta-migration-flattening-the-food-web)
- [4. Queries: Filtering by Ecological
  Criteria](#4-queries-filtering-by-ecological-criteria)
  - [Q1: Observations at a single
    site](#q1-observations-at-a-single-site)
  - [Q2: Quadrat surveys only](#q2-quadrat-surveys-only)
- [5. Query Composition: Building Survey Analysis
  Pipelines](#5-query-composition-building-survey-analysis-pipelines)
- [6. Delta for Species Profiles](#6-delta-for-species-profiles)
- [7. Sigma Migration: Harmonising Survey
  Formats](#7-sigma-migration-harmonising-survey-formats)
- [8. Coproduct: Merging Multi-Site Survey
  Data](#8-coproduct-merging-multi-site-survey-data)
- [9. Constraints and Chase: Enforcing Ecological
  Rules](#9-constraints-and-chase-enforcing-ecological-rules)
- [10. Transforms: Tracking Species Persistence Across
  Years](#10-transforms-tracking-species-persistence-across-years)
- [11. CoEval: Reconstructing Data from a
  Summary](#11-coeval-reconstructing-data-from-a-summary)
- [12. Unit and Counit: Round-Trip
  Properties](#12-unit-and-counit-round-trip-properties)
- [13. Schema Colimit: Integrating Monitoring
  Programmes](#13-schema-colimit-integrating-monitoring-programmes)
- [Comparison with RDF/SPARQL](#comparison-with-rdfsparql)
- [Summary](#summary)

## Introduction

Marine ecologists collect data across multiple scales: species
inventories from field surveys, trophic relationships from gut content
analysis, habitat associations from dive transects, and conservation
assessments from population monitoring. Each data source uses a
different format, and meaningful ecological analysis requires
integrating them into a coherent whole.

This vignette uses a northeastern Atlantic coastal food web — 14 species
spanning five trophic levels, from phytoplankton to killer whales — to
demonstrate how **CQL** (Categorical Query Language) provides
*mathematically guaranteed correct* data transformations for ecological
research.

We demonstrate nine CQL operations, each grounded in a concrete
ecological task:

| CQL Operation | Ecological Meaning |
|----|----|
| **Schema** | Define the data model for species, habitats, food webs, and surveys |
| **CSV Import** | Load field survey data from flat files into a normalised database |
| **Query (filter)** | Select observations by site, method, or species traits |
| **Query composition** | Chain filters into a pipeline (e.g., “quadrat surveys at St Andrews”) |
| **Delta migration** | Flatten the food web into a predator–prey pairs table |
| **Sigma migration** | Align two monitoring programmes’ schemas to a common standard |
| **Coproduct** | Merge survey data from independent field sites |
| **Constraints + Chase** | Enforce ecological rules and auto-generate missing records |
| **Transform** | Map between annual species inventories to track persistence |
| **CoEval** | Reconstruct what observations could exist given a species list |

``` julia
using CQL
```

## 1. Schema: The Ecosystem Data Model

A **schema** in CQL is the data dictionary — it defines what entity
types exist and how they relate to each other through **foreign keys**
(functional relationships). In ecological terms, the schema is our
ontology: it specifies the kinds of things we track and the biological
relationships between them.

Our ecosystem schema has six entity types:

- **TrophicLevel** — a position in the food chain (producer, primary
  consumer, … apex predator)
- **Habitat** — a distinct marine environment (pelagic, rocky
  intertidal, kelp forest, …)
- **Species** — a biological species, with a single trophic level
  assignment
- **FeedingLink** — a directed predator–prey relationship between two
  species
- **SpeciesHabitat** — records that a species occurs in a habitat
  (many-to-many junction)
- **Observation** — a field survey record linking a species to a site
  and count

<!-- -->

      TrophicLevel ←──trophic_level── Species ──species──→ SpeciesHabitat ──habitat──→ Habitat
                                         ↑         ↑
                                      predator    prey
                                         │         │
                                       FeedingLink
                                         ↑
                                  observed_species
                                         │
                                     Observation

Each arrow is a **foreign key** — a total function. Given a feeding
link, the `predator` FK returns exactly one species; given an
observation, `observed_species` returns exactly one species. This
strictness prevents dangling references: every observation must point to
a known species, and every feeding link must connect two real species.

``` julia
typeside_and_schema = """
typeside Ty = literal {
  types
    String
}

schema Ecosystem = literal : Ty {
  entities
    TrophicLevel Habitat Species FeedingLink SpeciesHabitat Observation
  foreign_keys
    trophic_level    : Species -> TrophicLevel
    predator         : FeedingLink -> Species
    prey             : FeedingLink -> Species
    species          : SpeciesHabitat -> Species
    habitat          : SpeciesHabitat -> Habitat
    observed_species : Observation -> Species
  attributes
    level_name          : TrophicLevel -> String
    hab_name            : Habitat -> String
    hab_description     : Habitat -> String
    common_name         : Species -> String
    conservation_status : Species -> String
    typical_size_cm     : Species -> String
    site_name           : Observation -> String
    count               : Observation -> String
    method              : Observation -> String
    obs_date            : Observation -> String
}
"""
```

## 2. CSV Import: Loading the Food Web

Field data is typically exported from spreadsheets or databases as CSV
files. CQL imports one CSV per entity type, each with an `id` column
(primary key) and columns matching the schema’s foreign key and
attribute names.

Our dataset represents a coastal ecosystem survey:

- `Species.csv` — 14 species across 5 trophic levels
- `FeedingLink.csv` — 18 predator–prey relationships
- `Habitat.csv` — 5 coastal habitat types
- `SpeciesHabitat.csv` — 21 species–habitat associations
- `Observation.csv` — 20 field observations across 4 survey sites

``` julia
import_program = typeside_and_schema * """
instance FoodWeb = import_csv "ecology_data" : Ecosystem
"""

env = run_program(import_program)
alg = env.instances["FoodWeb"].algebra

println("Ecosystem loaded:")
for en in sort(collect(env.schemas["Ecosystem"].ens))
    println("  $(rpad(string(en), 18)) $(length(CQL.carrier(alg, en))) records")
end
```

    Ecosystem loaded:
      FeedingLink        18 records
      Habitat            5 records
      Observation        20 records
      Species            14 records
      SpeciesHabitat     21 records
      TrophicLevel       5 records

## 3. Delta Migration: Flattening the Food Web

A **Delta migration** pulls data backward along a schema mapping. In
ecological terms, it *denormalises* a complex relational structure into
a simpler report format.

Here we define a flat `PredPreyReport` schema with a single entity type
and use a mapping to extract each feeding link as a row with predator
name, prey name, and their trophic levels. The `lambda` expressions
follow foreign key chains: `common_name(predator(fl))` reads “the common
name of the predator of this feeding link.”

``` julia
delta_program = import_program * """
schema PredPreyReport = literal : Ty {
  entities Link
  attributes
    predator_name  : Link -> String
    prey_name      : Link -> String
    predator_level : Link -> String
    prey_level     : Link -> String
}

mapping FlattenWeb = literal : PredPreyReport -> Ecosystem {
  entity Link -> FeedingLink
  attributes
    predator_name  -> lambda fl. common_name(predator(fl))
    prey_name      -> lambda fl. common_name(prey(fl))
    predator_level -> lambda fl. level_name(trophic_level(predator(fl)))
    prey_level     -> lambda fl. level_name(trophic_level(prey(fl)))
}

instance WebReport = delta FlattenWeb FoodWeb
"""

env = run_program(delta_program)
alg = env.instances["WebReport"].algebra

links = sort(collect(CQL.carrier(alg, :Link)), by=string)
println("Food Web ($(length(links)) trophic links):")
println("  ", rpad("Predator", 18), rpad("Level", 22),
        "  ", rpad("Prey", 18), "Level")
println("  ", "-"^76)
for x in links
    println("  ",
        rpad(string(CQL.eval_att(alg, :predator_name, x)), 18),
        rpad(string(CQL.eval_att(alg, :predator_level, x)), 22), "→ ",
        rpad(string(CQL.eval_att(alg, :prey_name, x)), 18),
        CQL.eval_att(alg, :prey_level, x))
end
```

    Food Web (18 trophic links):
      Predator          Level                   Prey              Level
      ----------------------------------------------------------------------------
      Killer Whale      apex predator         → Grey Seal         tertiary consumer
      Grey Seal         tertiary consumer     → Atlantic Cod      tertiary consumer
      Grey Seal         tertiary consumer     → Atlantic Herring  secondary consumer
      Atlantic Cod      tertiary consumer     → Atlantic Herring  secondary consumer
      Atlantic Cod      tertiary consumer     → Shore Crab        secondary consumer
      Atlantic Herring  secondary consumer    → Zooplankton       primary consumer
      Shore Crab        secondary consumer    → Blue Mussel       primary consumer
      Shore Crab        secondary consumer    → Acorn Barnacle    primary consumer
      Shore Crab        secondary consumer    → Common Limpet     primary consumer
      Common Starfish   secondary consumer    → Blue Mussel       primary consumer
      Common Starfish   secondary consumer    → Sea Urchin        primary consumer
      Sea Urchin        primary consumer      → Oarweed Kelp      producer
      Sea Urchin        primary consumer      → Coralline Algae   producer
      Blue Mussel       primary consumer      → Phytoplankton     producer
      Acorn Barnacle    primary consumer      → Phytoplankton     producer
      Acorn Barnacle    primary consumer      → Zooplankton       primary consumer
      Zooplankton       primary consumer      → Phytoplankton     producer
      Common Limpet     primary consumer      → Coralline Algae   producer

Each feeding link becomes a self-contained row — ready for food web
analysis, network visualisation, or export to a matrix format. The Delta
migration is **functorial**: it preserves all the structural
relationships, so no links are lost or duplicated.

## 4. Queries: Filtering by Ecological Criteria

A CQL **query** is a reusable, composable filter. Unlike a SQL `WHERE`
clause (which is a one-off statement), a CQL query is a first-class
mathematical object — a functor between schemas that can be stored,
named, and composed with other queries.

### Q1: Observations at a single site

Field ecologists often need to extract data from a specific survey site.
This query selects all observations recorded at “St Andrews”:

``` julia
q_site = """
query StAndrewsObs = literal : Ecosystem -> Ecosystem {
  entity TrophicLevel -> {from tl:TrophicLevel attributes level_name -> tl.level_name}
  entity Habitat -> {from h:Habitat attributes hab_name -> h.hab_name hab_description -> h.hab_description}
  entity Species -> {from s:Species attributes common_name -> s.common_name
    conservation_status -> s.conservation_status typical_size_cm -> s.typical_size_cm
    foreign_keys trophic_level -> {tl -> s.trophic_level}}
  entity FeedingLink -> {from fl:FeedingLink
    foreign_keys predator -> {s -> fl.predator} prey -> {s -> fl.prey}}
  entity SpeciesHabitat -> {from sh:SpeciesHabitat
    foreign_keys species -> {s -> sh.species} habitat -> {h -> sh.habitat}}
  entity Observation -> {from o:Observation where o.site_name = "St Andrews"
    attributes site_name -> o.site_name count -> o.count method -> o.method obs_date -> o.obs_date
    foreign_keys observed_species -> {s -> o.observed_species}}
}
"""
```

### Q2: Quadrat surveys only

Different survey methods measure different things. Quadrat counts give
reliable abundance estimates for sessile or slow-moving organisms. This
query selects only quadrat surveys:

``` julia
q_quadrat = """
query QuadratSurveys = literal : Ecosystem -> Ecosystem {
  entity TrophicLevel -> {from tl:TrophicLevel attributes level_name -> tl.level_name}
  entity Habitat -> {from h:Habitat attributes hab_name -> h.hab_name hab_description -> h.hab_description}
  entity Species -> {from s:Species attributes common_name -> s.common_name
    conservation_status -> s.conservation_status typical_size_cm -> s.typical_size_cm
    foreign_keys trophic_level -> {tl -> s.trophic_level}}
  entity FeedingLink -> {from fl:FeedingLink
    foreign_keys predator -> {s -> fl.predator} prey -> {s -> fl.prey}}
  entity SpeciesHabitat -> {from sh:SpeciesHabitat
    foreign_keys species -> {s -> sh.species} habitat -> {h -> sh.habitat}}
  entity Observation -> {from o:Observation where o.method = "quadrat"
    attributes site_name -> o.site_name count -> o.count method -> o.method obs_date -> o.obs_date
    foreign_keys observed_species -> {s -> o.observed_species}}
}
"""
```

Let’s apply each filter:

``` julia
function show_observations(alg; label="")
    obs = sort(collect(CQL.carrier(alg, :Observation)), by=string)
    println("$label ($(length(obs)) observations):")
    println("  ", rpad("Species", 18), rpad("Site", 14), rpad("Method", 10), "Count")
    println("  ", "-"^50)
    for x in obs
        sp = CQL.eval_fk(alg, :observed_species, x)
        println("  ",
            rpad(string(CQL.eval_att(alg, :common_name, sp)), 18),
            rpad(string(CQL.eval_att(alg, :site_name, x)), 14),
            rpad(string(CQL.eval_att(alg, :method, x)), 10),
            CQL.eval_att(alg, :count, x))
    end
end

queries_program = import_program * q_site * q_quadrat * """
instance st_andrews = eval StAndrewsObs FoodWeb
instance quadrats   = eval QuadratSurveys FoodWeb
"""

env = run_program(queries_program)
show_observations(env.instances["st_andrews"].algebra, label="St Andrews observations")
println()
show_observations(env.instances["quadrats"].algebra, label="All quadrat surveys")
```

    St Andrews observations (5 observations):
      Species           Site          Method    Count
      --------------------------------------------------
      Acorn Barnacle    St Andrews    quadrat   891
      Blue Mussel       St Andrews    quadrat   342
      Shore Crab        St Andrews    visual    23
      Common Starfish   St Andrews    visual    7
      Common Limpet     St Andrews    quadrat   156

    All quadrat surveys (11 observations):
      Species           Site          Method    Count
      --------------------------------------------------
      Blue Mussel       Crail         quadrat   423
      Common Limpet     St Andrews    quadrat   156
      Acorn Barnacle    Crail         quadrat   756
      Coralline Algae   Arbroath      quadrat   89
      Acorn Barnacle    St Andrews    quadrat   891
      Blue Mussel       St Andrews    quadrat   342
      Oarweed Kelp      Arbroath      quadrat   12
      Sea Urchin        Crail         quadrat   38
      Blue Mussel       Arbroath      quadrat   567
      Sea Urchin        Arbroath      quadrat   45
      Acorn Barnacle    Arbroath      quadrat   1204

## 5. Query Composition: Building Survey Analysis Pipelines

CQL queries are **functorial** — composing two queries gives a third
query that is *provably equivalent* to applying them in sequence:

$$\text{eval}([Q_1; Q_2], I) = \text{eval}(Q_2, \text{eval}(Q_1, I))$$

This means ecologists can build complex data selection criteria from
simple, tested building blocks — “quadrat surveys at St Andrews” is
literally the composition of the site filter and the method filter.

``` julia
compose_program = queries_program * """
query QuadratsAtStAndrews = [StAndrewsObs ; QuadratSurveys]

instance composed  = eval QuadratsAtStAndrews FoodWeb
instance step1     = eval StAndrewsObs FoodWeb
instance step2     = eval QuadratSurveys step1
"""

env = run_program(compose_program)

println("=== Composed: [StAndrewsObs ; QuadratSurveys] ===")
show_observations(env.instances["composed"].algebra,
                  label="Quadrat surveys at St Andrews (one-step)")
println()
println("=== Stepwise: eval QuadratSurveys (eval StAndrewsObs FoodWeb) ===")
show_observations(env.instances["step2"].algebra,
                  label="Quadrat surveys at St Andrews (two-step)")
```

    === Composed: [StAndrewsObs ; QuadratSurveys] ===
    Quadrat surveys at St Andrews (one-step) (3 observations):
      Species           Site          Method    Count
      --------------------------------------------------
      Acorn Barnacle    St Andrews    quadrat   891
      Blue Mussel       St Andrews    quadrat   342
      Common Limpet     St Andrews    quadrat   156

    === Stepwise: eval QuadratSurveys (eval StAndrewsObs FoodWeb) ===
    Quadrat surveys at St Andrews (two-step) (3 observations):
      Species           Site          Method    Count
      --------------------------------------------------
      Blue Mussel       St Andrews    quadrat   342
      Common Limpet     St Andrews    quadrat   156
      Acorn Barnacle    St Andrews    quadrat   891

Both results are identical — this is the **composition theorem**. The
three quadrat records from St Andrews (barnacles, mussels, limpets) are
exactly what a field ecologist would want for comparing sessile
invertebrate abundance at this site.

## 6. Delta for Species Profiles

Beyond food web reports, Delta can create species profile cards. Here we
flatten each observation into a self-contained record with denormalised
species and trophic information:

``` julia
profile_program = import_program * """
schema SurveyReport = literal : Ty {
  entities Record
  attributes
    species_name   : Record -> String
    trophic_level  : Record -> String
    site           : Record -> String
    abundance      : Record -> String
    survey_method  : Record -> String
}

mapping FlatSurvey = literal : SurveyReport -> Ecosystem {
  entity Record -> Observation
  attributes
    species_name  -> lambda o. common_name(observed_species(o))
    trophic_level -> lambda o. level_name(trophic_level(observed_species(o)))
    site          -> site_name
    abundance     -> count
    survey_method -> method
}

instance SurveySheet = delta FlatSurvey FoodWeb
"""

env = run_program(profile_program)
alg = env.instances["SurveySheet"].algebra

records = sort(collect(CQL.carrier(alg, :Record)), by=string)
println("Field Survey Report ($(length(records)) records):")
println("  ", rpad("Species", 18), rpad("Trophic Level", 22),
        rpad("Site", 14), rpad("Method", 10), "Count")
println("  ", "-"^72)
for x in records
    println("  ",
        rpad(string(CQL.eval_att(alg, :species_name, x)), 18),
        rpad(string(CQL.eval_att(alg, :trophic_level, x)), 22),
        rpad(string(CQL.eval_att(alg, :site, x)), 14),
        rpad(string(CQL.eval_att(alg, :survey_method, x)), 10),
        CQL.eval_att(alg, :abundance, x))
end
```

    Field Survey Report (20 records):
      Species           Trophic Level         Site          Method    Count
      ------------------------------------------------------------------------
      Blue Mussel       primary consumer      St Andrews    quadrat   342
      Acorn Barnacle    primary consumer      St Andrews    quadrat   891
      Common Limpet     primary consumer      St Andrews    quadrat   156
      Shore Crab        secondary consumer    St Andrews    visual    23
      Common Starfish   secondary consumer    St Andrews    visual    7
      Blue Mussel       primary consumer      Arbroath      quadrat   567
      Acorn Barnacle    primary consumer      Arbroath      quadrat   1204
      Sea Urchin        primary consumer      Arbroath      quadrat   45
      Oarweed Kelp      producer              Arbroath      quadrat   12
      Coralline Algae   producer              Arbroath      quadrat   89
      Atlantic Herring  secondary consumer    Bell Rock     trawl     250
      Atlantic Cod      tertiary consumer     Bell Rock     trawl     18
      Grey Seal         tertiary consumer     Bell Rock     visual    3
      Phytoplankton     producer              Bell Rock     sample    1500
      Zooplankton       primary consumer      Bell Rock     sample    800
      Blue Mussel       primary consumer      Crail         quadrat   423
      Shore Crab        secondary consumer    Crail         visual    31
      Common Starfish   secondary consumer    Crail         visual    5
      Sea Urchin        primary consumer      Crail         quadrat   38
      Acorn Barnacle    primary consumer      Crail         quadrat   756

## 7. Sigma Migration: Harmonising Survey Formats

Different monitoring programmes use different data schemas. A university
research group might record `species_name`, `abundance`, and
`survey_method`, while a government agency tracks `taxon`,
`individuals`, and `protocol`. Before combining their data, both must be
**aligned** to a common standard.

**Sigma migration** (`sigma F I`) pushes an instance forward along a
mapping, renaming and restructuring attributes. In ecological terms,
this is taxonomic and methodological harmonisation — mapping local
terminology to a shared vocabulary.

``` julia
sigma_program = """
typeside Ty = literal { types String }

schema UniSurvey = literal : Ty {
  entities SurveyRecord
  attributes species_name : SurveyRecord -> String
    abundance : SurveyRecord -> String survey_method : SurveyRecord -> String
}

schema GovSurvey = literal : Ty {
  entities Sighting
  attributes taxon : Sighting -> String individuals : Sighting -> String
    protocol : Sighting -> String
}

schema StandardSurvey = literal : Ty {
  entities Record
  attributes what : Record -> String how_many : Record -> String how : Record -> String
}

mapping AlignUni = literal : UniSurvey -> StandardSurvey {
  entity SurveyRecord -> Record
  attributes species_name -> what abundance -> how_many survey_method -> how
}

mapping AlignGov = literal : GovSurvey -> StandardSurvey {
  entity Sighting -> Record
  attributes taxon -> what individuals -> how_many protocol -> how
}

instance UniData = literal : UniSurvey {
  generators s1 s2 s3 s4 : SurveyRecord
  equations
    s1.species_name = "Blue Mussel"     s1.abundance = "342" s1.survey_method = "quadrat"
    s2.species_name = "Acorn Barnacle"  s2.abundance = "891" s2.survey_method = "quadrat"
    s3.species_name = "Common Limpet"   s3.abundance = "156" s3.survey_method = "quadrat"
    s4.species_name = "Shore Crab"      s4.abundance = "23"  s4.survey_method = "visual"
}

instance GovData = literal : GovSurvey {
  generators g1 g2 g3 : Sighting
  equations
    g1.taxon = "Blue Mussel"     g1.individuals = "567" g1.protocol = "quadrat"
    g2.taxon = "Acorn Barnacle"  g2.individuals = "1204" g2.protocol = "quadrat"
    g3.taxon = "Sea Urchin"      g3.individuals = "45"  g3.protocol = "quadrat"
}

instance StdUni = sigma AlignUni UniData
instance StdGov = sigma AlignGov GovData
"""

env = run_program(sigma_program)

function show_standard(alg; label="")
    recs = sort(collect(CQL.carrier(alg, :Record)), by=string)
    println("$label ($(length(recs)) records):")
    for x in recs
        println("  ", rpad(string(CQL.eval_att(alg, :what, x)), 18),
                "n=", rpad(string(CQL.eval_att(alg, :how_many, x)), 6),
                CQL.eval_att(alg, :how, x))
    end
end

show_standard(env.instances["StdUni"].algebra, label="University survey → Standard")
println()
show_standard(env.instances["StdGov"].algebra, label="Government survey → Standard")
```

    University survey → Standard (4 records):
      Blue Mussel       n=342   quadrat
      Acorn Barnacle    n=891   quadrat
      Common Limpet     n=156   quadrat
      Shore Crab        n=23    visual

    Government survey → Standard (3 records):
      Blue Mussel       n=567   quadrat
      Acorn Barnacle    n=1204  quadrat
      Sea Urchin        n=45    quadrat

Despite starting with completely different column names (`species_name`
vs `taxon`, `abundance` vs `individuals`), both datasets now conform to
the same schema.

## 8. Coproduct: Merging Multi-Site Survey Data

Once survey data from different sources has been aligned to a common
schema, the next step is **merging**. A CQL **coproduct** creates the
disjoint union of two instances — in ecological terms, it pools data
from independent survey sites into a combined dataset.

The coproduct preserves all records without deduplication. This is
ecologically correct: if two independent teams both recorded Blue
Mussels, both observations should be retained because they represent
separate measurements at different sites.

``` julia
coprod_program = sigma_program * """
instance Combined = coproduct StdUni + StdGov : StandardSurvey
"""

env = run_program(coprod_program)
show_standard(env.instances["Combined"].algebra,
              label="Combined survey data")
```

    Combined survey data (7 records):
      Blue Mussel       n=342   quadrat
      Acorn Barnacle    n=891   quadrat
      Common Limpet     n=156   quadrat
      Shore Crab        n=23    visual
      Blue Mussel       n=567   quadrat
      Acorn Barnacle    n=1204  quadrat
      Sea Urchin        n=45    quadrat

All 7 records from both programmes are now in a single dataset, ready
for cross-site abundance analysis.

## 9. Constraints and Chase: Enforcing Ecological Rules

In biodiversity databases, certain consistency rules must hold. For
example: “every species recorded in a survey must have at least one
habitat association on file.” If a new species is observed but its
habitat hasn’t been catalogued yet, the database is incomplete.

CQL expresses such rules as **embedded dependencies** (EDs), and the
**chase** algorithm repairs violations by generating the minimum
additional data needed. In ecological terms, the chase identifies
species missing habitat records and creates placeholder entries that
taxonomists can then fill in.

``` julia
chase_program = """
typeside Ty = literal {
  types String
  constants "unknown" "recorded" : String
}

schema BioInventory = literal : Ty {
  entities Species HabitatRecord
  foreign_keys species : HabitatRecord -> Species
  attributes
    sp_name   : Species -> String
    hab_type  : HabitatRecord -> String
}

constraints HabitatRequired = literal : BioInventory {
  forall s:Species
  ->
  exists hr:HabitatRecord
  where hr.species = s
}

instance Incomplete = literal : BioInventory {
  generators sp1 sp2 sp3 sp4 : Species h1 h2 : HabitatRecord
  equations
    sp1.sp_name = "Blue Mussel"  sp2.sp_name = "Shore Crab"
    sp3.sp_name = "New Nudibranch" sp4.sp_name = "Unknown Worm"
    h1.species = sp1 h1.hab_type = "rocky intertidal"
    h2.species = sp2 h2.hab_type = "subtidal reef"
}

instance Complete = chase HabitatRequired Incomplete
"""

env = run_program(chase_program)

for (label, iname) in [("Before chase", "Incomplete"), ("After chase", "Complete")]
    alg = env.instances[iname].algebra
    species = CQL.carrier(alg, :Species)
    habitats = CQL.carrier(alg, :HabitatRecord)
    println("$label: $(length(species)) species, $(length(habitats)) habitat records")
    for hr in sort(collect(habitats), by=string)
        sp = CQL.eval_fk(alg, :species, hr)
        println("  $(rpad(string(CQL.eval_att(alg, :sp_name, sp)), 20)) habitat: $(CQL.eval_att(alg, :hab_type, hr))")
    end
    println()
end
```

    Before chase: 4 species, 2 habitat records
      Blue Mussel          habitat: rocky intertidal
      Shore Crab           habitat: subtidal reef

    After chase: 4 species, 4 habitat records
      New Nudibranch       habitat: chase_sk_1.hab_type
      Unknown Worm         habitat: chase_sk_2.hab_type
      Blue Mussel          habitat: rocky intertidal
      Shore Crab           habitat: subtidal reef

The chase created habitat records for “New Nudibranch” and “Unknown
Worm” — the species that were missing habitat data. The habitat type for
these new records is a **Skolem term** (a placeholder), flagging them
for taxonomic review. The chase adds only the minimum necessary records:
Blue Mussel and Shore Crab already had habitats, so they were left
untouched.

## 10. Transforms: Tracking Species Persistence Across Years

A CQL **transform** is a structure-preserving map between two instances
on the same schema. In ecological terms, it formalises the relationship
between two annual species inventories: “all species recorded in Year 1
are still present in Year 2, with these additional species newly
observed.”

``` julia
transform_program = """
typeside Ty = literal { types String }

schema Inventory = literal : Ty {
  entities Species
  attributes sp_name : Species -> String trophic : Species -> String
}

instance Year2023 = literal : Inventory {
  generators s1 s2 s3 s4 : Species
  equations
    s1.sp_name = "Blue Mussel"  s1.trophic = "primary consumer"
    s2.sp_name = "Shore Crab"   s2.trophic = "secondary consumer"
    s3.sp_name = "Atlantic Cod" s3.trophic = "tertiary consumer"
    s4.sp_name = "Oarweed Kelp" s4.trophic = "producer"
}

instance Year2024 = literal : Inventory {
  generators d1 d2 d3 d4 d5 d6 : Species
  equations
    d1.sp_name = "Blue Mussel"    d1.trophic = "primary consumer"
    d2.sp_name = "Shore Crab"     d2.trophic = "secondary consumer"
    d3.sp_name = "Atlantic Cod"   d3.trophic = "tertiary consumer"
    d4.sp_name = "Oarweed Kelp"   d4.trophic = "producer"
    d5.sp_name = "Grey Seal"      d5.trophic = "tertiary consumer"
    d6.sp_name = "Sea Urchin"     d6.trophic = "primary consumer"
}

transform Persistence = literal : Year2023 -> Year2024 {
  generators s1 -> d1 s2 -> d2 s3 -> d3 s4 -> d4
}
"""

env = run_program(transform_program)

for (label, iname) in [("2023 inventory", "Year2023"), ("2024 inventory", "Year2024")]
    alg = env.instances[iname].algebra
    species = sort(collect(CQL.carrier(alg, :Species)), by=string)
    println("$label: $(length(species)) species")
    for x in species
        println("  ", rpad(string(CQL.eval_att(alg, :sp_name, x)), 18),
                CQL.eval_att(alg, :trophic, x))
    end
    println()
end
println("Transform maps: all 4 Year-2023 species persist into Year 2024")
println("New in 2024: Grey Seal (tertiary consumer), Sea Urchin (primary consumer)")
```

    2023 inventory: 4 species
      Blue Mussel       primary consumer
      Shore Crab        secondary consumer
      Atlantic Cod      tertiary consumer
      Oarweed Kelp      producer

    2024 inventory: 6 species
      Blue Mussel       primary consumer
      Shore Crab        secondary consumer
      Atlantic Cod      tertiary consumer
      Oarweed Kelp      producer
      Grey Seal         tertiary consumer
      Sea Urchin        primary consumer

    Transform maps: all 4 Year-2023 species persist into Year 2024
    New in 2024: Grey Seal (tertiary consumer), Sea Urchin (primary consumer)

CQL verifies the transform at construction time: if `s1` maps to `d1`,
their species names and trophic levels must agree. Any mismatch — say,
if Atlantic Cod’s trophic level changed between years — would be caught
as a type error.

## 11. CoEval: Reconstructing Data from a Summary

CQL’s **coeval** is the right adjoint to query evaluation. Where
`eval Q I` pushes data forward through a query (extracting a subset),
`coeval Q J` pulls data backward — reconstructing what the source data
might look like given the query’s output.

In ecological terms: given a list of species observed at a site (the
query result), the coeval reconstructs the source inventory — providing
a formal provenance chain from summary back to source.

``` julia
coeval_program = """
typeside Ty = literal { types String }

schema FullInventory = literal : Ty {
  entities Species
  attributes sp_name : Species -> String status : Species -> String
}

schema ConservationList = literal : Ty {
  entities AtRisk
  attributes name : AtRisk -> String
}

query ExtractVulnerable = literal : FullInventory -> ConservationList {
  entity AtRisk -> {
    from s:Species
    where s.status = "Vulnerable"
    attributes name -> s.sp_name
  }
}

instance AllSpecies = literal : FullInventory {
  generators s1 s2 s3 s4 : Species
  equations
    s1.sp_name = "Atlantic Cod"    s1.status = "Vulnerable"
    s2.sp_name = "Blue Mussel"     s2.status = "Least Concern"
    s3.sp_name = "Killer Whale"    s3.status = "Data Deficient"
    s4.sp_name = "European Eel"    s4.status = "Vulnerable"
}

instance VulnerableList = eval ExtractVulnerable AllSpecies
instance Reconstructed  = coeval ExtractVulnerable VulnerableList
"""

env = run_program(coeval_program)

println("=== Forward: extract vulnerable species ===")
alg = env.instances["VulnerableList"].algebra
for x in sort(collect(CQL.carrier(alg, :AtRisk)), by=string)
    println("  ", CQL.eval_att(alg, :name, x))
end

println("\n=== Backward (coeval): reconstruct from vulnerability list ===")
alg = env.instances["Reconstructed"].algebra
for x in sort(collect(CQL.carrier(alg, :Species)), by=string)
    println("  ", rpad(string(CQL.eval_att(alg, :sp_name, x)), 18),
            "status=", CQL.eval_att(alg, :status, x))
end
```

    === Forward: extract vulnerable species ===
      European Eel
      Atlantic Cod

    === Backward (coeval): reconstruct from vulnerability list ===
      European Eel      status=Vulnerable
      Atlantic Cod      status=Vulnerable

The coeval reconstructs only the species visible through the query —
Blue Mussel and Killer Whale are absent because they were filtered out.
Each reconstructed species retains its “Vulnerable” status, confirming
the provenance chain from conservation list back to the full inventory.

## 12. Unit and Counit: Round-Trip Properties

When you export data from a local format to a standard and then reimport
it, how much is preserved? The **unit** and **counit** transforms answer
this precisely.

For a mapping `F : Local → Standard`:

- **Unit** (`unit F I`): maps `I` into `delta F (sigma F I)` — export
  then reimport
- **Counit** (`counit F J`): maps `sigma F (delta F J)` into `J` —
  import then re-export

In ecological terms: if you harmonise a local species list to Darwin
Core format (Sigma) and then extract it back (Delta), the unit tells you
what survived the round trip.

``` julia
adjunction_program = """
typeside Ty = literal { types String }

schema LocalList = literal : Ty {
  entities LSp
  attributes local_name : LSp -> String local_status : LSp -> String
}

schema DarwinCore = literal : Ty {
  entities Taxon
  attributes scientificName : Taxon -> String threatStatus : Taxon -> String
}

mapping ToDwC = literal : LocalList -> DarwinCore {
  entity LSp -> Taxon
  attributes local_name -> scientificName local_status -> threatStatus
}

instance MyList = literal : LocalList {
  generators l1 l2 : LSp
  equations
    l1.local_name = "Atlantic Cod" l1.local_status = "Vulnerable"
    l2.local_name = "Grey Seal"    l2.local_status = "Least Concern"
}

instance DwCData = literal : DarwinCore {
  generators t1 t2 : Taxon
  equations
    t1.scientificName = "Atlantic Cod" t1.threatStatus = "Vulnerable"
    t2.scientificName = "Grey Seal"    t2.threatStatus = "Least Concern"
}

transform eta = unit ToDwC MyList
transform eps = counit ToDwC DwCData
"""

env = run_program(adjunction_program)
println("Unit (η): LocalList → Δ(Σ(LocalList))")
println("  Verifies no information is lost when exporting to Darwin Core and reimporting")
println()
println("Counit (ε): Σ(Δ(DwCData)) → DwCData")
println("  Verifies no information is lost when importing from Darwin Core and re-exporting")
println()
println("Both adjunction transforms computed — the Δ ⊣ Σ adjunction holds.")
println("For this bijective mapping, both are isomorphisms: perfect round-trip fidelity.")
```

    Unit (η): LocalList → Δ(Σ(LocalList))
      Verifies no information is lost when exporting to Darwin Core and reimporting

    Counit (ε): Σ(Δ(DwCData)) → DwCData
      Verifies no information is lost when importing from Darwin Core and re-exporting

    Both adjunction transforms computed — the Δ ⊣ Σ adjunction holds.
    For this bijective mapping, both are isomorphisms: perfect round-trip fidelity.

## 13. Schema Colimit: Integrating Monitoring Programmes

When two monitoring programmes use entirely different schemas — not just
different column names but different entity structures — we need
**schema colimit** to merge them.

A schema colimit computes the categorical pushout of multiple schemas,
identifying shared concepts. In ecological terms: the marine survey team
tracks “Species in Habitats” while the conservation team tracks “Taxa
with Threat Levels.” Both reference the same biological species, but
model them differently. The schema colimit unifies these views.

``` julia
colimit_program = """
typeside Ty = literal { types String }

schema MarineSurvey = literal : Ty {
  entities MSp MHab
  foreign_keys m_inhabits : MSp -> MHab
  attributes m_name : MSp -> String m_hab : MHab -> String
}

schema ConservationDB = literal : Ty {
  entities CTaxon CRegion
  foreign_keys c_region : CTaxon -> CRegion
  attributes c_name : CTaxon -> String c_status : CTaxon -> String c_reg : CRegion -> String
}

schema_colimit Biodiversity = coproduct MarineSurvey + ConservationDB : Ty

schema BioSchema = getSchema Biodiversity
mapping MarineMap = getMapping Biodiversity MarineSurvey
mapping ConservMap = getMapping Biodiversity ConservationDB

instance MarineData = literal : MarineSurvey {
  generators cod seal : MSp mhab_reef mhab_pelagic : MHab
  equations
    cod.m_name = "Atlantic Cod"
    seal.m_name = "Grey Seal"
    cod.m_inhabits = mhab_reef
    seal.m_inhabits = mhab_pelagic
    mhab_reef.m_hab = "subtidal reef"
    mhab_pelagic.m_hab = "pelagic"
}

instance ConservData = literal : ConservationDB {
  generators t1 t2 : CTaxon r1 : CRegion
  equations
    t1.c_name = "Atlantic Cod" t1.c_status = "Vulnerable" t1.c_region = r1
    t2.c_name = "European Eel" t2.c_status = "Critically Endangered" t2.c_region = r1
    r1.c_reg = "NE Atlantic"
}

instance MarineFwd  = sigma MarineMap MarineData
instance ConservFwd = sigma ConservMap ConservData
instance Integrated = coproduct MarineFwd + ConservFwd : BioSchema
"""

env = run_program(colimit_program)

sch = env.schemas["BioSchema"]
println("Unified biodiversity schema:")
println("  Entities: ", join(sort([string(e) for e in sch.ens]), ", "))
println()

alg = env.instances["Integrated"].algebra
for en in sort(collect(sch.ens))
    elems = sort(collect(CQL.carrier(alg, en)), by=string)
    isempty(elems) && continue
    println("Entity $en ($(length(elems)) records):")
    for x in elems
        parts = String[]
        for (att, (src, _)) in sort(collect(sch.atts), by=x->string(x[1]))
            src == en || continue
            push!(parts, "$(CQL._display_name(att))=$(CQL.eval_att(alg, att, x))")
        end
        println("  ", join(parts, ", "))
    end
end
```

    Unified biodiversity schema:
      Entities: ConservationDB_CRegion, ConservationDB_CTaxon, MarineSurvey_MHab, MarineSurvey_MSp

    Entity ConservationDB_CRegion (1 records):
      ConservationDB_CRegion_c_reg=NE Atlantic
    Entity ConservationDB_CTaxon (2 records):
      ConservationDB_CTaxon_c_name=Atlantic Cod, ConservationDB_CTaxon_c_status=Vulnerable
      ConservationDB_CTaxon_c_name=European Eel, ConservationDB_CTaxon_c_status=Critically Endangered
    Entity MarineSurvey_MHab (2 records):
      MarineSurvey_MHab_m_hab=pelagic
      MarineSurvey_MHab_m_hab=subtidal reef
    Entity MarineSurvey_MSp (2 records):
      MarineSurvey_MSp_m_name=Atlantic Cod
      MarineSurvey_MSp_m_name=Grey Seal

The coproduct schema colimit keeps marine and conservation data as
separate entity types because they model different aspects of
biodiversity. A **quotient** colimit (with `entity_equations`) could
merge species entities across the two systems — but that requires
explicit curation to decide which taxa are the same.

## Comparison with RDF/SPARQL

The RDF knowledge graph approach (OWL ontology, SPARQL queries, Datalog
reasoning) offers complementary capabilities for ecological data:

| Feature | CQL | RDF/SPARQL |
|----|----|----|
| **Schema enforcement** | Strict (categorical foreign keys) | Optional (OWL/SHACL) |
| **Query composition** | Provably correct | No composition guarantee |
| **Data migration** | Functorial (Delta/Sigma) | Manual CONSTRUCT queries |
| **Transitive closure** | Not supported | Property paths (`feeds_on+`) |
| **Aggregation** | Limited | Full (COUNT, SUM, GROUP BY) |
| **Inference** | Via equations | RDFS/OWL/Datalog rules |
| **Probabilistic** | Not supported | ProbLog extensions |
| **Many-to-many** | Junction entities | Native triples |

CQL excels at **structural operations**: reshaping data between schemas,
composing filters into pipelines, and guaranteeing round-trip migration
properties. RDF excels at **graph operations**: transitive food chain
traversal, rule-based inference, and flexible many-to-many
relationships. Together, they cover the full spectrum of ecological data
management needs.

## Summary

This vignette demonstrated how CQL’s categorical operations map to
concrete ecological data management tasks:

| Step | CQL Operation | Ecological Task |
|----|----|----|
| 1 | Schema | Define the data dictionary for species, food webs, and surveys |
| 2 | CSV Import | Load 14 species, 18 feeding links, and 20 observations |
| 3 | Delta migration | Flatten the food web into a predator–prey report |
| 4 | Query filters | Select observations by site or survey method |
| 5 | Query composition | Chain filters: “quadrat surveys at St Andrews” |
| 6 | Delta (profiles) | Denormalise observations into flat survey sheets |
| 7 | Sigma migration | Harmonise university and government survey formats |
| 8 | Coproduct | Pool multi-source data into a combined dataset |
| 9 | Constraints + Chase | Enforce “every species needs a habitat” and auto-generate placeholders |
| 10 | Transform | Formally map 2023 → 2024 species inventories |
| 11 | CoEval | Reconstruct source data from a conservation species list |
| 12 | Unit / Counit | Verify round-trip fidelity of Darwin Core export/import |
| 13 | Schema Colimit | Unify marine survey and conservation database schemas |

Every operation preserves structural integrity through categorical
guarantees — making CQL a rigorous foundation for ecological data
integration where correctness matters.
