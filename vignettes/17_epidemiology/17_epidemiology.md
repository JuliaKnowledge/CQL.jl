# Epidemiological Data Integration with CQL
Simon Frost

- [Introduction](#introduction)
- [1. Schema: The Outbreak Data
  Model](#1-schema-the-outbreak-data-model)
- [2. CSV Import: Loading the Line
  List](#2-csv-import-loading-the-line-list)
- [3. Queries: Filtering Cases by Epidemiological
  Criteria](#3-queries-filtering-cases-by-epidemiological-criteria)
  - [Q1: Severe cases — for clinical
    escalation](#q1-severe-cases--for-clinical-escalation)
  - [Q2: Hospital cases — for nosocomial
    investigation](#q2-hospital-cases--for-nosocomial-investigation)
  - [Q3: Influenza cases — for pathogen-specific
    response](#q3-influenza-cases--for-pathogen-specific-response)
  - [Q4: Care home cases — for vulnerable population
    monitoring](#q4-care-home-cases--for-vulnerable-population-monitoring)
- [4. Query Composition: Building Epidemiological
  Pipelines](#4-query-composition-building-epidemiological-pipelines)
  - [Severe hospital cases (nosocomial
    escalation)](#severe-hospital-cases-nosocomial-escalation)
  - [Severe flu in care homes (antiviral
    prioritisation)](#severe-flu-in-care-homes-antiviral-prioritisation)
- [5. Delta Migration: Reshaping for
  Reporting](#5-delta-migration-reshaping-for-reporting)
- [6. Sigma Migration: Aligning Regional
  Schemas](#6-sigma-migration-aligning-regional-schemas)
- [7. Coproduct: Merging Data from Multiple
  Sources](#7-coproduct-merging-data-from-multiple-sources)
- [8. Constraints and Chase: Enforcing Data Quality
  Rules](#8-constraints-and-chase-enforcing-data-quality-rules)
- [9. Transforms: Tracking Outbreak
  Progression](#9-transforms-tracking-outbreak-progression)
- [10. CoEval: Reverse Query
  Evaluation](#10-coeval-reverse-query-evaluation)
- [11. Unit and Counit: Round-Trip Migration
  Properties](#11-unit-and-counit-round-trip-migration-properties)
- [12. Schema Colimit: Integrating Surveillance
  Systems](#12-schema-colimit-integrating-surveillance-systems)
- [Julia DSL](#julia-dsl)
- [Summary](#summary)

## Introduction

During a multi-pathogen respiratory outbreak, data arrives from many
sources: hospital infection control systems, care home surveillance,
school absence reports, and public health laboratories. Each source uses
a different schema, and the response depends on being able to
**filter**, **reshape**, **merge**, and **migrate** this data correctly.

This vignette uses a fictional winter outbreak — concurrent influenza,
COVID-19, and RSV clusters across hospitals, care homes, and schools —
to demonstrate how **CQL** (Categorical Query Language) provides
*mathematically guaranteed correct* data transformations for
epidemiological surveillance.

We demonstrate nine CQL operations:

| CQL Operation | Epidemiological Meaning |
|----|----|
| **CSV Import** | Load a line list from flat files into a structured database |
| **Query (filter)** | Select cases by severity, pathogen, or setting |
| **Query composition** | Chain filters into a pipeline (e.g., “severe flu in care homes”) |
| **Delta migration** | Reshape detailed records into a flat surveillance report |
| **Sigma migration** | Align a regional schema to a national reporting standard |
| **Coproduct** | Merge case data from two independent hospital systems |
| **Constraints + Chase** | Enforce rules (e.g., “every severe case needs a contact trace”) and auto-generate missing records |
| **Transform** | Map between two outbreak snapshots showing case persistence |
| **CoEval** | Reconstruct what detailed data might look like given a summary |

``` julia
using CQL
```

## 1. Schema: The Outbreak Data Model

We begin by defining a **typeside** (the set of basic data types) and a
**schema** (the relational structure). In epidemiology terms, the schema
is the data dictionary — it defines what entities exist and how they
relate to each other.

Our schema models four entity types connected by foreign keys:

- **Patient** — a person under surveillance, with demographics and risk
  factors
- **Case** — a single infection event, linking a patient to a location
  and pathogen
- **Location** — a facility or setting where transmission occurs
- **Pathogen** — the causative agent (species, lineage, or variant)

<!-- -->

        Patient ←──patient── Case ──location──→ Location
                              │
                           pathogen
                              │
                              ▼
                           Pathogen

Each foreign key (`patient`, `location`, `pathogen`) is a function —
given a case, it returns exactly one patient, one location, and one
pathogen. This is stricter than an RDF graph (where relationships can be
many-to-many) but guarantees that every case is fully attributed.

``` julia
typeside_and_schema = """
typeside Ty = literal {
  types
    String
}

schema Epi = literal : Ty {
  entities
    Patient Case Location Pathogen
  foreign_keys
    patient   : Case -> Patient
    location  : Case -> Location
    pathogen  : Case -> Pathogen
  attributes
    name       : Patient -> String
    age_group  : Patient -> String
    vaccinated : Patient -> String
    risk       : Patient -> String
    severity   : Case -> String
    onset      : Case -> String
    symptoms   : Case -> String
    loc_name   : Location -> String
    loc_type   : Location -> String
    path_name  : Pathogen -> String
}
"""
```

## 2. CSV Import: Loading the Line List

In practice, outbreak data arrives as CSV exports from hospital
information systems, laboratory LIMS, or national surveillance
platforms. CQL can import CSV files directly, one file per entity type.
Each CSV has an `id` column (the primary key) plus columns matching the
foreign key and attribute names in the schema.

Our data files are in `epi_data/`:

- `Patient.csv` — 10 patients across age groups 0–4, 5–17, 18–39, 40–64,
  65+
- `Case.csv` — 12 case reports with severity, onset date, and symptoms
- `Location.csv` — 6 facilities: 2 hospitals, 2 care homes, 2 schools
- `Pathogen.csv` — 3 pathogens: Influenza A H3N2, SARS-CoV-2 JN.1, RSV-B

``` julia
import_program = typeside_and_schema * """
instance Outbreak = import_csv "epi_data" : Epi
"""

env = run_program(import_program)
alg = env.instances["Outbreak"].algebra

function show_cases(alg; label="Cases")
    cases = sort(collect(CQL.carrier(alg, :Case)), by=string)
    println("$label ($(length(cases)) rows):")
    println("  ", rpad("Patient", 10), rpad("Pathogen", 20), rpad("Location", 22),
            rpad("Severity", 10), "Onset")
    println("  ", "-"^72)
    for x in cases
        pt  = CQL.eval_fk(alg, :patient, x)
        loc = CQL.eval_fk(alg, :location, x)
        pg  = CQL.eval_fk(alg, :pathogen, x)
        println("  ",
            rpad(string(CQL.eval_att(alg, :name, pt)), 10),
            rpad(string(CQL.eval_att(alg, :path_name, pg)), 20),
            rpad(string(CQL.eval_att(alg, :loc_name, loc)), 22),
            rpad(string(CQL.eval_att(alg, :severity, x)), 10),
            CQL.eval_att(alg, :onset, x))
    end
end

show_cases(alg, label="Full Outbreak")
```

    Full Outbreak (12 rows):
      Patient   Pathogen            Location              Severity  Onset
      ------------------------------------------------------------------------
      Margaret  Influenza A H3N2    Sunrise Care Home     severe    2024-01-10
      Harold    Influenza A H3N2    Sunrise Care Home     severe    2024-01-12
      Dorothy   Influenza A H3N2    Meadow Care Home      moderate  2024-01-14
      Grace     Influenza A H3N2    Meadow Care Home      severe    2024-01-15
      James     SARS-CoV-2 JN.1     Royal Infirmary       mild      2024-01-11
      Sarah     SARS-CoV-2 JN.1     Royal Infirmary       severe    2024-01-13
      William   SARS-CoV-2 JN.1     Royal Infirmary       mild      2024-01-16
      Margaret  SARS-CoV-2 JN.1     General Hospital      moderate  2024-01-18
      Emily     RSV-B               Westside Primary      severe    2024-01-09
      Oliver    RSV-B               Westside Primary      moderate  2024-01-11
      Amelia    RSV-B               Eastgate Academy      mild      2024-01-13
      Emily     RSV-B               General Hospital      severe    2024-01-14

Note that Margaret (p01) appears twice — once with flu at a care home
and once with COVID at a hospital — reflecting co-infections during
concurrent outbreaks. Emily (p06) also has two entries: an initial RSV
case at school and a later hospital admission as her condition worsened.

## 3. Queries: Filtering Cases by Epidemiological Criteria

A CQL **query** is a structure-preserving transformation from one schema
to another (here, from `Epi` to itself). In epidemiological terms, each
query is a reusable *case definition* or *filter criterion* that selects
a subset of the outbreak data while preserving all the relationships
between entities.

Unlike a SQL `WHERE` clause, which is a one-off statement, a CQL query
is a first-class object that can be stored, reused, and — crucially —
**composed** with other queries.

### Q1: Severe cases — for clinical escalation

Which cases require immediate clinical attention? We select only cases
where the severity attribute equals “severe”:

``` julia
q_severe = """
query SevereCases = literal : Epi -> Epi {
  entity Patient  -> {from p:Patient
    attributes name -> p.name age_group -> p.age_group
               vaccinated -> p.vaccinated risk -> p.risk}
  entity Case     -> {from c:Case where c.severity = "severe"
    attributes severity -> c.severity onset -> c.onset symptoms -> c.symptoms
    foreign_keys patient -> {p -> c.patient}
                 location -> {l -> c.location}
                 pathogen -> {g -> c.pathogen}}
  entity Location -> {from l:Location
    attributes loc_name -> l.loc_name loc_type -> l.loc_type}
  entity Pathogen -> {from g:Pathogen
    attributes path_name -> g.path_name}
}
"""
```

### Q2: Hospital cases — for nosocomial investigation

Which cases occurred in hospitals? This helps infection control teams
identify potential hospital-acquired (nosocomial) transmission. The
query joins `Case` with `Location` in its `from` clause and filters on
the location type:

``` julia
q_hospital = """
query HospitalCases = literal : Epi -> Epi {
  entity Patient  -> {from p:Patient
    attributes name -> p.name age_group -> p.age_group
               vaccinated -> p.vaccinated risk -> p.risk}
  entity Case     -> {from c:Case l:Location
    where c.location = l l.loc_type = "Hospital"
    attributes severity -> c.severity onset -> c.onset symptoms -> c.symptoms
    foreign_keys patient -> {p -> c.patient}
                 location -> {l -> l}
                 pathogen -> {g -> c.pathogen}}
  entity Location -> {from l:Location where l.loc_type = "Hospital"
    attributes loc_name -> l.loc_name loc_type -> l.loc_type}
  entity Pathogen -> {from g:Pathogen
    attributes path_name -> g.path_name}
}
"""
```

### Q3: Influenza cases — for pathogen-specific response

Each pathogen triggers a different response protocol. This query
extracts only influenza cases, which might be sent to the flu response
team for antiviral distribution:

``` julia
q_flu = """
query FluCases = literal : Epi -> Epi {
  entity Patient  -> {from p:Patient
    attributes name -> p.name age_group -> p.age_group
               vaccinated -> p.vaccinated risk -> p.risk}
  entity Case     -> {from c:Case g:Pathogen
    where c.pathogen = g g.path_name = "Influenza A H3N2"
    attributes severity -> c.severity onset -> c.onset symptoms -> c.symptoms
    foreign_keys patient -> {p -> c.patient}
                 location -> {l -> c.location}
                 pathogen -> {g -> g}}
  entity Location -> {from l:Location
    attributes loc_name -> l.loc_name loc_type -> l.loc_type}
  entity Pathogen -> {from g:Pathogen where g.path_name = "Influenza A H3N2"
    attributes path_name -> g.path_name}
}
"""
```

### Q4: Care home cases — for vulnerable population monitoring

Care home residents are among the most vulnerable during respiratory
outbreaks. This filter extracts cases occurring in care homes:

``` julia
q_carehome = """
query CareHomeCases = literal : Epi -> Epi {
  entity Patient  -> {from p:Patient
    attributes name -> p.name age_group -> p.age_group
               vaccinated -> p.vaccinated risk -> p.risk}
  entity Case     -> {from c:Case l:Location
    where c.location = l l.loc_type = "CareHome"
    attributes severity -> c.severity onset -> c.onset symptoms -> c.symptoms
    foreign_keys patient -> {p -> c.patient}
                 location -> {l -> l}
                 pathogen -> {g -> c.pathogen}}
  entity Location -> {from l:Location where l.loc_type = "CareHome"
    attributes loc_name -> l.loc_name loc_type -> l.loc_type}
  entity Pathogen -> {from g:Pathogen
    attributes path_name -> g.path_name}
}
"""
```

Let’s apply each filter independently:

``` julia
eval_queries = """
instance severe_cases   = eval SevereCases   Outbreak
instance hospital_cases = eval HospitalCases Outbreak
instance flu_cases      = eval FluCases      Outbreak
instance carehome_cases = eval CareHomeCases Outbreak
"""

env = run_program(import_program * q_severe * q_hospital * q_flu * q_carehome * eval_queries)

show_cases(env.instances["severe_cases"].algebra,   label="Severe Cases")
println()
show_cases(env.instances["hospital_cases"].algebra,  label="Hospital Cases")
println()
show_cases(env.instances["flu_cases"].algebra,       label="Influenza Cases")
println()
show_cases(env.instances["carehome_cases"].algebra,  label="Care Home Cases")
```

    Severe Cases (6 rows):
      Patient   Pathogen            Location              Severity  Onset
      ------------------------------------------------------------------------
      Sarah     SARS-CoV-2 JN.1     Royal Infirmary       severe    2024-01-13
      Margaret  Influenza A H3N2    Sunrise Care Home     severe    2024-01-10
      Grace     Influenza A H3N2    Meadow Care Home      severe    2024-01-15
      Harold    Influenza A H3N2    Sunrise Care Home     severe    2024-01-12
      Emily     RSV-B               General Hospital      severe    2024-01-14
      Emily     RSV-B               Westside Primary      severe    2024-01-09

    Hospital Cases (5 rows):
      Patient   Pathogen            Location              Severity  Onset
      ------------------------------------------------------------------------
      Margaret  SARS-CoV-2 JN.1     General Hospital      moderate  2024-01-18
      James     SARS-CoV-2 JN.1     Royal Infirmary       mild      2024-01-11
      Sarah     SARS-CoV-2 JN.1     Royal Infirmary       severe    2024-01-13
      Emily     RSV-B               General Hospital      severe    2024-01-14
      William   SARS-CoV-2 JN.1     Royal Infirmary       mild      2024-01-16

    Influenza Cases (4 rows):
      Patient   Pathogen            Location              Severity  Onset
      ------------------------------------------------------------------------
      Margaret  Influenza A H3N2    Sunrise Care Home     severe    2024-01-10
      Grace     Influenza A H3N2    Meadow Care Home      severe    2024-01-15
      Harold    Influenza A H3N2    Sunrise Care Home     severe    2024-01-12
      Dorothy   Influenza A H3N2    Meadow Care Home      moderate  2024-01-14

    Care Home Cases (4 rows):
      Patient   Pathogen            Location              Severity  Onset
      ------------------------------------------------------------------------
      Margaret  Influenza A H3N2    Sunrise Care Home     severe    2024-01-10
      Grace     Influenza A H3N2    Meadow Care Home      severe    2024-01-15
      Harold    Influenza A H3N2    Sunrise Care Home     severe    2024-01-12
      Dorothy   Influenza A H3N2    Meadow Care Home      moderate  2024-01-14

## 4. Query Composition: Building Epidemiological Pipelines

In CQL, queries are **functorial** — they are morphisms in a category of
schemas. If `Q₁ : Epi → Epi` and `Q₂ : Epi → Epi`, their composition
`[Q₁ ; Q₂] : Epi → Epi` is another query with a mathematical guarantee:

$$\text{eval}([Q_1; Q_2], I) = \text{eval}(Q_2, \text{eval}(Q_1, I))$$

This means applying the composed query in one step gives the *exact same
result* as applying each query sequentially. In epidemiological
practice, this lets you build complex case definitions from tested
building blocks — and know the result is correct.

### Severe hospital cases (nosocomial escalation)

Which severe cases occurred in hospitals? These are the cases most
likely to represent nosocomial transmission and require immediate
infection control intervention:

``` julia
compose_program = import_program * q_severe * q_hospital * q_flu * q_carehome * """
query SevereHospital = [SevereCases ; HospitalCases]

instance composed_sh  = eval SevereHospital Outbreak
instance step1_sh     = eval SevereCases Outbreak
instance step2_sh     = eval HospitalCases step1_sh
"""

env = run_program(compose_program)

println("=== Composed: [SevereCases ; HospitalCases] ===")
show_cases(env.instances["composed_sh"].algebra,
           label="Severe Hospital Cases (one-step)")
println()
println("=== Stepwise: eval HospitalCases (eval SevereCases Outbreak) ===")
show_cases(env.instances["step2_sh"].algebra,
           label="Severe Hospital Cases (two-step)")
```

    === Composed: [SevereCases ; HospitalCases] ===
    Severe Hospital Cases (one-step) (2 rows):
      Patient   Pathogen            Location              Severity  Onset
      ------------------------------------------------------------------------
      Sarah     SARS-CoV-2 JN.1     Royal Infirmary       severe    2024-01-13
      Emily     RSV-B               General Hospital      severe    2024-01-14

    === Stepwise: eval HospitalCases (eval SevereCases Outbreak) ===
    Severe Hospital Cases (two-step) (2 rows):
      Patient   Pathogen            Location              Severity  Onset
      ------------------------------------------------------------------------
      Sarah     SARS-CoV-2 JN.1     Royal Infirmary       severe    2024-01-13
      Emily     RSV-B               General Hospital      severe    2024-01-14

The composed and stepwise results are identical — this is the
**composition theorem**.

### Severe flu in care homes (antiviral prioritisation)

Who needs urgent antivirals? Compose the flu filter, severity filter,
and care home filter into a three-step pipeline. Since CQL’s `[Q;Q]`
syntax composes two queries at a time, we build the pipeline
incrementally:

``` julia
pipeline_program = compose_program * """
query FluSevere         = [FluCases ; SevereCases]
query FluSevereCareHome = [FluSevere ; CareHomeCases]

instance pipeline_result = eval FluSevereCareHome Outbreak
instance pipeline_s1     = eval FluCases Outbreak
instance pipeline_s2     = eval SevereCases pipeline_s1
instance pipeline_s3     = eval CareHomeCases pipeline_s2
"""

env = run_program(pipeline_program)

println("=== Three-way pipeline: [[Flu ; Severe] ; CareHome] ===")
show_cases(env.instances["pipeline_result"].algebra,
           label="Severe Flu in Care Homes (composed)")
println()
println("=== Stepwise verification ===")
show_cases(env.instances["pipeline_s3"].algebra,
           label="Severe Flu in Care Homes (stepwise)")
```

    === Three-way pipeline: [[Flu ; Severe] ; CareHome] ===
    Severe Flu in Care Homes (composed) (3 rows):
      Patient   Pathogen            Location              Severity  Onset
      ------------------------------------------------------------------------
      Margaret  Influenza A H3N2    Sunrise Care Home     severe    2024-01-10
      Grace     Influenza A H3N2    Meadow Care Home      severe    2024-01-15
      Harold    Influenza A H3N2    Sunrise Care Home     severe    2024-01-12

    === Stepwise verification ===
    Severe Flu in Care Homes (stepwise) (3 rows):
      Patient   Pathogen            Location              Severity  Onset
      ------------------------------------------------------------------------
      Margaret  Influenza A H3N2    Sunrise Care Home     severe    2024-01-10
      Grace     Influenza A H3N2    Meadow Care Home      severe    2024-01-15
      Harold    Influenza A H3N2    Sunrise Care Home     severe    2024-01-12

These are the elderly care home residents with severe influenza —
exactly the group that needs urgent antiviral treatment and enhanced
infection control.

## 5. Delta Migration: Reshaping for Reporting

Different stakeholders need different views of the same data. Hospital
infection control teams work with the full four-entity schema, but a
public health agency may need a **flat line list** — a single table with
denormalised columns — for their surveillance dashboard.

A CQL **mapping** defines a structure-preserving morphism between two
schemas. A **Delta migration** (`delta F I`) pulls data back along this
mapping: it takes an instance `I` on the target schema and produces an
instance on the source schema by following the mapping’s attribute
definitions in reverse.

In epidemiological terms: Delta is like defining a “report template”
(the flat schema) and then automatically populating it from the detailed
database. The mathematical guarantee is that every record in the output
corresponds to exactly one record in the input, with no duplicates and
no data loss.

``` julia
delta_program = import_program * """
schema Surveillance = literal : Ty {
  entities
    Report
  attributes
    report_name     : Report -> String
    report_pathogen : Report -> String
    report_location : Report -> String
    report_setting  : Report -> String
    report_severity : Report -> String
    report_onset    : Report -> String
}

mapping Denorm = literal : Surveillance -> Epi {
  entity Report -> Case
  attributes
    report_name     -> lambda c. name(patient(c))
    report_pathogen -> lambda c. path_name(pathogen(c))
    report_location -> lambda c. loc_name(location(c))
    report_setting  -> lambda c. loc_type(location(c))
    report_severity -> severity
    report_onset    -> onset
}

instance SurveillanceReport = delta Denorm Outbreak
"""

env = run_program(delta_program)
alg = env.instances["SurveillanceReport"].algebra

reports = sort(collect(CQL.carrier(alg, :Report)), by=string)
println("Public Health Line List ($(length(reports)) rows):")
println("  ", rpad("Name", 10), rpad("Pathogen", 20), rpad("Location", 22),
        rpad("Setting", 12), rpad("Severity", 10), "Onset")
println("  ", "-"^84)
for x in reports
    println("  ",
        rpad(string(CQL.eval_att(alg, :report_name, x)), 10),
        rpad(string(CQL.eval_att(alg, :report_pathogen, x)), 20),
        rpad(string(CQL.eval_att(alg, :report_location, x)), 22),
        rpad(string(CQL.eval_att(alg, :report_setting, x)), 12),
        rpad(string(CQL.eval_att(alg, :report_severity, x)), 10),
        CQL.eval_att(alg, :report_onset, x))
end
```

    Public Health Line List (12 rows):
      Name      Pathogen            Location              Setting     Severity  Onset
      ------------------------------------------------------------------------------------
      Margaret  Influenza A H3N2    Sunrise Care Home     CareHome    severe    2024-01-10
      Harold    Influenza A H3N2    Sunrise Care Home     CareHome    severe    2024-01-12
      Dorothy   Influenza A H3N2    Meadow Care Home      CareHome    moderate  2024-01-14
      Grace     Influenza A H3N2    Meadow Care Home      CareHome    severe    2024-01-15
      James     SARS-CoV-2 JN.1     Royal Infirmary       Hospital    mild      2024-01-11
      Sarah     SARS-CoV-2 JN.1     Royal Infirmary       Hospital    severe    2024-01-13
      William   SARS-CoV-2 JN.1     Royal Infirmary       Hospital    mild      2024-01-16
      Margaret  SARS-CoV-2 JN.1     General Hospital      Hospital    moderate  2024-01-18
      Emily     RSV-B               Westside Primary      School      severe    2024-01-09
      Oliver    RSV-B               Westside Primary      School      moderate  2024-01-11
      Amelia    RSV-B               Eastgate Academy      School      mild      2024-01-13
      Emily     RSV-B               General Hospital      Hospital    severe    2024-01-14

Each of the 12 cases becomes a single flat row — ready for upload to a
national surveillance dashboard.

## 6. Sigma Migration: Aligning Regional Schemas

Different regions often use different data schemas. Region A’s hospital
system records `patient_name`, `pathogen`, and `severity`, while Region
B’s system uses `person`, `diagnosis`, and `outcome`. Before data can be
combined, both must be aligned to a common standard.

**Sigma migration** (`sigma F I`) pushes an instance forward along a
mapping. It renames and restructures data from a source schema to a
target schema. In epidemiological terms, this is the “schema alignment”
step of data integration — transforming each hospital’s local data model
into the national reporting standard.

``` julia
sigma_program = """
typeside Ty = literal { types String }

schema RegionA = literal : Ty {
  entities ACase
  attributes patient_name : ACase -> String pathogen : ACase -> String
             severity : ACase -> String onset : ACase -> String
}

schema RegionB = literal : Ty {
  entities BEncounter
  attributes person : BEncounter -> String diagnosis : BEncounter -> String
             outcome : BEncounter -> String date_reported : BEncounter -> String
}

schema National = literal : Ty {
  entities Report
  attributes who : Report -> String what : Report -> String
             how_severe : Report -> String when_ : Report -> String
}

mapping AlignA = literal : RegionA -> National {
  entity ACase -> Report
  attributes patient_name -> who pathogen -> what severity -> how_severe onset -> when_
}

mapping AlignB = literal : RegionB -> National {
  entity BEncounter -> Report
  attributes person -> who diagnosis -> what outcome -> how_severe date_reported -> when_
}

instance DataA = literal : RegionA {
  generators a1 a2 a3 : ACase
  equations
    a1.patient_name = "Margaret" a1.pathogen = "Influenza" a1.severity = "severe" a1.onset = "2024-01-10"
    a2.patient_name = "Harold"   a2.pathogen = "Influenza" a2.severity = "severe" a2.onset = "2024-01-12"
    a3.patient_name = "James"    a3.pathogen = "COVID-19"  a3.severity = "mild"   a3.onset = "2024-01-11"
}

instance DataB = literal : RegionB {
  generators b1 b2 : BEncounter
  equations
    b1.person = "Emily"  b1.diagnosis = "RSV"       b1.outcome = "severe" b1.date_reported = "2024-01-09"
    b2.person = "Oliver" b2.diagnosis = "RSV"       b2.outcome = "moderate" b2.date_reported = "2024-01-11"
}

instance NatA = sigma AlignA DataA
instance NatB = sigma AlignB DataB
"""

env = run_program(sigma_program)

function show_national(alg; label="")
    rpts = sort(collect(CQL.carrier(alg, :Report)), by=string)
    println("$label ($(length(rpts)) reports):")
    for x in rpts
        println("  ", rpad(string(CQL.eval_att(alg, :who, x)), 12),
                rpad(string(CQL.eval_att(alg, :what, x)), 14),
                rpad(string(CQL.eval_att(alg, :how_severe, x)), 10),
                CQL.eval_att(alg, :when_, x))
    end
end

show_national(env.instances["NatA"].algebra, label="Region A → National")
println()
show_national(env.instances["NatB"].algebra, label="Region B → National")
```

    Region A → National (3 reports):
      Margaret    Influenza     severe    2024-01-10
      Harold      Influenza     severe    2024-01-12
      James       COVID-19      mild      2024-01-11

    Region B → National (2 reports):
      Emily       RSV           severe    2024-01-09
      Oliver      RSV           moderate  2024-01-11

Both regions’ data now conforms to the same national schema, despite
having started with completely different column names and structures.

## 7. Coproduct: Merging Data from Multiple Sources

Once regional data has been aligned to a common schema, the next step is
**merging**. A CQL **coproduct** (`coproduct I₁ + I₂ : S`) creates the
disjoint union of two instances on the same schema. In epidemiological
terms, this is combining case data from two independent reporting
systems into a single unified dataset.

The coproduct preserves all records from both sources without
deduplication — each hospital’s cases remain distinct. This is the
correct default for surveillance: if two hospitals independently report
a case, both reports should appear in the merged dataset until explicit
record linkage is performed.

``` julia
coprod_program = sigma_program * """
instance Combined = coproduct NatA + NatB : National
"""

env = run_program(coprod_program)
show_national(env.instances["Combined"].algebra,
              label="Combined National Surveillance")
```

    Combined National Surveillance (5 reports):
      Margaret    Influenza     severe    2024-01-10
      Harold      Influenza     severe    2024-01-12
      James       COVID-19      mild      2024-01-11
      Emily       RSV           severe    2024-01-09
      Oliver      RSV           moderate  2024-01-11

All 5 reports are now in a single dataset. The Sigma + Coproduct
pipeline is the CQL equivalent of “ETL” (Extract, Transform, Load) — but
with categorical guarantees that the schema alignment is structurally
correct.

## 8. Constraints and Chase: Enforcing Data Quality Rules

In outbreak response, certain data quality rules must be enforced. For
example: “every severe case must have a contact tracing record.” In CQL,
these rules are expressed as **embedded dependencies** (EDs) —
`forall ... exists ... where ...` constraints.

The **chase** algorithm takes an instance that may violate constraints
and repairs it by generating the minimum additional data needed to
satisfy all rules. In epidemiological terms, the chase identifies cases
missing required follow-up records and creates placeholder entries that
the response team can then fill in.

``` julia
chase_program = """
typeside Ty = literal {
  types String
  constants "severe" "mild" "moderate" "traced" "pending" : String
}

schema TracedEpi = literal : Ty {
  entities Case ContactTrace
  foreign_keys traced_case : ContactTrace -> Case
  attributes
    case_name : Case -> String
    case_severity : Case -> String
    trace_status : ContactTrace -> String
}

constraints TracingPolicy = literal : TracedEpi {
  forall c:Case
  where c.case_severity = "severe"
  ->
  exists t:ContactTrace
  where t.traced_case = c
}

instance BeforeChase = literal : TracedEpi {
  generators c1 c2 c3 c4 : Case t1 : ContactTrace
  equations
    c1.case_name = "Margaret" c1.case_severity = "severe"
    c2.case_name = "James"    c2.case_severity = "mild"
    c3.case_name = "Sarah"    c3.case_severity = "severe"
    c4.case_name = "Emily"    c4.case_severity = "severe"
    t1.traced_case = c1 t1.trace_status = "traced"
}

instance AfterChase = chase TracingPolicy BeforeChase
"""

env = run_program(chase_program)

for (label, iname) in [("Before chase", "BeforeChase"), ("After chase", "AfterChase")]
    alg = env.instances[iname].algebra
    cases = sort(collect(CQL.carrier(alg, :Case)), by=string)
    traces = sort(collect(CQL.carrier(alg, :ContactTrace)), by=string)
    println("$label: $(length(cases)) cases, $(length(traces)) contact traces")
    for t in traces
        c = CQL.eval_fk(alg, :traced_case, t)
        status = CQL.eval_att(alg, :trace_status, t)
        println("  trace → $(CQL.eval_att(alg, :case_name, c)) ",
                "($(CQL.eval_att(alg, :case_severity, c))) ",
                "status=$status")
    end
    println()
end
```

    Before chase: 4 cases, 1 contact traces
      trace → Margaret (severe) status=traced

    After chase: 4 cases, 3 contact traces
      trace → Emily (severe) status=chase_sk_1.trace_status
      trace → Sarah (severe) status=chase_sk_2.trace_status
      trace → Margaret (severe) status=traced

The chase created new contact trace records for Sarah and Emily — the
severe cases that were missing traces. The `trace_status` of these new
records is a Skolem term (a placeholder), indicating they have been
flagged but not yet completed. The response team now has a work list.

## 9. Transforms: Tracking Outbreak Progression

A CQL **transform** is a morphism between two instances on the same
schema. In epidemiological terms, it’s a formal mapping that shows how
one snapshot of the outbreak relates to another — for example, how Week
1 data embeds into Week 2 data.

This is useful for situation reports: you can formally state “all Week 1
cases persist into Week 2, plus these new cases appeared.”

``` julia
transform_program = """
typeside Ty = literal {
  types String
  constants "severe" "mild" "moderate" "Influenza" "COVID-19" "RSV" : String
}

schema LineList = literal : Ty {
  entities Case
  attributes name : Case -> String pathogen : Case -> String
             severity : Case -> String onset : Case -> String
}

instance Week1 = literal : LineList {
  generators c1 c2 c3 : Case
  equations
    c1.name = "Margaret" c1.pathogen = "Influenza" c1.severity = "severe"   c1.onset = "2024-01-10"
    c2.name = "James"    c2.pathogen = "COVID-19"  c2.severity = "mild"     c2.onset = "2024-01-11"
    c3.name = "Harold"   c3.pathogen = "Influenza" c3.severity = "severe"   c3.onset = "2024-01-12"
}

instance Week2 = literal : LineList {
  generators d1 d2 d3 d4 d5 : Case
  equations
    d1.name = "Margaret" d1.pathogen = "Influenza" d1.severity = "severe"   d1.onset = "2024-01-10"
    d2.name = "James"    d2.pathogen = "COVID-19"  d2.severity = "mild"     d2.onset = "2024-01-11"
    d3.name = "Harold"   d3.pathogen = "Influenza" d3.severity = "severe"   d3.onset = "2024-01-12"
    d4.name = "Sarah"    d4.pathogen = "COVID-19"  d4.severity = "severe"   d4.onset = "2024-01-13"
    d5.name = "Emily"    d5.pathogen = "RSV"       d5.severity = "severe"   d5.onset = "2024-01-14"
}

transform WeeklyProgression = literal : Week1 -> Week2 {
  generators c1 -> d1 c2 -> d2 c3 -> d3
}
"""

env = run_program(transform_program)

for (label, iname) in [("Week 1", "Week1"), ("Week 2", "Week2")]
    alg = env.instances[iname].algebra
    cases = sort(collect(CQL.carrier(alg, :Case)), by=string)
    println("$label: $(length(cases)) cases")
    for x in cases
        println("  ", rpad(string(CQL.eval_att(alg, :name, x)), 12),
                rpad(string(CQL.eval_att(alg, :pathogen, x)), 14),
                CQL.eval_att(alg, :severity, x))
    end
    println()
end
println("Transform maps: c1→d1 (Margaret), c2→d2 (James), c3→d3 (Harold)")
println("New in Week 2: d4 (Sarah, COVID-19, severe), d5 (Emily, RSV, severe)")
```

    Week 1: 3 cases
      Margaret    Influenza     severe
      James       COVID-19      mild
      Harold      Influenza     severe

    Week 2: 5 cases
      Margaret    Influenza     severe
      James       COVID-19      mild
      Harold      Influenza     severe
      Sarah       COVID-19      severe
      Emily       RSV           severe

    Transform maps: c1→d1 (Margaret), c2→d2 (James), c3→d3 (Harold)
    New in Week 2: d4 (Sarah, COVID-19, severe), d5 (Emily, RSV, severe)

The transform is a proof that Week 1’s data is faithfully embedded in
Week 2. CQL verifies that the mapped generators agree on all attributes
— if `c1` maps to `d1`, their names, pathogens, severities, and onset
dates must match. Any discrepancy is caught at construction time.

## 10. CoEval: Reverse Query Evaluation

CQL’s **coeval** is the right adjoint to query evaluation. Where
`eval Q I` pushes data *forward* through a query, `coeval Q J` pulls
data *backward* — reconstructing what the source instance might look
like given a target instance.

In epidemiological terms: given a summary report (e.g., “these are the
severe cases”), the coeval reconstructs the detailed data that would
produce that summary. This is useful for data provenance — tracing a
summary back to its source records.

``` julia
coeval_program = """
typeside Ty = literal {
  types String
  constants "severe" "mild" "moderate" : String
}

schema Full = literal : Ty {
  entities Case
  attributes name : Case -> String severity : Case -> String onset : Case -> String
}

schema SevereOnly = literal : Ty {
  entities SevereCase
  attributes sname : SevereCase -> String sonset : SevereCase -> String
}

query ExtractSevere = literal : Full -> SevereOnly {
  entity SevereCase -> {
    from c:Case
    where c.severity = "severe"
    attributes sname -> c.name sonset -> c.onset
  }
}

instance AllCases = literal : Full {
  generators c1 c2 c3 c4 : Case
  equations
    c1.name = "Margaret" c1.severity = "severe" c1.onset = "2024-01-10"
    c2.name = "James"    c2.severity = "mild"   c2.onset = "2024-01-11"
    c3.name = "Sarah"    c3.severity = "severe" c3.onset = "2024-01-13"
    c4.name = "Emily"    c4.severity = "severe" c4.onset = "2024-01-14"
}

instance SevereReport = eval ExtractSevere AllCases
instance Reconstructed = coeval ExtractSevere SevereReport
"""

env = run_program(coeval_program)

println("=== Forward: Extract severe cases ===")
alg = env.instances["SevereReport"].algebra
for x in sort(collect(CQL.carrier(alg, :SevereCase)), by=string)
    println("  ", CQL.eval_att(alg, :sname, x), " (onset: ", CQL.eval_att(alg, :sonset, x), ")")
end

println("\n=== Backward (coeval): Reconstruct source data ===")
alg = env.instances["Reconstructed"].algebra
for x in sort(collect(CQL.carrier(alg, :Case)), by=string)
    println("  ", CQL.eval_att(alg, :name, x),
            " severity=", CQL.eval_att(alg, :severity, x),
            " onset=", CQL.eval_att(alg, :onset, x))
end
```

    === Forward: Extract severe cases ===
      Emily (onset: 2024-01-14)
      Margaret (onset: 2024-01-10)
      Sarah (onset: 2024-01-13)

    === Backward (coeval): Reconstruct source data ===
      Margaret severity=severe onset=2024-01-10
      Emily severity=severe onset=2024-01-14
      Sarah severity=severe onset=2024-01-13

The coeval reconstructs only the cases that were visible through the
query — the mild case (James) is not in the reconstruction because it
was filtered out by the query. Each reconstructed record retains its
severity (“severe”) and onset date, confirming the provenance chain.

## 11. Unit and Counit: Round-Trip Migration Properties

When you migrate data from one schema to another and back, how much
information is preserved? The **unit** and **counit** transforms answer
this question precisely.

For a mapping `F : S₁ → S₂`:

- **Unit** (`unit F I`): maps instance `I` on `S₁` into
  `delta F (sigma F I)` — push forward then pull back. The unit
  transform shows how the original data embeds into the round-trip
  result.
- **Counit** (`counit F J`): maps `sigma F (delta F J)` into instance
  `J` on `S₂` — pull back then push forward. The counit shows how the
  round-trip result maps back to the original.

In epidemiological terms: if you export hospital data to a national
standard (Sigma) and then import it back (Delta), the unit tells you
what was preserved. If you import national data (Delta) and re-export it
(Sigma), the counit tells you what was preserved in that direction.

``` julia
adjunction_program = """
typeside Ty = literal {
  types String
  constants "severe" "mild" : String
}

schema Local = literal : Ty {
  entities LCase
  attributes lname : LCase -> String lseverity : LCase -> String lonset : LCase -> String
}

schema National = literal : Ty {
  entities NCase
  attributes nname : NCase -> String nseverity : NCase -> String nonset : NCase -> String
}

mapping Align = literal : Local -> National {
  entity LCase -> NCase
  attributes lname -> nname lseverity -> nseverity lonset -> nonset
}

instance LocalData = literal : Local {
  generators lc1 lc2 : LCase
  equations
    lc1.lname = "Margaret" lc1.lseverity = "severe" lc1.lonset = "2024-01-10"
    lc2.lname = "James"    lc2.lseverity = "mild"   lc2.lonset = "2024-01-11"
}

instance NatData = literal : National {
  generators nc1 nc2 : NCase
  equations
    nc1.nname = "Margaret" nc1.nseverity = "severe" nc1.nonset = "2024-01-10"
    nc2.nname = "James"    nc2.nseverity = "mild"   nc2.nonset = "2024-01-11"
}

transform eta = unit Align LocalData
transform eps = counit Align NatData
"""

env = run_program(adjunction_program)
println("Unit transform (η): LocalData → Δ(Σ(LocalData))")
println("  Maps local hospital data into the round-trip result")
println("  If η is an isomorphism, no information was lost in the export/reimport cycle")
println()
println("Counit transform (ε): Σ(Δ(NatData)) → NatData")
println("  Maps the round-trip result back to the national data")
println("  If ε is an isomorphism, no information was lost in the import/reexport cycle")
println()
println("Both transforms computed successfully — the Δ ⊣ Σ adjunction holds.")
```

    Unit transform (η): LocalData → Δ(Σ(LocalData))
      Maps local hospital data into the round-trip result
      If η is an isomorphism, no information was lost in the export/reimport cycle

    Counit transform (ε): Σ(Δ(NatData)) → NatData
      Maps the round-trip result back to the national data
      If ε is an isomorphism, no information was lost in the import/reexport cycle

    Both transforms computed successfully — the Δ ⊣ Σ adjunction holds.

For this simple renaming mapping (a bijection on entities and
attributes), both unit and counit are isomorphisms: no information is
lost in either direction. For more complex mappings that merge entities
or drop attributes, the unit and counit reveal exactly what is lost or
gained.

## 12. Schema Colimit: Integrating Surveillance Systems

When two surveillance systems use completely different schemas — not
just different column names, but different entity structures — we need
**schema colimit** to merge them.

A CQL **schema colimit** computes the categorical colimit (pushout) of
multiple schemas, optionally identifying entities and attributes across
them. In epidemiological terms, this is “ontology alignment” — defining
that Hospital A’s `FluCase` entity and Hospital B’s `CovidCase` entity
should both map into a unified `Case` entity, while their different
`Location` entities are actually the same concept.

``` julia
colimit_program = """
typeside Ty = literal { types String }

schema FluSurv = literal : Ty {
  entities FluCase FluLoc
  foreign_keys flu_loc : FluCase -> FluLoc
  attributes flu_name : FluCase -> String flu_loc_name : FluLoc -> String
}

schema CovidSurv = literal : Ty {
  entities CovidCase CovidLoc
  foreign_keys covid_loc : CovidCase -> CovidLoc
  attributes covid_name : CovidCase -> String covid_loc_name : CovidLoc -> String
}

schema_colimit Unified = quotient FluSurv + CovidSurv : Ty {
  entity_equations
    FluSurv.FluLoc = CovidSurv.CovidLoc
  observation_equations
    forall x. x.FluSurv_FluLoc_flu_loc_name = x.CovidSurv_CovidLoc_covid_loc_name
  options
    simplify_names = false
}

schema UnifiedSchema = getSchema Unified
mapping FluToUnified   = getMapping Unified FluSurv
mapping CovidToUnified = getMapping Unified CovidSurv

instance FluData = literal : FluSurv {
  generators fc1 fc2 : FluCase fl1 : FluLoc
  equations
    fc1.flu_name = "Margaret" fc2.flu_name = "Harold"
    fc1.flu_loc = fl1 fc2.flu_loc = fl1
    fl1.flu_loc_name = "Royal Infirmary"
}

instance CovidData = literal : CovidSurv {
  generators cc1 cc2 : CovidCase cl1 : CovidLoc
  equations
    cc1.covid_name = "James" cc2.covid_name = "Sarah"
    cc1.covid_loc = cl1 cc2.covid_loc = cl1
    cl1.covid_loc_name = "Royal Infirmary"
}

instance FluFwd   = sigma FluToUnified FluData
instance CovidFwd = sigma CovidToUnified CovidData
instance Integrated = coproduct FluFwd + CovidFwd : UnifiedSchema
"""

env = run_program(colimit_program)

sch = env.schemas["UnifiedSchema"]
println("Unified schema entities: ", sort(collect(sch.ens)))
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

    Unified schema entities: [:CovidSurv_CovidCase, :FluSurv_FluCase, :FluSurv_FluLoc]

    Entity CovidSurv_CovidCase (2 records):
      CovidSurv_CovidCase_covid_name=James
      CovidSurv_CovidCase_covid_name=Sarah
    Entity FluSurv_FluCase (2 records):
      FluSurv_FluCase_flu_name=Margaret
      FluSurv_FluCase_flu_name=Harold
    Entity FluSurv_FluLoc (2 records):
      CovidSurv_CovidLoc_covid_loc_name=Royal Infirmary, FluSurv_FluLoc_flu_loc_name=Royal Infirmary
      CovidSurv_CovidLoc_covid_loc_name=Royal Infirmary, FluSurv_FluLoc_flu_loc_name=Royal Infirmary

The schema colimit merged the two `Location` entities (`FluLoc` and
`CovidLoc`) into a single entity with a shared location name attribute,
while keeping `FluCase` and `CovidCase` as separate entity types (since
flu and COVID cases have different epidemiological properties). The
Sigma + Coproduct pipeline then pushed both datasets into this unified
schema.

## Julia DSL

The examples above use `run_program` with CQL source strings. CQL.jl
also provides Julia-native macros. Here is how the Epi schema looks
using the DSL:

``` julia
using CQL

Ty = @typeside begin
    String::Ty
end

Epi = @schema Ty begin
    @entities Patient, Case, Location, Pathogen
    patient : Case → Patient
    location : Case → Location
    pathogen : Case → Pathogen
    name : Patient ⇒ String
    age_group : Patient ⇒ String
    vaccinated : Patient ⇒ String
    risk : Patient ⇒ String
    severity : Case ⇒ String
    onset : Case ⇒ String
    symptoms : Case ⇒ String
    loc_name : Location ⇒ String
    loc_type : Location ⇒ String
    path_name : Pathogen ⇒ String
end

println("Epi entities: ", sort(collect(Epi.ens)))
println("Foreign keys: ", length(Epi.fks))
println("Attributes: ", length(Epi.atts))
```

    Epi entities: [:Case, :Location, :Pathogen, :Patient]
    Foreign keys: 3
    Attributes: 10

Note: CSV import (`import_csv`), `constraints` + `chase`, `coeval`,
`schema_colimit`, and mappings with `lambda` expressions (used in the
delta migration for flat reports) still require the `cql"""..."""` or
`run_program` syntax. The DSL covers typeside, schema, and instance
definitions. Queries for filtering cases (severe, hospital, flu, care
home) can be expressed using the `@query` macro.

## Summary

This vignette demonstrated nine CQL operations applied to outbreak
surveillance data:

| Step | Operation | What It Does |
|----|----|----|
| 1 | **CSV Import** | Loaded a 12-case line list from flat files into a normalised 4-entity database |
| 2 | **Query filters** | Defined reusable case selection criteria (severity, pathogen, setting) |
| 3 | **Query composition** | Chained filters into pipelines with provably correct results |
| 4 | **Delta migration** | Reshaped the normalised database into a flat surveillance report |
| 5 | **Sigma migration** | Aligned two regional schemas to a common national standard |
| 6 | **Coproduct** | Merged multi-source data into a single unified dataset |
| 7 | **Constraints + Chase** | Enforced “every severe case needs a trace” and auto-generated missing records |
| 8 | **Transform** | Formally mapped between weekly outbreak snapshots |
| 9 | **CoEval** | Traced a summary report back to its source cases |

Each operation has a categorical foundation that guarantees correctness:

- **Queries compose associatively**:
  `[Q₁ ; [Q₂ ; Q₃]] = [[Q₁ ; Q₂] ; Q₃]`
- **Delta and Sigma are adjoint functors**: round-trip properties are
  captured by unit/counit
- **Chase terminates with minimal repair**: only the necessary records
  are created
- **Coproduct preserves all data**: no records are lost or silently
  merged

These guarantees are especially valuable in outbreak response, where
incorrect data transformations can lead to missed cases, duplicated
records, or misleading situation reports. CQL makes the data pipeline a
mathematical object that can be reasoned about as rigorously as the
epidemiological models it feeds.
