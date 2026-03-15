# Algebraic Property Graphs
Simon Frost

## Introduction

Property graphs — as used by Neo4j, Amazon Neptune, and similar
databases — represent data as vertices and edges, each carrying labels
and key-value properties. They are flexible and intuitive, but lack a
rigorous notion of **schema**: there is no systematic way to specify
what labels exist, what properties they carry, or how edges connect to
vertices. Without this, there are no formal guarantees about data
integrity, and no principled way to transform data between schemas.

**Algebraic Property Graphs** (APGs), introduced by [Wisnesky, Breiner,
Jones, Spivak, and Vasilakopoulou
(2019)](https://arxiv.org/abs/1909.04881), solve this by giving property
graphs a foundation in type theory and category theory. Each label
receives an **algebraic type** built from products (tuples), coproducts
(tagged unions), base types (primitives), and label references (foreign
keys). This type assignment forms the **schema**, and instances must
conform to it.

The framework originated from a data integration toolkit at Uber
(Dragon) that carries data and schemas along composable mappings between
interchange formats like Apache Avro, Thrift, and Protocol Buffers.

This vignette demonstrates how APG concepts map naturally to CQL.jl:

| APG Concept | CQL Encoding |
|----|----|
| Label with unit type `()` | Entity (no attributes) |
| Label with `base T` | Entity with one attribute of type `T` |
| Label with `label X` in product | Foreign key to entity `X` |
| Label with product type | Entity with multiple FKs and attributes |
| APG instance element | Generator in CQL instance |
| APG morphism | CQL transform or mapping |
| Coequalizer | Sigma data migration or generator equations |

``` julia
using CQL
```

## APG Label Types

An APG schema assigns each label an **algebraic type** from the grammar:

$$\tau ::= () \mid T \mid \ell \mid \tau_1 \times \tau_2 \mid \tau_1 + \tau_2$$

where $()$ is the unit type, $T$ is a base type (like `Str` or `Nat`),
$\ell$ is a reference to another label, $\times$ is a product (tuple),
and $+$ is a coproduct (tagged union).

The simplest label types — units, base types, label references, and
products of these — map directly to CQL’s entities, attributes, and
foreign keys. We demonstrate each in turn.

### Unit Labels: Vertices

A label with unit type `()` is a vertex type — an entity with no data of
its own:

    APG:    User -> ()           Trip -> ()
    CQL:    entities  User  Trip

``` julia
env = cql"""
typeside Ty = literal {
    types Str
}

schema VertexSch = literal : Ty {
    entities
        User
        Trip
}

instance Vertices = literal : VertexSch {
    generators
        u1 : User
        t1 : Trip
}
"""

alg = env.Vertices.algebra
println("Users: ", length(carrier(alg, :User)), "  Trips: ", length(carrier(alg, :Trip)))
```

    Users: 1  Trips: 1

Each generator corresponds to an APG element. The label type `()`
carries no data — only identity.

### Base Labels: Typed Values

A label with a base type represents a typed atomic value:

    APG:    UnixTime -> base Nat
    CQL:    entity UnixTime   attributes time_val : UnixTime -> Nat

``` julia
env = cql"""
typeside Ty = literal {
    types
        Nat
    constants
        v1 v3 v4 : Nat
}

schema TimeSch = literal : Ty {
    entities
        UnixTime
    attributes
        time_val : UnixTime -> Nat
}

instance Times = literal : TimeSch {
    generators
        s1 s2 s3 : UnixTime
    equations
        time_val(s1) = v1
        time_val(s2) = v4
        time_val(s3) = v3
}
"""

alg = env.Times.algebra
for x in carrier(alg, :UnixTime)
    println("  ", repr_x(alg, x), " = ", eval_att(alg, :time_val, x))
end
```

      s1 = v1
      s3 = v3
      s2 = v4

### Product Labels: Structured Records

A label with a product type `(a: label X * b: base T)` becomes an entity
with a foreign key and an attribute:

    APG:    UserName -> (user: label User * name: base Str)
    CQL:    entity UserName
            foreign_keys  name_user  : UserName -> User
            attributes    name_value : UserName -> Str

This is the **reified property** pattern: each name is its own element,
linked to a user. Unlike a simple `name : User -> Str` attribute, this
allows **multiple names per user**:

``` julia
env = cql"""
typeside Ty = literal {
    types
        Str
    constants
        Arthur ArthurPDent : Str
}

schema PropertySch = literal : Ty {
    entities
        User
        UserName
    foreign_keys
        name_user : UserName -> User
    attributes
        name_value : UserName -> Str
}

instance Properties = literal : PropertySch {
    generators
        u1 : User
        n1 n2 : UserName
    equations
        name_user(n1) = u1   name_value(n1) = Arthur
        name_user(n2) = u1   name_value(n2) = ArthurPDent
}
"""

alg = env.Properties.algebra
println("User u1 has ", length(carrier(alg, :UserName)), " names:")
for x in carrier(alg, :UserName)
    println("  ", eval_att(alg, :name_value, x))
end
```

    User u1 has 2 names:
      Arthur
      ArthurPDent

This is a key feature of the APG model: properties are **elements**, not
just attributes. A user can have multiple names, multiple addresses, or
multiple phone numbers — each is a separate element with its own
identity.

### Edge Labels: Relationships

An edge label is a product of label references. The APG label
`Driver -> (trip: label Trip * user: label User)` becomes an entity with
two foreign keys:

``` julia
env = cql"""
typeside Ty = literal {
    types Str
}

schema EdgeSch = literal : Ty {
    entities
        User
        Trip
        Driver
        Rider
    foreign_keys
        driver_trip : Driver -> Trip
        driver_user : Driver -> User
        rider_trip  : Rider -> Trip
        rider_user  : Rider -> User
}

instance Edges = literal : EdgeSch {
    generators
        u1 u2 : User
        t1 : Trip
        d1 : Driver
        r1 : Rider
    equations
        driver_trip(d1) = t1  driver_user(d1) = u1
        rider_trip(r1)  = t1  rider_user(r1)  = u2
}
"""

alg = env.Edges.algebra
for x in carrier(alg, :Driver)
    t = eval_fk(alg, :driver_trip, x)
    u = eval_fk(alg, :driver_user, x)
    println("Driver ", repr_x(alg, x), ": drives trip ", repr_x(alg, t),
            " for user ", repr_x(alg, u))
end
for x in carrier(alg, :Rider)
    t = eval_fk(alg, :rider_trip, x)
    u = eval_fk(alg, :rider_user, x)
    println("Rider  ", repr_x(alg, x), ": rides trip ", repr_x(alg, t),
            " as user ", repr_x(alg, u))
end
```

    Driver d1: drives trip r1.rider_trip for user u1
    Rider  r1: rides trip r1.rider_trip as user u2

Each edge element is a first-class object with its own identity, linked
to its endpoints by foreign keys.

## A Ride-Sharing APG

Combining all the label types, we build a complete ride-sharing graph
inspired by the APG paper’s Uber example. The APG schema in
type-theoretic notation:

    User       -> ()
    Trip       -> (user1: label User * user2: label User)
    Place      -> ()
    PlaceEvent -> (place: label Place * time: base Nat)
    Driver     -> (trip: label Trip * user: label User)
    Rider      -> (trip: label Trip * user: label User)
    UserName   -> (user: label User * name: base Str)

In CQL:

``` julia
env = cql"""
typeside Ty = literal {
    types
        Str
        Nat
    constants
        Arthur Zaphod Ford : Str
        v1 v3 v4 : Nat
}

schema RideShare = literal : Ty {
    entities
        User
        Trip
        Place
        PlaceEvent
        Driver
        Rider
        UserName
    foreign_keys
        trip_user1  : Trip -> User
        trip_user2  : Trip -> User
        event_place : PlaceEvent -> Place
        driver_trip : Driver -> Trip
        driver_user : Driver -> User
        rider_trip  : Rider -> Trip
        rider_user  : Rider -> User
        name_user   : UserName -> User
    attributes
        event_time : PlaceEvent -> Nat
        name_value : UserName   -> Str
}
"""

sch = env.RideShare
println("Entities: ", sch.ens)
println("Foreign keys: ", length(sch.fks))
println("Attributes: ", length(sch.atts))
```

    Entities: Set([:User, :Place, :Rider, :UserName, :PlaceEvent, :Trip, :Driver])
    Foreign keys: 8
    Attributes: 2

### Populating the Graph

``` julia
env = cql"""
typeside Ty = literal {
    types
        Str
        Nat
    constants
        Arthur Zaphod Ford : Str
        v1 v3 v4 : Nat
}

schema RideShare = literal : Ty {
    entities
        User
        Trip
        Place
        PlaceEvent
        Driver
        Rider
        UserName
    foreign_keys
        trip_user1  : Trip -> User
        trip_user2  : Trip -> User
        event_place : PlaceEvent -> Place
        driver_trip : Driver -> Trip
        driver_user : Driver -> User
        rider_trip  : Rider -> Trip
        rider_user  : Rider -> User
        name_user   : UserName -> User
    attributes
        event_time : PlaceEvent -> Nat
        name_value : UserName   -> Str
}

instance UberData = literal : RideShare {
    generators
        u1 u2 u3 : User
        t1 t2 : Trip
        p1 p2 p3 : Place
        e1 e2 e3 e4 : PlaceEvent
        d1 d2 : Driver
        r1 r2 : Rider
        n1 n2 n3 : UserName
    equations
        trip_user1(t1) = u1   trip_user2(t1) = u2
        trip_user1(t2) = u1   trip_user2(t2) = u3

        event_place(e1) = p1  event_time(e1) = v1
        event_place(e2) = p2  event_time(e2) = v1
        event_place(e3) = p2  event_time(e3) = v4
        event_place(e4) = p3  event_time(e4) = v3

        driver_trip(d1) = t1  driver_user(d1) = u1
        driver_trip(d2) = t2  driver_user(d2) = u1
        rider_trip(r1)  = t1  rider_user(r1)  = u2
        rider_trip(r2)  = t2  rider_user(r2)  = u3

        name_user(n1) = u1    name_value(n1) = Arthur
        name_user(n2) = u2    name_value(n2) = Zaphod
        name_user(n3) = u3    name_value(n3) = Ford
}
"""

alg = env.UberData.algebra

println("=== Ride-Sharing Graph ===\n")

# Helper: look up user name
function user_name(alg, u)
    for n in carrier(alg, :UserName)
        if eval_fk(alg, :name_user, n) == u
            return string(eval_att(alg, :name_value, n))
        end
    end
    return string(repr_x(alg, u))
end

println("Trips:")
for x in carrier(alg, :Trip)
    u1 = eval_fk(alg, :trip_user1, x)
    u2 = eval_fk(alg, :trip_user2, x)
    println("  ", repr_x(alg, x), ": ", user_name(alg, u1), " → ", user_name(alg, u2))
end

println("\nDriver/Rider assignments:")
for d in carrier(alg, :Driver)
    t = eval_fk(alg, :driver_trip, d)
    u = eval_fk(alg, :driver_user, d)
    println("  Driver: ", user_name(alg, u), " on trip ", repr_x(alg, t))
end
for r in carrier(alg, :Rider)
    t = eval_fk(alg, :rider_trip, r)
    u = eval_fk(alg, :rider_user, r)
    println("  Rider:  ", user_name(alg, u), " on trip ", repr_x(alg, t))
end

println("\nPlace events:")
for x in carrier(alg, :PlaceEvent)
    p = eval_fk(alg, :event_place, x)
    t = eval_att(alg, :event_time, x)
    println("  ", repr_x(alg, x), ": place=", repr_x(alg, p), " time=", t)
end
```

    === Ride-Sharing Graph ===

    Trips:
      r1.rider_trip: Arthur → Zaphod
      r2.rider_trip: Arthur → Ford

    Driver/Rider assignments:
      Driver: Arthur on trip r2.rider_trip
      Driver: Arthur on trip r1.rider_trip
      Rider:  Ford on trip r2.rider_trip
      Rider:  Zaphod on trip r1.rider_trip

    Place events:
      e1: place=p1 time=v1
      e2: place=p2 time=v1
      e4: place=p3 time=v3
      e3: place=p2 time=v4

The graph has 3 users (Arthur, Zaphod, Ford), 2 trips, 3 places, 4 place
events, 2 driver assignments, and 2 rider assignments. Every element is
typed and every relationship is navigable through foreign keys.

## Querying an APG

One advantage of the APG framework is that queries have categorical
semantics. In CQL, we express APG queries as **uber-flower** queries
that traverse the graph structure.

### Flattening Driver-Rider Pairs

This query computes all driver-rider pairs on the same trip, resolving
names by navigating foreign keys:

``` julia
env = cql"""
typeside Ty = literal {
    types
        Str
        Nat
    constants
        Arthur Zaphod Ford : Str
        v1 v3 v4 : Nat
}

schema RideShare = literal : Ty {
    entities
        User
        Trip
        Place
        PlaceEvent
        Driver
        Rider
        UserName
    foreign_keys
        trip_user1  : Trip -> User
        trip_user2  : Trip -> User
        event_place : PlaceEvent -> Place
        driver_trip : Driver -> Trip
        driver_user : Driver -> User
        rider_trip  : Rider -> Trip
        rider_user  : Rider -> User
        name_user   : UserName -> User
    attributes
        event_time : PlaceEvent -> Nat
        name_value : UserName   -> Str
}

schema DriverRiderReport = literal : Ty {
    entities
        Row
    attributes
        driver_name : Row -> Str
        rider_name  : Row -> Str
}

query FlattenTrips = literal : RideShare -> DriverRiderReport {
    entity Row -> {
        from
            d  : Driver
            r  : Rider
            dn : UserName
            rn : UserName
        where
            d.driver_trip = r.rider_trip
            dn.name_user  = d.driver_user
            rn.name_user  = r.rider_user
        attributes
            driver_name -> dn.name_value
            rider_name  -> rn.name_value
    }
}

instance UberData = literal : RideShare {
    generators
        u1 u2 u3 : User
        t1 t2 : Trip
        p1 p2 p3 : Place
        e1 e2 e3 e4 : PlaceEvent
        d1 d2 : Driver
        r1 r2 : Rider
        n1 n2 n3 : UserName
    equations
        trip_user1(t1) = u1   trip_user2(t1) = u2
        trip_user1(t2) = u1   trip_user2(t2) = u3
        event_place(e1) = p1  event_time(e1) = v1
        event_place(e2) = p2  event_time(e2) = v1
        event_place(e3) = p2  event_time(e3) = v4
        event_place(e4) = p3  event_time(e4) = v3
        driver_trip(d1) = t1  driver_user(d1) = u1
        driver_trip(d2) = t2  driver_user(d2) = u1
        rider_trip(r1)  = t1  rider_user(r1)  = u2
        rider_trip(r2)  = t2  rider_user(r2)  = u3
        name_user(n1) = u1    name_value(n1) = Arthur
        name_user(n2) = u2    name_value(n2) = Zaphod
        name_user(n3) = u3    name_value(n3) = Ford
}

instance Report = eval FlattenTrips UberData
"""

alg = env.Report.algebra
println("Driver-Rider pairs on the same trip:\n")
println(rpad("Driver", 10), "| Rider")
println("-"^10, "+", "-"^10)
for x in carrier(alg, :Row)
    dn = eval_att(alg, :driver_name, x)
    rn = eval_att(alg, :rider_name, x)
    println(rpad(string(dn), 10), "| ", rn)
end
```

    Driver-Rider pairs on the same trip:

    Driver    | Rider
    ----------+----------
    Arthur    | Ford
    Arthur    | Zaphod

The query binds four variables (`d`, `r`, `dn`, `rn`), constrains
drivers and riders to the same trip and matches each to their name
element, then projects the name values. In SQL this would require four
joins; in CQL it’s a single from-where-attributes block.

## Coequalizers: Deduplicating Records

APGs support **coequalizers** — a categorical construction that merges
elements identified by two morphisms. In data integration, this is
record deduplication: when two sources contain overlapping data, the
coequalizer computes the quotient.

### The Plate Number Problem

Consider license plates from two sources that partially overlap:

``` julia
env = cql"""
typeside Ty = literal {
    types
        Str
    constants
        US MX CA BC SN v6trj244 ahd4102 vuk1775 : Str
}

schema PlateSch = literal : Ty {
    entities
        PlateNumber
    attributes
        plate_id  : PlateNumber -> Str
        region_id : PlateNumber -> Str
        region_lp : PlateNumber -> Str
}

instance Plates = literal : PlateSch {
    generators
        p1 p2 q1 q2 : PlateNumber
    equations
        plate_id(p1) = US  region_id(p1) = CA  region_lp(p1) = v6trj244
        plate_id(p2) = MX  region_id(p2) = BC  region_lp(p2) = ahd4102
        plate_id(q1) = US  region_id(q1) = CA  region_lp(q1) = v6trj244
        plate_id(q2) = MX  region_id(q2) = SN  region_lp(q2) = vuk1775
}
"""

alg = env.Plates.algebra
println("Before deduplication: ", length(carrier(alg, :PlateNumber)), " plates\n")
for x in carrier(alg, :PlateNumber)
    pid = eval_att(alg, :plate_id, x)
    rid = eval_att(alg, :region_id, x)
    rlp = eval_att(alg, :region_lp, x)
    println("  ", repr_x(alg, x), ": ", pid, "/", rid, "/", rlp)
end
```

    Before deduplication: 4 plates

      q2: MX/SN/vuk1775
      p1: US/CA/v6trj244
      q1: US/CA/v6trj244
      p2: MX/BC/ahd4102

Plates `p1` and `q1` are the same real-world plate (US/CA/6trj244) from
different sources.

### Direct Coequalizer via Equations

The simplest encoding: add the equation `p1 = q1` to merge duplicates:

``` julia
env = cql"""
typeside Ty = literal {
    types
        Str
    constants
        US MX CA BC SN v6trj244 ahd4102 vuk1775 : Str
}

schema PlateSch = literal : Ty {
    entities
        PlateNumber
    attributes
        plate_id  : PlateNumber -> Str
        region_id : PlateNumber -> Str
        region_lp : PlateNumber -> Str
}

instance MergedPlates = literal : PlateSch {
    generators
        p1 p2 q1 q2 : PlateNumber
    equations
        plate_id(p1) = US  region_id(p1) = CA  region_lp(p1) = v6trj244
        plate_id(p2) = MX  region_id(p2) = BC  region_lp(p2) = ahd4102
        plate_id(q1) = US  region_id(q1) = CA  region_lp(q1) = v6trj244
        plate_id(q2) = MX  region_id(q2) = SN  region_lp(q2) = vuk1775
        p1 = q1
}
"""

alg = env.MergedPlates.algebra
println("After coequalizer (p1 = q1): ", length(carrier(alg, :PlateNumber)), " plates\n")
for x in carrier(alg, :PlateNumber)
    pid = eval_att(alg, :plate_id, x)
    rid = eval_att(alg, :region_id, x)
    rlp = eval_att(alg, :region_lp, x)
    println("  ", repr_x(alg, x), ": ", pid, "/", rid, "/", rlp)
end
```

    After coequalizer (p1 = q1): 3 plates

      q2: MX/SN/vuk1775
      p1: US/CA/v6trj244
      p2: MX/BC/ahd4102

CQL’s theorem prover automatically computes the equivalence class: `p1`
and `q1` merge into a single element, reducing 4 plates to 3.

### Sigma-Based Coequalizer

In the APG framework, coequalizers are computed from two morphisms
`j, k: N → M`. In CQL, we can model this structurally using **sigma**
(pushforward) data migration. We add an explicit `Overlap` entity with
foreign keys `left` and `right` pointing to the two overlapping plates,
then push forward along a mapping that collapses `Overlap` into
`PlateNumber`:

``` julia
env = cql"""
typeside Ty = literal {
    types
        Str
    constants
        US MX CA BC SN v6trj244 ahd4102 vuk1775 : Str
}

schema PlateSch = literal : Ty {
    entities
        PlateNumber
    attributes
        plate_id  : PlateNumber -> Str
        region_id : PlateNumber -> Str
        region_lp : PlateNumber -> Str
}

schema OverlapSch = literal : Ty {
    entities
        Overlap
        PlateNumber
    foreign_keys
        left  : Overlap -> PlateNumber
        right : Overlap -> PlateNumber
    attributes
        plate_id  : PlateNumber -> Str
        region_id : PlateNumber -> Str
        region_lp : PlateNumber -> Str
}

mapping Merge = literal : OverlapSch -> PlateSch {
    entity
        Overlap -> PlateNumber
        foreign_keys
            left  -> PlateNumber
            right -> PlateNumber
    entity
        PlateNumber -> PlateNumber
        attributes
            plate_id  -> lambda x. plate_id(x)
            region_id -> lambda x. region_id(x)
            region_lp -> lambda x. region_lp(x)
}

instance WithOverlap = literal : OverlapSch {
    generators
        p1 p2 q1 q2 : PlateNumber
        o1 : Overlap
    equations
        plate_id(p1) = US  region_id(p1) = CA  region_lp(p1) = v6trj244
        plate_id(p2) = MX  region_id(p2) = BC  region_lp(p2) = ahd4102
        plate_id(q1) = US  region_id(q1) = CA  region_lp(q1) = v6trj244
        plate_id(q2) = MX  region_id(q2) = SN  region_lp(q2) = vuk1775
        left(o1)  = p1
        right(o1) = q1
}

instance SigmaMerged = sigma Merge WithOverlap
"""

alg = env.SigmaMerged.algebra
println("After sigma merge: ", length(carrier(alg, :PlateNumber)), " plates\n")
for x in carrier(alg, :PlateNumber)
    pid = eval_att(alg, :plate_id, x)
    rid = eval_att(alg, :region_id, x)
    rlp = eval_att(alg, :region_lp, x)
    println("  ", repr_x(alg, x), ": ", pid, "/", rid, "/", rlp)
end
```

    After sigma merge: 3 plates

      q2: MX/SN/vuk1775
      p1: US/CA/v6trj244
      p2: MX/BC/ahd4102

The sigma maps both `Overlap` and `PlateNumber` to `PlateNumber`, and
the FK equations `left(o1) = p1`, `right(o1) = q1` become `o1 = p1` and
`o1 = q1` after pushforward, giving `p1 = q1` transitively. This is
exactly the APG coequalizer construction.

## Delta: Schema Evolution

APG **mappings** between schemas define how to transform data. In CQL, a
mapping `F: S → T` induces a **delta** (pullback) functor that
restructures instances of `T` into instances of `S`.

``` julia
env = cql"""
typeside Ty = literal {
    types
        Str
        Nat
    constants
        Alice Bob v40 v30 : Str
        n40 n30 : Nat
}

schema PersonSch = literal : Ty {
    entities
        Person
    attributes
        age  : Person -> Nat
        name : Person -> Str
}

schema RecordSch = literal : Ty {
    entities
        Record
    attributes
        rec_name : Record -> Str
        rec_age  : Record -> Str
}

mapping PersonToRecord = literal : PersonSch -> RecordSch {
    entity
        Person -> Record
        attributes
            age  -> lambda x. rec_age(x)
            name -> lambda x. rec_name(x)
}

instance Records = literal : RecordSch {
    generators
        r1 r2 : Record
    equations
        rec_name(r1) = Alice  rec_age(r1) = v40
        rec_name(r2) = Bob    rec_age(r2) = v30
}

instance Persons = delta PersonToRecord Records
"""

alg = env.Persons.algebra
println("Delta pullback: Records → Persons\n")
for x in carrier(alg, :Person)
    nm = eval_att(alg, :name, x)
    ag = eval_att(alg, :age, x)
    println("  ", repr_x(alg, x), ": name=", nm, " age=", ag)
end
```

    Delta pullback: Records → Persons

      Person_r1: name=Alice age=v40
      Person_r2: name=Bob age=v30

The delta functor pulls the `Records` instance back along the mapping,
renaming `rec_name` → `name` and `rec_age` → `age`. In the APG
framework, this corresponds to the pullback of an instance along a
schema morphism.

## Handling Union Types

APGs support **coproduct** (union/variant) types like
`<place: label PlaceEvent + null: ()>`. CQL does not have built-in union
types, but they can be encoded using the **tagged union pattern**: a
separate entity with discriminator attributes and optional foreign keys.

For example, the APG type:

    OptionalEvent -> <place: label PlaceEvent + null: ()>

can be encoded as:

    entity OptionalEvent
    foreign_keys
        opt_event : OptionalEvent -> PlaceEvent   -- only valid when tag = place
    attributes
        tag : OptionalEvent -> Str                 -- "place" or "null"

In practice, most APG schemas can be expressed without union types by
using separate edge labels for each case (e.g., `TripWithEvents` and
`TripWithoutEvents` instead of a single `Trip` with optional events).
This is a common pattern in relational databases as well.

## APGs vs Traditional Property Graphs

Traditional property graphs (Neo4j, TinkerPop) and APGs represent the
same kind of data, but APGs add algebraic structure:

| Aspect | Traditional PG | Algebraic PG (CQL) |
|----|----|----|
| **Schema** | Optional, informal | Required, algebraic types |
| **Vertex types** | String labels | Entities (typed labels) |
| **Edge types** | String labels | Entities with typed FKs |
| **Properties** | Key-value bags | Typed attributes |
| **Multi-valued props** | List-valued properties | Reified property entities |
| **Type checking** | Runtime (if at all) | Compile-time |
| **Morphisms** | Not defined | Structure-preserving maps |
| **Products** | Not supported | Natural (FK + attribute tuples) |
| **Coproducts** | Not supported | Encodable (tagged unions) |
| **Deduplication** | Application logic | Coequalizer (sigma) |
| **Schema evolution** | Manual migration | Delta pullback |
| **Query semantics** | Imperative (Cypher) | Categorical (uber-flower) |

The key insight from the APG paper is that property graphs are not a
fundamentally different data model from relational databases — they are
a **presentation** of the same categorical structure. By giving property
graphs algebraic types, we gain all the tools of categorical data
integration: composable mappings, adjoint data migration functors
($\Sigma \dashv \Delta \dashv \Pi$), and provably correct
transformations.

## Summary

| Concept | Description |
|----|----|
| **APG schema** | Labels with algebraic type assignments (unit, base, product, coproduct) |
| **APG instance** | Elements assigned to labels, with terms conforming to label types |
| **CQL encoding** | Labels → entities, label refs → FKs, base types → attributes |
| **Reified properties** | Multi-valued properties as separate entities with FK back to owner |
| **Coequalizer** | Merge duplicate elements via equations or sigma pushforward |
| **Delta pullback** | Schema evolution via mapping-induced data restructuring |
| **Query** | Multi-variable from-where-attributes traverses the property graph |

Algebraic Property Graphs unify property graphs with the functorial data
model. CQL.jl provides a practical implementation: every APG with
product and base label types maps directly to a CQL schema, and APG
operations (morphisms, coequalizers, pullbacks) correspond to CQL
transforms, sigma, and delta. The type system catches errors at compile
time, and the theorem prover handles deduplication automatically.
