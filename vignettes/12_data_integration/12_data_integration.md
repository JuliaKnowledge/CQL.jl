# Categorical Data Integration
CQL.jl

## Introduction

**Data integration** — combining data from heterogeneous sources into a
unified, consistent view — is a pervasive challenge in computational
science. Schema differences, naming inconsistencies, denormalized
layouts, and derived attributes all complicate the task.

The **Categorical Query Language (CQL)** provides a principled approach
based on *functorial data migration*. Rather than writing ad-hoc ETL
scripts, we express each integration step as a mathematical functor
between categories (schemas), and CQL automatically computes the
resulting data.

This vignette demonstrates a complete integration pipeline on a library
database, adapted from [Brown, Spivak & Wisnesky
(2019)](https://arxiv.org/abs/1903.10579) and the companion [Python
code](https://github.com/kris-brown/cql_data_integration). We show how
to:

1.  **Define** a denormalized source schema and populate it with data
2.  **Query** to normalize, enrich, and restructure into a target schema
    — including generating new entities from computed joins
3.  **Correct** data errors and deduplicate entities
4.  **Decompose** the pipeline into reusable query + mapping + sigma
    steps, demonstrating **labeled nulls** for missing data

``` julia
using CQL
```

## The Source Data

Our source is a denormalized library database with three entities:
`Book` (with inline author name), `Chapter`, and `Reader`. The `Reader`
entity has a `borrowed` attribute storing a comma-separated list of book
titles the reader has checked out — this is typical of denormalized data
where a structured relationship is collapsed into a single string field.

The typeside includes a `contains` function that tests whether a string
contains a substring. Since CQL.jl uses symbolic computation (unlike the
Java CQL which can execute Java code), we provide ground equations that
define `contains` for each (borrowed-list, title) pair in our data.

``` julia
env = cql"""
typeside Ty = literal {
    types
        Str
        Bool
    constants
        Mann Kakfa Kafka : Str
        Magic Meta Castle : Str
        KSB BR : Str
        borrowed_mm borrowed_m : Str
        text_mm1 text_mm2 text_met text_cas : Str
        v1 v2 v1924 v1915 v1926 : Str
        strue sfalse : Bool
    functions
        contains : Str, Str -> Bool
        count_words : Str -> Str
        str_len : Str -> Str
        plus : Str, Str -> Str
    equations
        contains(borrowed_mm, Magic) = strue
        contains(borrowed_mm, Meta) = strue
        contains(borrowed_mm, Castle) = sfalse
        contains(borrowed_m, Magic) = sfalse
        contains(borrowed_m, Meta) = strue
        contains(borrowed_m, Castle) = sfalse
}

schema Source = literal : Ty {
    entities
        Book
        Chapter
        Reader
    foreign_keys
        chapter_book : Chapter -> Book
        reader_fav   : Reader  -> Book
    attributes
        author_name  : Book    -> Str
        title        : Book    -> Str
        year         : Book    -> Str
        chapter_num  : Chapter -> Str
        chapter_text : Chapter -> Str
        reader_name  : Reader  -> Str
        borrowed     : Reader  -> Str
}

instance LibraryData = literal : Source {
    generators
        b1 b2 b3 : Book
        ch1 ch2 ch3 ch4 : Chapter
        r1 r2 : Reader
    multi_equations
        author_name  -> {b1 Mann, b2 Kakfa, b3 Kafka}
        title        -> {b1 Magic, b2 Meta, b3 Castle}
        year         -> {b1 v1924, b2 v1915, b3 v1926}
        chapter_num  -> {ch1 v1, ch2 v2, ch3 v1, ch4 v1}
        chapter_text -> {ch1 text_mm1, ch2 text_mm2, ch3 text_met, ch4 text_cas}
        chapter_book -> {ch1 b1, ch2 b1, ch3 b2, ch4 b3}
        reader_name  -> {r1 KSB, r2 BR}
        borrowed     -> {r1 borrowed_mm, r2 borrowed_m}
        reader_fav   -> {r1 b1, r2 b2}
}
"""
nothing
```

The source has three books (with a deliberate typo: `Kakfa` instead of
`Kafka` for *Metamorphosis*), four chapters, and two readers. Reader
`r1` (KSB) has borrowed *Magic Mountain* and *Metamorphosis*; reader
`r2` (BR) has borrowed only *Metamorphosis*.

``` julia
alg = env.LibraryData.algebra
println("Books: ", length(carrier(alg, :Book)))
for x in carrier(alg, :Book)
    t = eval_att(alg, :title, x)
    a = eval_att(alg, :author_name, x)
    println("  $t by $a")
end
println("\nReaders:")
for x in carrier(alg, :Reader)
    println("  ", eval_att(alg, :reader_name, x),
            " (borrowed: ", eval_att(alg, :borrowed, x), ")")
end
```

    Books: 3
      Meta by Kakfa
      Castle by Kafka
      Magic by Mann

    Readers:
      BR (borrowed: borrowed_m)
      KSB (borrowed: borrowed_mm)

Notice two problems: the author name is stored redundantly on each
`Book`, so `Kafka` and `Kakfa` coexist as separate strings with no
shared `Author` entity; and the borrow relationships are buried inside
the `borrowed` string attribute rather than structured as proper
records.

## Direct Query: Source to Target

The **target** schema normalizes the data by extracting a separate
`Author` entity, renaming `Book` to `Novel`, adding a computed
`chapter_nwords` attribute (word count of the chapter text), and
computing `total_len` (sum of reader name and title lengths) on each
borrow record.

An **uber-flower query** maps each target entity back to a combination
of source entities:

- `Novel` comes from `Book`, inheriting the title
- `Author` comes from `Book`, extracting the author name (one Author per
  Book initially)
- `Chapter` adds the computed `count_words(chapter_text)`
- `Reader` maps directly
- `Borrow` is generated from the Cartesian product of `Book` and
  `Reader`, filtered by the `where` clause:
  `contains(r.borrowed, b.title) = strue`. This tests whether the
  reader’s borrowed-list includes the book’s title, turning the
  denormalized string into structured borrow records.

``` julia
env2 = cql"""
typeside Ty = literal {
    types Str Bool
    constants
        Mann Kakfa Kafka : Str
        Magic Meta Castle : Str
        KSB BR : Str
        borrowed_mm borrowed_m : Str
        text_mm1 text_mm2 text_met text_cas : Str
        v1 v2 v1924 v1915 v1926 : Str
        strue sfalse : Bool
    functions
        contains : Str, Str -> Bool
        count_words : Str -> Str
        str_len : Str -> Str
        plus : Str, Str -> Str
    equations
        contains(borrowed_mm, Magic) = strue
        contains(borrowed_mm, Meta) = strue
        contains(borrowed_mm, Castle) = sfalse
        contains(borrowed_m, Magic) = sfalse
        contains(borrowed_m, Meta) = strue
        contains(borrowed_m, Castle) = sfalse
}

schema Source = literal : Ty {
    entities Book Chapter Reader
    foreign_keys
        chapter_book : Chapter -> Book
        reader_fav   : Reader  -> Book
    attributes
        author_name  : Book    -> Str
        title        : Book    -> Str
        year         : Book    -> Str
        chapter_num  : Chapter -> Str
        chapter_text : Chapter -> Str
        reader_name  : Reader  -> Str
        borrowed     : Reader  -> Str
}

schema Target = literal : Ty {
    entities
        Novel Chapter Author Reader Borrow
    foreign_keys
        chapter_novel : Chapter -> Novel
        novel_author  : Novel   -> Author
        reader_fav    : Reader  -> Novel
        borrow_reader : Borrow  -> Reader
        borrow_novel  : Borrow  -> Novel
    attributes
        novel_title    : Novel   -> Str
        chapter_num    : Chapter -> Str
        chapter_nwords : Chapter -> Str
        author_name    : Author  -> Str
        reader_name    : Reader  -> Str
        total_len      : Borrow  -> Str
}

query Integrate = literal : Source -> Target {
    entity Novel -> {
        from b : Book
        attributes novel_title -> b.title
        foreign_keys novel_author -> {b -> b}
    }
    entity Chapter -> {
        from c : Chapter
        attributes
            chapter_num    -> c.chapter_num
            chapter_nwords -> count_words(c.chapter_text)
        foreign_keys chapter_novel -> {b -> c.chapter_book}
    }
    entity Author -> {
        from b : Book
        attributes author_name -> b.author_name
    }
    entity Reader -> {
        from r : Reader
        attributes reader_name -> r.reader_name
        foreign_keys reader_fav -> {b -> r.reader_fav}
    }
    entity Borrow -> {
        from b : Book r : Reader
        where contains(r.borrowed, b.title) = strue
        attributes
            total_len -> plus(str_len(r.reader_name), str_len(b.title))
        foreign_keys
            borrow_reader -> {r -> r}
            borrow_novel  -> {b -> b}
    }
}

instance LibraryData = literal : Source {
    generators
        b1 b2 b3 : Book
        ch1 ch2 ch3 ch4 : Chapter
        r1 r2 : Reader
    multi_equations
        author_name  -> {b1 Mann, b2 Kakfa, b3 Kafka}
        title        -> {b1 Magic, b2 Meta, b3 Castle}
        year         -> {b1 v1924, b2 v1915, b3 v1926}
        chapter_num  -> {ch1 v1, ch2 v2, ch3 v1, ch4 v1}
        chapter_text -> {ch1 text_mm1, ch2 text_mm2, ch3 text_met, ch4 text_cas}
        chapter_book -> {ch1 b1, ch2 b1, ch3 b2, ch4 b3}
        reader_name  -> {r1 KSB, r2 BR}
        borrowed     -> {r1 borrowed_mm, r2 borrowed_m}
        reader_fav   -> {r1 b1, r2 b2}
}

instance Result = eval Integrate LibraryData
"""
nothing
```

Let’s inspect the result:

``` julia
alg2 = env2.Result.algebra
println("Target instance:")
println("  Novels:   ", length(carrier(alg2, :Novel)))
println("  Chapters: ", length(carrier(alg2, :Chapter)))
println("  Authors:  ", length(carrier(alg2, :Author)))
println("  Readers:  ", length(carrier(alg2, :Reader)))
println("  Borrows:  ", length(carrier(alg2, :Borrow)))
```

    Target instance:
      Novels:   3
      Chapters: 4
      Authors:  3
      Readers:  2
      Borrows:  3

``` julia
println("Novels (with extracted Author):")
for x in carrier(alg2, :Novel)
    t = eval_att(alg2, :novel_title, x)
    a = eval_fk(alg2, :novel_author, x)
    an = eval_att(alg2, :author_name, a)
    println("  $t by $an")
end
```

    Novels (with extracted Author):
      Castle by Kafka
      Magic by Mann
      Meta by Kakfa

``` julia
println("Chapters (with computed word count):")
for x in carrier(alg2, :Chapter)
    n = eval_fk(alg2, :chapter_novel, x)
    t = eval_att(alg2, :novel_title, n)
    num = eval_att(alg2, :chapter_num, x)
    nw = eval_att(alg2, :chapter_nwords, x)
    println("  $t ch.$num — n_words = $nw")
end
```

    Chapters (with computed word count):
      Magic ch.v1 — n_words = count_words(text_mm1)
      Castle ch.v1 — n_words = count_words(text_cas)
      Magic ch.v2 — n_words = count_words(text_mm2)
      Meta ch.v1 — n_words = count_words(text_met)

The word counts appear as symbolic expressions `count_words(text_mm1)`
etc. because `count_words` is declared as a typeside function without
ground evaluation equations — CQL treats it as an uninterpreted function
symbol. In the original Python/Java pipeline, `count_words` has a Java
implementation that evaluates immediately.

``` julia
println("Authors (one per book — note the typo):")
for x in carrier(alg2, :Author)
    println("  ", eval_att(alg2, :author_name, x))
end
```

    Authors (one per book — note the typo):
      Kakfa
      Mann
      Kafka

``` julia
println("Borrows (generated from contains-based join):")
for x in carrier(alg2, :Borrow)
    r = eval_fk(alg2, :borrow_reader, x)
    n = eval_fk(alg2, :borrow_novel, x)
    tl = eval_att(alg2, :total_len, x)
    println("  ", eval_att(alg2, :reader_name, r), " borrowed ",
            eval_att(alg2, :novel_title, n), "  (total_len = $tl)")
end
```

    Borrows (generated from contains-based join):
      KSB borrowed Magic  (total_len = plus(str_len(KSB),str_len(Magic)))
      KSB borrowed Meta  (total_len = plus(str_len(KSB),str_len(Meta)))
      BR borrowed Meta  (total_len = plus(str_len(BR),str_len(Meta)))

We now have 3 Borrow records, derived from the denormalized `borrowed`
string via the `contains` function in the `where` clause. Each Borrow
also carries a `total_len` attribute (symbolic expression
`plus(str_len(...), str_len(...))`). There are 3 separate Author
elements — one per book — preserving the `Kakfa`/`Kafka` typo.

## Correcting and Deduplicating

In the original paper, a *coequalizer* merges duplicate authors. Here we
demonstrate the corrected target instance directly, fixing the `Kakfa`
typo and sharing a single `kafka` author between *Metamorphosis* and
*The Castle*.

``` julia
env3 = cql"""
typeside Ty = literal {
    types Str Bool
    constants
        Mann Kafka Magic Meta Castle KSB BR : Str
        text_mm1 text_mm2 text_met text_cas : Str
        v1 v2 : Str
    functions
        count_words : Str -> Str
        str_len : Str -> Str
        plus : Str, Str -> Str
}

schema Target = literal : Ty {
    entities
        Novel Chapter Author Reader Borrow
    foreign_keys
        chapter_novel : Chapter -> Novel
        novel_author  : Novel   -> Author
        reader_fav    : Reader  -> Novel
        borrow_reader : Borrow  -> Reader
        borrow_novel  : Borrow  -> Novel
    attributes
        novel_title    : Novel   -> Str
        chapter_num    : Chapter -> Str
        chapter_nwords : Chapter -> Str
        author_name    : Author  -> Str
        reader_name    : Reader  -> Str
        total_len      : Borrow  -> Str
}

instance Corrected = literal : Target {
    generators
        novel_magic novel_meta novel_castle : Novel
        ch1 ch2 ch3 ch4 : Chapter
        mann kafka : Author
        reader_ksb reader_br : Reader
        borrow1 borrow2 borrow3 : Borrow
    equations
        novel_title(novel_magic) = Magic
        novel_title(novel_meta) = Meta
        novel_title(novel_castle) = Castle
        novel_author(novel_magic) = mann
        novel_author(novel_meta) = kafka
        novel_author(novel_castle) = kafka
        chapter_novel(ch1) = novel_magic  chapter_num(ch1) = v1
        chapter_novel(ch2) = novel_magic  chapter_num(ch2) = v2
        chapter_novel(ch3) = novel_meta   chapter_num(ch3) = v1
        chapter_novel(ch4) = novel_castle chapter_num(ch4) = v1
        chapter_nwords(ch1) = count_words(text_mm1)
        chapter_nwords(ch2) = count_words(text_mm2)
        chapter_nwords(ch3) = count_words(text_met)
        chapter_nwords(ch4) = count_words(text_cas)
        author_name(mann) = Mann
        author_name(kafka) = Kafka
        reader_name(reader_ksb) = KSB
        reader_name(reader_br) = BR
        reader_fav(reader_ksb) = novel_magic
        reader_fav(reader_br) = novel_meta
        borrow_reader(borrow1) = reader_ksb  borrow_novel(borrow1) = novel_magic
        borrow_reader(borrow2) = reader_ksb  borrow_novel(borrow2) = novel_meta
        borrow_reader(borrow3) = reader_br   borrow_novel(borrow3) = novel_meta
        total_len(borrow1) = plus(str_len(KSB), str_len(Magic))
        total_len(borrow2) = plus(str_len(KSB), str_len(Meta))
        total_len(borrow3) = plus(str_len(BR), str_len(Meta))
    options
        interpret_as_algebra = true
}
"""
nothing
```

``` julia
alg3 = env3.Corrected.algebra
println("Corrected instance:")
println("  Authors: ", length(carrier(alg3, :Author)))
for x in carrier(alg3, :Author)
    println("    ", eval_att(alg3, :author_name, x))
end
println("\n  Novels per Author:")
for a in carrier(alg3, :Author)
    an = eval_att(alg3, :author_name, a)
    novels = [eval_att(alg3, :novel_title, n) for n in carrier(alg3, :Novel)
              if eval_fk(alg3, :novel_author, n) == a]
    println("    $an: ", join(string.(novels), ", "))
end
```

    Corrected instance:
      Authors: 2
        Kafka
        Mann

      Novels per Author:
        Kafka: Castle, Meta
        Mann: Magic

Now Kafka is a single author entity shared by both *Metamorphosis* and
*The Castle*. The typo has been corrected and the data is properly
normalized.

## Decomposed Pipeline: Query + Mapping + Sigma

In practice, integration pipelines are often decomposed into smaller,
reusable steps. Following the approach in [Brown et
al. (2019)](https://arxiv.org/abs/1903.10579) and the companion [Python
code](https://github.com/kris-brown/cql_data_integration), we factor the
integration into:

1.  **Query (Enrich)**: `Source → Intermediate` — extracts `Author` from
    `Book`, generates `Borrow` from the `contains`-based join, computes
    `chapter_nwords` and `total_len`
2.  **Mapping (Rename)**: `Intermediate → Target` — renames entities
    (`Book → Novel`) and foreign keys, and the target schema includes
    additional entities (`Library`) and attributes (`author_born`,
    `chapter_page_start`, `borrow_date`) not present in the intermediate
    schema
3.  **Sigma**: pushes the enriched data forward along the mapping,
    automatically generating **labeled nulls** (Skolem terms) for any
    target-side information that couldn’t be derived from the source

This decomposition separates *structural enrichment* (adding new
entities and computed attributes) from *naming conventions* (aligning
with the target schema vocabulary). The target schema here includes a
`Library` entity with a `most_popular` foreign key to `Novel`, following
the original Python code — even though the source has no library data.

``` julia
common_typeside = """
typeside Ty = literal {
    types Str Bool
    constants
        Mann Kakfa Kafka : Str
        Magic Meta Castle : Str
        KSB BR : Str
        borrowed_mm borrowed_m : Str
        text_mm1 text_mm2 text_met text_cas : Str
        v1 v2 v1924 v1915 v1926 : Str
        strue sfalse : Bool
    functions
        contains : Str, Str -> Bool
        count_words : Str -> Str
        str_len : Str -> Str
        plus : Str, Str -> Str
    equations
        contains(borrowed_mm, Magic) = strue
        contains(borrowed_mm, Meta) = strue
        contains(borrowed_mm, Castle) = sfalse
        contains(borrowed_m, Magic) = sfalse
        contains(borrowed_m, Meta) = strue
        contains(borrowed_m, Castle) = sfalse
}
"""
nothing
```

``` julia
env4 = run_program(common_typeside * """
schema Source = literal : Ty {
    entities Book Chapter Reader
    foreign_keys
        chapter_book : Chapter -> Book
        reader_fav   : Reader  -> Book
    attributes
        author_name  : Book    -> Str
        title        : Book    -> Str
        year         : Book    -> Str
        chapter_num  : Chapter -> Str
        chapter_text : Chapter -> Str
        reader_name  : Reader  -> Str
        borrowed     : Reader  -> Str
}

schema Intermediate = literal : Ty {
    entities Book Chapter Author Reader Borrow
    foreign_keys
        chapter_book  : Chapter -> Book
        book_author   : Book    -> Author
        reader_fav    : Reader  -> Book
        borrow_reader : Borrow  -> Reader
        borrow_book   : Borrow  -> Book
    attributes
        book_title     : Book    -> Str
        chapter_num    : Chapter -> Str
        chapter_nwords : Chapter -> Str
        author_name    : Author  -> Str
        reader_name    : Reader  -> Str
        total_len      : Borrow  -> Str
}

schema Target = literal : Ty {
    entities Novel Chapter Author Reader Borrow Library
    foreign_keys
        chapter_novel  : Chapter -> Novel
        novel_author   : Novel   -> Author
        reader_fav     : Reader  -> Novel
        borrow_reader  : Borrow  -> Reader
        borrow_novel   : Borrow  -> Novel
        borrow_library : Borrow  -> Library
        most_popular   : Library -> Novel
    attributes
        novel_title        : Novel   -> Str
        chapter_num        : Chapter -> Str
        chapter_nwords     : Chapter -> Str
        chapter_page_start : Chapter -> Str
        author_name        : Author  -> Str
        author_born        : Author  -> Str
        reader_name        : Reader  -> Str
        total_len          : Borrow  -> Str
        borrow_date        : Borrow  -> Str
        library_name       : Library -> Str
}

query Enrich = literal : Source -> Intermediate {
    entity Book -> {
        from b : Book
        attributes book_title -> b.title
        foreign_keys book_author -> {b -> b}
    }
    entity Chapter -> {
        from c : Chapter
        attributes
            chapter_num    -> c.chapter_num
            chapter_nwords -> count_words(c.chapter_text)
        foreign_keys chapter_book -> {b -> c.chapter_book}
    }
    entity Author -> {
        from b : Book
        attributes author_name -> b.author_name
    }
    entity Reader -> {
        from r : Reader
        attributes reader_name -> r.reader_name
        foreign_keys reader_fav -> {b -> r.reader_fav}
    }
    entity Borrow -> {
        from b : Book r : Reader
        where contains(r.borrowed, b.title) = strue
        attributes
            total_len -> plus(str_len(r.reader_name), str_len(b.title))
        foreign_keys
            borrow_reader -> {r -> r}
            borrow_book   -> {b -> b}
    }
}

mapping Rename = literal : Intermediate -> Target {
    entity
        Book -> Novel
        foreign_keys
            book_author -> novel_author
        attributes
            book_title -> novel_title
    entity
        Chapter -> Chapter
        foreign_keys
            chapter_book -> chapter_novel
        attributes
            chapter_num -> chapter_num
            chapter_nwords -> chapter_nwords
    entity
        Author -> Author
        attributes
            author_name -> author_name
    entity
        Reader -> Reader
        foreign_keys
            reader_fav -> reader_fav
        attributes
            reader_name -> reader_name
    entity
        Borrow -> Borrow
        foreign_keys
            borrow_reader -> borrow_reader
            borrow_book -> borrow_novel
        attributes
            total_len -> total_len
}

instance LibraryData = literal : Source {
    generators
        b1 b2 b3 : Book
        ch1 ch2 ch3 ch4 : Chapter
        r1 r2 : Reader
    multi_equations
        author_name  -> {b1 Mann, b2 Kakfa, b3 Kafka}
        title        -> {b1 Magic, b2 Meta, b3 Castle}
        year         -> {b1 v1924, b2 v1915, b3 v1926}
        chapter_num  -> {ch1 v1, ch2 v2, ch3 v1, ch4 v1}
        chapter_text -> {ch1 text_mm1, ch2 text_mm2, ch3 text_met, ch4 text_cas}
        chapter_book -> {ch1 b1, ch2 b1, ch3 b2, ch4 b3}
        reader_name  -> {r1 KSB, r2 BR}
        borrowed     -> {r1 borrowed_mm, r2 borrowed_m}
        reader_fav   -> {r1 b1, r2 b2}
}

instance Enriched = eval Enrich LibraryData
instance Migrated = sigma Rename Enriched {
    options allow_empty_sorts_unsafe = true
}
""")
nothing
```

Let’s inspect the migrated instance:

``` julia
alg4 = env4.Migrated.algebra
println("After Enrich (query) + Rename (sigma):")
println("  Novels:    ", length(carrier(alg4, :Novel)))
println("  Chapters:  ", length(carrier(alg4, :Chapter)))
println("  Authors:   ", length(carrier(alg4, :Author)))
println("  Readers:   ", length(carrier(alg4, :Reader)))
println("  Borrows:   ", length(carrier(alg4, :Borrow)))
println("  Libraries: ", length(carrier(alg4, :Library)))
```

    After Enrich (query) + Rename (sigma):
      Novels:    6
      Chapters:  4
      Authors:   6
      Readers:   2
      Borrows:   3
      Libraries: 3

There are 6 Novels and 6 Authors instead of 3 each, and 3 Libraries have
appeared — despite the source having no library data at all. This is the
**labeled null cascade** described in the Python code’s README:

> Each Borrow has a `borrow_library` FK that must point somewhere, so 3
> Library entities are generated (one per Borrow — we have no reason to
> conclude they are the same library). Each Library has a `most_popular`
> FK to Novel, generating 3 more Novels. Each of those Novels has a
> `novel_author` FK, generating 3 more Authors.

``` julia
println("Borrows:")
for x in carrier(alg4, :Borrow)
    r = eval_fk(alg4, :borrow_reader, x)
    n = eval_fk(alg4, :borrow_novel, x)
    lib = eval_fk(alg4, :borrow_library, x)
    println("  ", eval_att(alg4, :reader_name, r), " borrowed ",
            eval_att(alg4, :novel_title, n))
    println("    total_len:  ", eval_att(alg4, :total_len, x))
    println("    date:       ", eval_att(alg4, :borrow_date, x))
    println("    library:    ", eval_att(alg4, :library_name, lib))
end
```

    Borrows:
      KSB borrowed Magic
        total_len:  plus(str_len(KSB),str_len(Magic))
        date:       q_Borrow_3.borrow_date
        library:    q_Borrow_3.borrow_library.library_name
      BR borrowed Meta
        total_len:  plus(str_len(BR),str_len(Meta))
        date:       q_Borrow_1.borrow_date
        library:    q_Borrow_1.borrow_library.library_name
      KSB borrowed Meta
        total_len:  plus(str_len(KSB),str_len(Meta))
        date:       q_Borrow_2.borrow_date
        library:    q_Borrow_2.borrow_library.library_name

The `borrow_date` and `library_name` values are Skolem terms (labeled
nulls) — distinct unknown values that participate in the algebra like
variables. This is CQL’s approach to handling missing data: rather than
SQL’s single `NULL`, each unknown gets a unique symbolic term that
tracks its provenance.

``` julia
println("Authors (3 real + 3 from labeled null cascade):")
for x in carrier(alg4, :Author)
    an = eval_att(alg4, :author_name, x)
    born = eval_att(alg4, :author_born, x)
    println("  name = $an")
    println("    born = $born")
end
```

    Authors (3 real + 3 from labeled null cascade):
      name = q_Borrow_3.borrow_library.most_popular.novel_author.author_name
        born = q_Borrow_3.borrow_library.most_popular.novel_author.author_born
      name = Mann
        born = q_Book_3.novel_author.author_born
      name = q_Borrow_2.borrow_library.most_popular.novel_author.author_name
        born = q_Borrow_2.borrow_library.most_popular.novel_author.author_born
      name = q_Borrow_1.borrow_library.most_popular.novel_author.author_name
        born = q_Borrow_1.borrow_library.most_popular.novel_author.author_born
      name = Kafka
        born = q_Chapter_4.chapter_novel.novel_author.author_born
      name = Kakfa
        born = q_Chapter_1.chapter_novel.novel_author.author_born

The 3 original authors (Mann, Kakfa, Kafka) have unknown `born` values
(Skolem terms). The 3 cascade-generated authors have unknown names and
unknown birth years. The `chapter_page_start` attributes are similarly
Skolem terms for all 4 chapters.

## Summary

This vignette demonstrated the key ideas from [Brown, Spivak & Wisnesky
(2019)](https://arxiv.org/abs/1903.10579):

| Step | CQL Operation | Purpose |
|----|----|----|
| Normalize | Query (`eval`) | Extract `Author` from `Book`, compute derived attributes |
| Entity generation | Query with `where` clause | Create `Borrow` from `(Book, Reader)` join via `contains` |
| Rename | Mapping + Sigma | Align entity/FK names with target schema |
| Labeled nulls | Sigma migration | Automatically fill missing FKs/attributes with Skolem terms |
| Deduplicate | Corrected instance | Fix typos, merge equivalent entities |

Comparing with the Python/Java CQL pipeline:

| Feature | Python/Java CQL | CQL.jl |
|----|----|----|
| Functions | Java-backed (`count_words` evaluates) | Symbolic (uninterpreted or ground equations) |
| `contains` / regex | Java `matches` with regex patterns | Typeside ground equations for specific inputs |
| `total_len` | Evaluates to concrete integers | Symbolic `plus(str_len(...), str_len(...))` |
| Labeled nulls | Automatic (sigma creates Skolem-filled entities) | Same behavior |
| Deduplication | `quotient_query` (automatic by key equality) | Manual corrected instance |

The **functorial data migration** framework provides several advantages
over ad-hoc ETL:

- **Correctness by construction**: each migration step is a well-typed
  functor, so data integrity constraints are automatically preserved
- **Composability**: pipelines decompose into reusable query, mapping,
  and sigma steps
- **Labeled nulls**: missing data is represented as distinct Skolem
  terms with full provenance, rather than a single undifferentiated NULL
- **Transparency**: symbolic function applications (like `count_words`)
  make the transformation explicit, even before concrete implementations
  are provided
- **Schema evolution**: the intermediate schema serves as documentation
  of the enrichment step, separate from naming conventions

For real-world applications involving materials science databases, see
the [full paper](https://arxiv.org/abs/1903.10579) which applies this
approach to integrate data from the Open Quantum Materials Database.
