# Stage 8: one keyword fewer, twice — the surface after `functor` and `resource`

*Written 2026-09-17, before the change, because the change is Daniel's
call and the argument is the part worth reading. Nothing here is built.
Stage 8's shipped halves — the evidence fix and the declaration
substrate — are elsewhere; this is the SURFACE, proposed as option C
and nothing else.*

## The proposal, in one table

| today | proposed | what it is |
|---|---|---|
| `theory T(…) [in D] = …` | unchanged | a presentation |
| `model M [(P)] in T [(args)] [(A ↦ B via c)] = …` | unchanged | a presentation interpreted |
| `transformation N in A ⇒ B = w` | unchanged | a map between two models |
| `def f [in X] [with Y…] = body` | unchanged | a word |
| `type` / `data` | unchanged | the type layer |
| `import "f.braid"` | unchanged | an act on files |
| `table N(cols) = "f.csv"` | unchanged | an act on files |
| **`functor F = word`** | **`model F in Base = word`** | a model of `Base` whose table is COMPUTED |
| **`resource R = Ty`** | **`model R in Doctrine = Ty`** | a model of the Doctrine by the state construction at `Ty` |

Nine surface forms become seven. The declaration layer is then
`theory`, `model`, `transformation`, `def`, `type`, `data`, `import`,
`table` — with `in` and `with` the two header clauses, exactly as now.

CONSTRUCTS.md's opening sentence becomes: *beside the type layer
(`type`, `data`) there are **three declarations** — `theory`, `model`,
`transformation` — **one definition form** (`def`), **two file acts**
(`import`, `table`) and **two header clauses** (`in`, `with`).*

---

## 1. `resource R = Ty` → `model R in Doctrine = Ty`

### What is already true

Since 7b a `resource` declaration **is** a model declaration. `resource
Log = Str` generates, and `:doc Log` prints:

```text
data Log@k(a..., b...) = Fn⟨Log a ⇒ Log b⟩
theory Log@t(k(..., ...)) in Doctrine =
    compose : k(a, b) k(b, c) ⇒ k(a, c)
    embed   : Fn⟨a ⇒ b⟩ ⇒ k(a, b)
model Log in Log@t(Log@k) =
    compose = Log@then
    embed   = Log@arr
```

Everything downstream — `transportOf`, `elabScope`, the receipt, the
routing pass read as that model's fused evaluator — already treats it
as one. The keyword is a second spelling for a thing the language
already has one spelling for, which is the house rule this violates.

### The spelling

```braid
model Log in Doctrine = Str
```

Read: **a model of as much of the Doctrine as the state construction at
`Str` supports.** The body is a *stack* (`model Books in Doctrine = Str
Int`), not a table of bindings, and that is what tells this head from
every other `model` head — the same content-directed rule the object
map already uses. A body with no `=` in it is a carrier; a body of
`p = q` lines is a table; a single name is a computed table (§2).

`in Doctrine` is the one genuine widening of `in`. Today `in` names a
theory (a template) or a model with a carrier (a hand-built morphism),
and on a `model` head it names the theory the model interprets. The
Doctrine is a presentation like any other, so naming it is well-formed;
what is new is that the model interprets a **sub-presentation** of it —
`compose` and `embed`, and not `observe`/`sample`, for 7b's reason (a
generated `observe` would have to run a resource program, which needs a
seed, and seeds live at install sites). That partiality has to be said
out loud in the manual, because a plain `model M in T` is total over
`T`'s slots and this one is not.

### What it checks, and what it generates

Byte for byte what `resource` checks and generates today: the carrier
line through `addType`, the theory through `parseTheory` + `checkExtends`,
the model through `parseInstance` + `checkInstance`, the two images as
generated defs. Nothing in the pipeline moves; the keyword guard in
`splitDefsIx` moves from `resource` to a shape test on a `model` body.
`:doc Log` prints exactly what it prints now.

### Before and after

| file | before | after |
|---|---|---|
| `examples/resources.braid` | `resource Log     = Str`<br>`resource Counter = Int` | `model Log     in Doctrine = Str`<br>`model Counter in Doctrine = Int` |
| `examples/metered.braid` | `resource Fuel = Int` | `model Fuel in Doctrine = Int` |
| `examples/payroll.braid` | `resource Books = Str Int` | `model Books in Doctrine = Str Int` |
| `examples/lifting.braid` | `resource Game = Int`<br>`resource Log = Str` | `model Game in Doctrine = Int`<br>`model Log in Doctrine = Str` |
| `examples/prob.braid` | `resource Rng = Int` | `model Rng in Doctrine = Int` |
| `examples/autodiff.braid` | `resource Gradient = Grad` | `model Gradient in Doctrine = Grad` |
| `test/imports/util.braid` | `resource Tally = Int` | `model Tally in Doctrine = Int` |

Nothing else in any of those files changes: `with Log`, `unLog`, `in
Log`'s refusal, the receipt `=Log>`, `:t!`'s routing explanation and
every printed line are untouched.

---

## 2. `functor F = word` → `model F in Base = word`

### The 7c objection, quoted

> The reason not to do it here is that a computed image cannot be
> blessed by `subsumes` at a declaration — there is nothing to bless
> until the word runs — so the fold would put two different checking
> stories under one keyword, and deciding how that reads is a stage's
> worth of work rather than a paragraph's.

### The answer

The objection is right about `subsumes` and wrong about "two checking
stories". There is **one** story, and the two bodies are two points on
the ladder `design-macros.md` already draws:

| the body of `model X in Base` | the model is | checked by | level |
|---|---|---|---|
| a table, `p = q, …` | a rewriting given by a table over the generators it names, the identity elsewhere | `checkBaseInstance`: each image blessed once by `subsumes` at the generator's own arrow | 2a — functorial by construction |
| a **program** `word` | a rewriting given by ONE image: the rewrite of the whole spine | `checkFunctorWord`: the word is `Code ⇒ Code`, pure, and defined at the first `with` | 2b — audited if claimed, never by construction |

So the model form **keeps exactly today's check**. `checkFunctorWord`
does not move, does not weaken and does not strengthen: it runs at the
first `with F`, it asks that the word's scheme subsume `Code ⇒ Code` at
pure grade, and it asks that the word be defined by then (the ordering
rule). What changes is the keyword in front of it and the sentence
`:doc` prints.

It is *weaker* than a table's check — that is the fact, not the
problem. A table's images are blessed at declaration; a program's image
is a program, and a program is not equal to anything until it runs. The
right move is not to pretend otherwise but to **say which**, which is
what 7c itself proposed:

```text
braid> :doc Traced
model Traced in Base — an UNCHECKED functor (level 2b): its table is
  computed by `marked : Code ⇒ Code`, so no image is blessed at this
  declaration.  Every `with Traced` mints `=Traced>`, and what it wrote
  is readable (`reflect`).
braid> :doc Opt
model Opt in Base — dupSwap = dup, copyDrop = id, dupInt = dup,
  twice = double  (every image blessed at its generator's arrow)
```

That is the same optimizer/dialect line this project has drawn since
2026-09-13 and the same line an object-mapped model's `:doc` draws
between PROVED and DIALECT. One keyword, one declaration, and the doc
says how much was checked. A reader who has to know the difference
asks; a reader who does not gets one construct instead of two.

### How the line parses

`model NAME in Base = REST`, and `REST` is read by content:

- `REST` contains a top-level `=` → a **table**. (Today's rule, and `;`
  still composes, so `mul = dup ; *` is one binding.)
- `REST` is a single identifier, or a program with no top-level `=` →
  a **computed image**. It is elaborated and run at the first `with`.
- `REST` is empty → today's refusal, unless there is a retraction.

There is no position to remember and no new punctuation: the same
content test that tells an object map (`↦`) from a theory argument.

### What is LOST, and it should be stated

`functor` is a noun that names what the thing is, and `model X in Base
= word` does not say "functor" anywhere. Two mitigations, both cheap:
`:doc` says *an UNCHECKED functor (level 2b)*, and `:defs` renders such
a model as `model Traced in Base = marked   (a functor — Code ⇒ Code)`.
The word survives in the vocabulary; only the keyword goes.

### Before and after

| file | before | after |
|---|---|---|
| `examples/traced.braid` | `functor Traced = marked`<br>`functor Ticked = ticked` | `model Traced in Base = marked`<br>`model Ticked in Base = ticked` |
| `examples/metered.braid` | `functor Metered = metered` | `model Metered in Base = metered` |
| `examples/optimizer.braid` | `functor Spaced  = spaced`<br>`functor Doubled = doubled` | `model Spaced  in Base = spaced`<br>`model Doubled in Base = doubled` |
| `examples/typerep.braid` | `functor Cells = cellsOfCode` | `model Cells in Base = cellsOfCode` |
| `test/imports/util.braid` | `functor Same = idF` | `model Same in Base = idF` |

`optimizer.braid` is the file that gains the most: it already declares
`model Opt in Base` beside `functor Spaced`, and after the fold the
three sit in one family with `:doc` distinguishing them — which is the
point that example has been making in prose since 2026-09-13.

---

## 3. The refusals for the retired keywords

By name, with the replacement spelled out, as `instance`, `mode`,
`rules`, `morphism`, `over` and `use` are:

```text
`functor` is gone since 2026-09-18: a functor is a rewriting of the
  ambient presentation, which is a MODEL of it — write
  `model Traced in Base = marked`.  Its table is computed rather than
  written, and `:doc Traced` says so.  CONSTRUCTS.md, MANUAL §8.

`resource` is gone since 2026-09-18: a resource IS the model of the
  Doctrine its declaration generated (stage 7b) — write
  `model Log in Doctrine = Str`.  `:doc Log` prints the carrier, the
  theory and the model, exactly as it did.  CONSTRUCTS.md, MANUAL §8.
```

Both are one-line mechanical rewrites, which is why refusing by name
rather than deprecating is the whole migration story.

---

## 4. The migration cost, counted

| site | `functor` | `resource` | total |
|---|---|---|---|
| `examples/*.braid` | 6 | 8 | 14 |
| `test/imports/*.braid` | 1 | 1 | 2 |
| `test/Tests.hs` source strings | 31 | 61 | 92 |
| **declaration sites** | **38** | **70** | **108** |
| `MANUAL.md` mentions | 19 | 18 | 37 |
| `CONSTRUCTS.md` mentions | 6 | 14 | 20 |
| other docs (`README`, `READING`, `design-*`) | 20 | 24 | 44 |

108 declaration sites and ~101 prose mentions. Every declaration site
is a textual substitution (`functor X =` → `model X in Base =`;
`resource X =` → `model X in Doctrine =`), so the risk is not in the
edit — it is in the **prose**, where "a resource" and "a functor" are
load-bearing nouns in about a hundred sentences and most of them stay
true. The keywords go; the nouns stay.

Printed output: **zero examples change a byte**, because neither fold
touches elaboration, generation, receipts or messages. That is the
property to hold the change to.

Checker cost, estimated: the `splitDefsIx` guards for `functor` and
`resource` become body-shape tests on the `model` guard; `parseFunctorLine`
and the `ownRes` derivation move behind `parseModelHead`; `modFunctors`
and the resource list stay as they are, fed from one parser instead of
three. No pass moves. The refusals above are two `Left` branches.

---

## 5. `import` and `table`: recommend they STAY keywords

They are not models and folding them in would cost the argument its
shape.

- **A model interprets a presentation in a category.** `import
  "util.braid"` interprets nothing: it is a **morphism of
  presentations** — objects added, never merged — and its argument is a
  *path*, not a theory. There is no category on the other side of it.
- **`table Trades = "trades.csv"` reads a file at check time and writes
  a `data` declaration and two words.** Its argument is also a path.
  Calling it `model Trades in Base = "trades.csv"` would make the one
  keyword that performs IO indistinguishable from the ones that do not,
  and the whole reason `table` is not `import` (2026-09-15) is that one
  keyword should not mean two things.
- Both act on **files**; every `model` acts on a **theory**. That is
  the line, it is short, and a reader can hold it.

The right home for `import` and `table` is the OTHER half of stage 8 —
they are already declaration WORDS (`importW : Str =Dict IO> •`,
`tableW : Str … =Dict IO> •`), which is the demolition
`design-macros.md` recorded for `table` in 2026-09-15. Keeping the
keyword and having the word beneath it is not a contradiction: that is
what the substrate is for.

---

## 6. What CONSTRUCTS.md's table becomes

The `functor` row and the `resource` row leave the table; the `model`
section gains two kinds, so "the same thing said five ways" becomes
**seven**:

| kind | object map | generator images |
|---|---|---|
| `model Opt in Base = p = q, …` | the identity | a table, partial |
| `model Traced in Base = marked` **(new)** | the identity | **one computed image** — the rewrite of the whole spine, level 2b |
| a plain model | the theory's parameters at this model's arguments | one program per slot |
| a Doctrine model | the identity on base types, `embed` total | the theory's slots; `;` ↦ `compose` |
| `model Log in Doctrine = Str` **(new)** | the identity on base types | the state construction at `Str`: `compose` and `embed` only |
| a family | a substitution driven by the parameter | over the parameter's words |
| an object-mapped model | a substitution, written | a table, partial, with unfolding and conjugation |

And the "What is NOT a construct" table gains two rows, `functor
(2026-09-18) → model of Base with a computed image` and `resource
(2026-09-18) → model of the Doctrine by the state construction`.

---

## 7. Open questions

1. **Does `in Doctrine` on a `model` head need a name of its own?** A
   model of a sub-presentation is a new thing for `in` to mean. The
   alternative is a named theory-former (`model Log in State = Str`),
   which is honest about the partiality but adds a name. Recommend
   `in Doctrine` and one manual paragraph; revisit if a second partial
   model of a doctrine ever appears.
2. **What does `with Log Traced` mean once both are models of `Base`
   or of a doctrine?** Today the `with` clause partitions by KIND
   (models rename, resources route, categories compose, functors
   rewrite, left to right) and the kinds are read off the declaration.
   After the fold they are still read off the declaration — the body
   shape is the kind — so the partition is unchanged. But it is now
   read off a body rather than a keyword, and that is a place to be
   careful.
3. **`model F in Base = <program>` where the program is not a single
   word.** `functor Both = metered ; circuitry` is recommended today as
   a named def; the model form makes `model Both in Base = metered ;
   circuitry` look writable. It is — `;` composes — but then the
   content test "contains a top-level `=`" is doing more work than a
   reader expects. Recommend allowing it and documenting the test.
4. **`:defs` and `:doc` renderings** need one line each and are the
   only user-visible output that changes. Pin them in tests before the
   fold, not after.
5. **Does anything want `model R in Doctrine` with a written body?** A
   resource whose `compose`/`embed` are hand-written is exactly
   `prob.braid`'s `Samp`, written by hand today as an ordinary theory
   and model. If the fold makes `model R in Doctrine = Ty` a shorthand
   for that, the long form should still be writable and the short form
   should say it is a shorthand.
6. **The date.** Every retirement so far has been refused by name
   forever. Two more entries is cheap; a third and fourth *category* of
   retirement message is not free to read. Worth deciding whether
   retired keywords ever graduate to "unknown word".

---

## What this is NOT proposing

- No change to `in`, `with`, receipts, routing, transport or any
  message the checker prints today.
- No change to what is CHECKED anywhere. `checkFunctorWord` keeps its
  job and its timing; `checkBaseInstance` keeps its; the resource
  generation keeps every line it writes.
- No new punctuation, no new position-sensitive clause, and no parsing
  word — direction 3 rules those out permanently.
