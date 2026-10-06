# The manifest as an ordered chain, with declared commutation

*Worked out 2026-10-05, between the author and the lead, from three
tabled items: the universal reading of a functor label, the commuting-functors
check, and "requiring both labels".*

**Not to be built now.** The standing decision is to use the language as it is
for a while first, and to reopen this only if `=Metered>` under-counting, or
an ambiguity about which order two functors were applied in, actually hurts.
This file records the design precisely enough to build from, and the price
plainly enough to decide against.

Every claim about current behaviour is marked `(REPL)` or `(code)`; the REPL
runs are 2026-10-05, Docker `haskell:9.4-slim`.

---

## 1. The problem, verified

### 1a. The label unions; the action does not propagate

A functor label is minted by a scope and travels by composition. The action
the functor performed does not travel with it. One `Fuel` resource and one
`Metered` interposing functor, as `examples/metered.braid` writes them, with
`g` metered and `f`, `h` bare:

```braid
def g with Fuel Metered = dup ; *
def f = _ 1 ; +
def h = _ 2 ; *
def base  = f ; g ; h
def outer with Fuel Metered = f ; g ; h
```

All three carry the same manifest, and the fuel counts differ (REPL):

```text
braid> :t g
g : Int ρ0 =Metered Fuel> Int ρ0
braid> :t base
base : Int ρ0 =Metered Fuel> Int ρ0
braid> :t outer
outer : Int ρ0 =Metered Fuel> Int ρ0
braid> (10 ; Fuel) 5 ; base ; _ print ; unFuel ; print
72
7
braid> (10 ; Fuel) 5 ; outer ; _ print ; unFuel ; print
72
3
```

`base` burns three, one per cut inside `g` plus the claim stage `with Fuel`
writes. `outer` burns seven, because the outer scope meters its own spine too
and `g` is one atom in it. Three burns against seven, one manifest: a reader
who takes `=Metered>` to mean "every cut burns" is wrong by four units.

### 1b. What today's label means, and why it unions

A label says **some part of this went through F**. `MANUAL.md` §3 puts it as
"this scope changed this code", and the grade is a set in the join-semilattice
`(P(labels), ∪, ∅)`, so composition unions. The union is forced. The manifest
amendment of 2026-09-29/30, recorded 2026-10-05 in "The manifest, stated
once", says why: an effect label names the **complement** of an image claim,
"I cannot promise this is in the image of the inclusion". Membership in a wide
subcategory intersects, because both parts in implies the composite in, and by
De Morgan the complement of an intersecting property is a unioning one. A
universal reading cannot ride the same set, which is the intersection half,
open since 2026-08-31.

### 1c. The order is lost, and one order does not type

Two interposing functors, `Metered` and the `Ticked` of
`examples/traced.braid`, applied to separate defs and composed in the base
(REPL):

```text
braid> :t both                 -- m ; t
both  : Int ρ0 =IO Metered Ticked Fuel> Int ρ0
braid> :t bothR                -- t ; m
bothR : Int ρ0 =IO Metered Ticked Fuel> Int ρ0
```

Two different programs, identical types. The display order carries no
information: `arrowBetween` renders `S.toList (eLabels e \\ folded) ++
folded`, so the unfolded part comes out in `Set` order and the folded carrier
names are appended in carrier order (code, `:5270`), which is what `MANUAL.md`
§3 means by "in any order, displayed sorted".

Order is not merely lost. In one header, one of the two orders is refused
today, for reasons the manifest never shows (REPL):

```text
braid> :import "/t/c10.braid"     -- def tm with Traced Fuel Metered = dup ; *
error: /t/c10.braid:8, in def tm: Cannot unify types: Str vs Fuel
  `Fuel` is a resource, so the code on one side of this was ROUTED for
  it and says so. ...
```

`with Fuel Metered Traced` elaborates and runs, and its trace output names
`burn` at three of the six cuts it printed (REPL).

### 1d. The two tabled items this resolves

The **universal reading** ("every cut") is the coeffect half, recorded open in
the coeffect section of `design-macros.md` and in `design-7b.md` §8; the chain
is that claim, if the leaf check holds (§2k). The **commuting-functors check**
is the functor-interaction question parked at
Gaboardi–Katsumata–Orchard–Breuvart in `READING.md`; it becomes a declared
commutor with a naturality square. `design-7b.md` §8 also lists "Order in the
grade (typestate, traces)" as explicitly out, naming Tate and Gordon for a
future product component, under the constraint "provenance never becomes
non-idempotent". A chain keeps that constraint: no label repeats (§6e).

---

## 2. The design

### 2a. The manifest is a chain

A manifest is a **chain**: the functors on the arrow, in the order they were
applied, identity first. `Fuel Metered` means `Fuel` was applied to the
written program and `Metered` to the result; the empty chain is the pure
arrow. Display is in application order and nothing is sorted, so today's
`Set`-order display (§1c) and `MANUAL.md` §3's "displayed sorted" both go.

### 2b. Lifting is appending

A chain `L` lifts canonically to a chain `M` **iff `L` is a prefix of `M`**,
and the lift is the application of the remaining functors. The empty chain is
a prefix of every chain, so pure code flows anywhere, which is the
subeffecting `MANUAL.md` §3 already has. Prefix, not subset, because
application is not insertion: `F₁F₃` cannot be lifted to `F₁F₂F₃`, since `F₃`
was applied to the `F₁`-program, its image is fixed, and there is nowhere to
put `F₂` underneath it. Subset order would claim a lift no program realizes.

### 2c. Commutors are declared

A **commutor** is a natural transformation `c : F ∘ G ⇒ G ∘ F`, required to be
an iso. It has one component per object and one square per generator:

```text
(F∘G)(g) ; c  =  c ; (G∘F)(g)
```

Proposed syntax, a `transformation` whose head names a chain:

```braid
transformation MeteredLog in Metered Log ⇒ Log Metered = swap
```

Nothing commutes by default. With a commutor in scope, `Metered Log` and `Log
Metered` are two manifests of one program and each may stand for the other.
Both halves of that head are new. Today the parser takes exactly three tokens
after `in`, one model name on each side of the arrow
(`parseTransformationLine`, code, `:7845`), and both must be models of one
theory (`transformationDefs`, code, `:7883`). There is also no prelude word
`sym` (code): the swap on two wires is `swap`, `∀ a b. a b ⇒ b a` (code,
`:5879`).

### 2d. Subset lifting, through commutors

To lift `F₁F₃` to `F₁F₂F₃`: append `F₂`, giving `F₁F₃F₂`, then commute `F₂`
past `F₃`, which needs the commutor `F₃F₂ ≅ F₂F₃` and nothing else. The
general rule: **append the missing letters, then commute each past the letters
it must pass; the lift exists iff every commutor it needs has been declared.**
Today's subset order is this rule with every commutor present.

### 2e. What the manifest is

A manifest is a **Mazurkiewicz trace**: a word over the alphabet of functor
names, modulo the declared commutations. Two degenerate cases bracket it.

Everything independent gives the free commutative monoid, which with
idempotence is a set, which is today's grade. Nothing independent gives the
free monoid, a word, a bare application sequence. Declared pair by pair gives
a trace monoid, which is this design. Mazurkiewicz, *Trace theory* (1986), is
the source for the monoid and its normal forms, and §3 gathers the citations.
`READING.md` already uses "trace" for a trace on a traced monoidal category
(Hasegawa, line 75), so a Mazurkiewicz trace gets its full name every time.

### 2f. Composition

To compose `f : Σ =L> Θ` with `g : Θ =M> Ξ`: lift both to a common extension
and compose there. A common extension exists iff the two chains agree on their
shared prefix and every letter they disagree on commutes past the letters it
must pass. Where it exists, the composite carries the **universal** reading
for free, because the lift is the application: the letters appended to `L`
really did run over `f`. Where none exists, composition is **refused**, naming
the pair and asking for an explicit order. `Metered` then `Traced` against
`Traced` then `Metered`, with no commutor declared, is the case. That refusal
is "requiring both labels", and it arises where the two orders are different
programs and nowhere else.

### 2g. Which pairs commute for free

| pair | commutor | by |
|---|---|---|
| resource with resource, or resource with anything | free | routing pads, and `swap` swaps the pads |
| `IO`, anything | free | `IO` is a product with a carrier nobody writes (`MANUAL.md` §3) |
| `Recursive`, any graph morphism | claimed free | transport of recursion, `F(fix b) = fix (F b)` |
| `Recursive`, any resource | claimed free | the same |
| any other pair | declared or nothing | one `transformation` per pair |

The free ones are declared once, in the prelude, so a sweep does not ask every
module to restate them. **The `Recursive` claim is weaker in the record than
stated above.** In `design-macros.md` the law `F(fix b) = fix (F b)` is
"*statable* ... but it is not stated: that is a law in `theory Functor`, and
it is 5b" (`:1476`), and it is "decided when the body does not call itself ...
still syntactic when it does" (`:1891`). It is not recorded as holding by
construction for every by-generators functor. Treating `Recursive` as an
independent letter therefore rests on future work: either 5b lands first, or
the prelude commutor is declared and sampled like any other.

The "innermost" elaboration of `Recursive` is also not only a convenience.
`elabHeaders` says "`Recursive` first, and INNERMOST ... so every other scope
on this header ... sees the tied knot rather than a name that is not in scope
yet" (code, `:6869`). Its position is fixed by name resolution and its
independence by the transport law, which are two facts.

### 2h. Algebras are the way back down

An **algebra** for `F` is a natural transformation `F ⇒ Id`. Proposed syntax,
with `Id` as a target, which the parser does not accept (code, `:7845`):

```braid
transformation Unmeter in Metered ⇒ Id = dropFuel
```

Its square is `F(g) ; ε = ε ; g`, Dantas–Walker harmlessness, already in the
record: "for a functor `F` with discharge `ε : F(Σ) ⇒ Σ`, naturality `F(p) ; ε
= ε ; p` says stripping the instrumentation changes no value. It holds for
`Metered` with `ε = drop the fuel`" (`design-macros.md:1902`).

| letter | its algebra | exists? |
|---|---|---|
| a resource | its handler, `seed ; … ; unwrap` | yes (`examples/resources.braid`) |
| a Doctrine model | its exit, `observe` / `runP` | yes, as a theory slot |
| an interposing functor | this construct | no |
| `IO` | none by design; the linear `World` has no `unWorld` (`MANUAL.md` §3) | no, structurally |
| `Recursive` | none in general; unknotting is a termination proof | no |
| a model receipt | none; you cannot un-substitute | no |
| `Traced`, while its prints are `IO` | none; routed into a `Log` resource it would have one | no |

**The concrete bug this fixes.** `Metered`'s algebra is `Fuel`'s discharge.
Today, discharging `Fuel` strips the carrier from the stacks and leaves the
label on the row (REPL):

```text
braid> :t! collectFuel
collectFuel : Fn⟨Fuel ρ0 ⇒ Fuel ρ1⟩ ⇒ Fn⟨ρ0 ⇒ Int ρ1⟩
braid> :t ranG                 -- [g] ; collectFuel, g with Fuel Metered
ranG : • ⇒ Fn⟨Int ρ0 =Fuel Metered> Int Int ρ0⟩
braid> :t! [square] ; collectLog           -- examples/resources.braid
[square] ; collectLog : • ⇒ Fn⟨Int ρ0 =Log> Str Int ρ0⟩
```

Both handlers' declared result arrows are pure, and both applied results carry
the label. `Fuel Metered` over-claims twice: no `Fuel` wire crosses that
arrow, and nothing downstream can be metered. So "the arrow loses the label
across it" (`MANUAL.md` §5, near line 5129) is true of a handler's signature
and false of its application. Under the chain, discharge pops the letter and
the over-claim goes with it.

### 2i. Discharge is a pop

A handler removes the **last** letter of the chain. Reaching a letter in the
middle requires commutors to move it to the top first: the chain is a stack of
functors and commutors are the only access below the top. Three operations,
and no others:

| operation | what it does | needs |
|---|---|---|
| append | lift | nothing |
| pop | discharge | an algebra for the last letter |
| commute | reorder | a declared commutor for the adjacent pair |

### 2j. The order-matters refusal, worked

Two headers, the same functors, opposite order. **`with Traced Fuel Metered`,
then discharge `Fuel`.** The chain is `Traced Fuel Metered`. `Fuel` and
`Metered` commute, so `Metered` reaches the top:
`Traced Metered Fuel` by one commutor, then `Unmeter` pops `Metered` and the
handler pops `Fuel`. The result is `=Traced>`. The trace was taken of
un-metered code, and un-metered code is what it printed, so the remaining
claim is true.

**`with Fuel Metered Traced`, then discharge.** The chain is `Fuel Metered
Traced`. `Traced` sits above `Metered` and no commutor between them has been
declared, so `Metered` cannot reach the top. Discharge is **refused**. It has
to be: the trace recorded the burns, the printed output names `burn` at every
cut, and discharging the meter would leave a `=Traced>` arrow whose output
lies about the program that remains. One pair of functors, one commutor
missing, two opposite verdicts, and the reason is checkable against the
printed output.

**Note on today's behaviour.** The good order above is the one that does not
elaborate today, and the refused order is the one that works (§1c, REPL).
`with Traced Fuel Metered` fails with *Cannot unify types: Str vs Fuel*,
because `Traced`'s inserted stage is built and padded before `Fuel`'s routing
has put the wire underneath it. So this example is not a regression test. It
says what the chain would make of two orders, one of which the elaborator
cannot build at all until that padding-against-routing interaction is sorted
out. That is a cost item, listed in §4.

### 2k. The leaf check, and the bottom-up cost

A scope applies its functors to **this def's spine**, and a called def is an
atom in that spine. So `with Metered = f ; g` burns around `g` and not inside
it, which §1a measures: three burns inside `g`, four more around the outer
spine, seven in all. The universal reading is therefore a lie unless every def
the scope calls already carries the chain. The **leaf check**: a scope mints
its chain only if every called def already carries it. Primitives are atomic
and pass. Consequences:

| rule | why |
|---|---|
| lifting at composition is for primitives only | a primitive has no inside, so appending a letter to it is the application |
| a called def must already match | its inside was fixed when it was elaborated, and nothing can be inserted there now |
| you build bottom-up | the innermost def gets the scope first |

This is "intersection must be declared" made concrete, and it is the real
price: a `with` clause on every def in a metered world, and a refusal naming
the def whenever one is missing. The lead's mock of this design, 2026-10-05,
got it wrong in its §3, where `note` was lifted at composition rather than
required to carry the chain already. The plan's record says "The lead's mock
got this wrong."

### 2l. Branching

The two arms of a row need a common extension. Where none exists the row is
refused and the programmer writes the order. This is a **deviation** from
every published sequential effect system: Tate's productors and Gordon's
effect quantales both supply a total join for conditionals, and so does every
graded monad over a semilattice. Here the join is partial, and principal types
are given up at the non-commuting branches, deliberately, because a total join
at a branch is what produces a label claiming an order neither arm ran in.

### 2m. Parallel

A tensor stage `f g` is `(f ⊗ id) ; (id ⊗ g)` in a premonoidal category (Power
& Robinson, `READING.md` line 9), so it is a composition, follows §2f and the
left-to-right decree, and needs no new rule.

---

## 3. What it is, in PL terms

A **sequential effect system** graded by a trace monoid whose independence
relation is declared.

| element | the literature | in `READING.md`? |
|---|---|---|
| order in the grade | Tate, productors (POPL 2013); Gordon, flow-sensitive effects (ECOOP 2017) | yes, lines 119 and 125 |
| grading by a preordered monoid | Katsumata (POPL 2014); the prefix order on traces is one | yes, line 97 |
| the trace monoid and its normal forms | Mazurkiewicz, *Trace theory* (1986) | no |
| grading by a monoidal **category**: chains are objects, liftings and commutors are morphisms | Fujii, Katsumata & Melliès (FoSSaCS 2016) | no |
| a commutor as a distributive law | Beck, one pair at a time | no |
| sum of theories by default, tensor on declaration | Hyland, Plotkin & Power, *Combining effect theories* | no; Plotkin & Power and Power & Robinson are there, the sum/tensor paper is not |

The four absent entries would be added. Tate's present entry already
anticipates this file: "The reference for a NON-commutative grade (traces,
typestate), which Braid would add as a product component, never by making
provenance non-idempotent." A chain is non-commutative and still idempotent,
because a letter never repeats. Contrast with Koka (Leijen, `READING.md` line
90), the other arrangement: distinct labels always commute, repeated labels
keep their order. Here nothing commutes until declared, and a label never
repeats, because a non-commuting pair can only coexist as a named composite
functor. `design-macros.md:275` gives that advice already for another reason:
a second `interpose` instruments the first's insertions, so "compose markers,
not interpositions, when the product is meant".

---

## 4. The cost, measured

Line numbers are `src/MiniConcatTypechecker.hs` (14,269 lines).

| piece | what changes | size today |
|---|---|---|
| representation | `data EffRow = Eff { eLabels :: Set String, eTail :: Maybe EVar }` (`:88`) becomes a list | 18 mentions of `eLabels` at 12 sites, plus `effPure`/`effIO`/`effLabel` (`:185`–`:193`) |
| unification | `unifyEff` works by `S.\\` and `S.union` (`:1094`, `:1111`), `bindEffVar` by `S.null (eLabels row)` (`:1230`); both need prefix matching modulo commutation | 63 lines (`:1082`–`:1144`) plus 17 |
| subsumption | `CSubEff part composite` (`:496`) becomes prefix-with-commutation; `fixSubs` (`:1346`–`:1365`) must detect "no common extension" and refuse instead of growing by `missing = lp S.\\ lc` | 20 lines inside a 52-line `solve` |
| the bridge | `keepSubs` walks the constraint graph accumulating `ls' = ls S.union lc` (`:8384`–`:8406`) | 23 lines |
| display | `arrowBetween` (`:5270`) and `arrowGlyph` (`:361`) render in application order; the carrier fold in `showArrowA` (`:5289`) keeps working | 8 lines, plus the pins |
| elaborator | `elabHeaders` must respect header order within a kind and record the order it used; today the order is actions, "renames, then routes, then composes, then rewrites" (`:6890`), which is why `with Metered Fuel` and `with Fuel Metered` behave identically (REPL) | 266 lines (`:6839`–`:7104`); `runFunctor` is 17 |
| the leaf check | new: every called def's chain compared against the scope's | new |
| `transformation` | chains on both sides, `Id` as a target | parser 29 lines (`:7839`), checker 194 (`:7880`–`:8073`) |
| discharge | pop with an algebra, and the refusal when the letter is not on top | new |

**The hard part is unification and subsumption modulo commutation**:

| sub-problem | status |
|---|---|
| normal forms for traces (Foata normal form, or lexicographic normal form w.r.t. the independence relation) | well understood; trace monoids have decidable word problem and computable normal forms |
| the prefix order on traces, and least common extension | well understood |
| all of the above against an **open tail** `eTail :: Maybe EVar` | not understood; a tail stands for an unknown suffix, and prefix-with-commutation against an unknown suffix is where a solver either loses principality or loops |
| the existing bridge (`keepSubs`, two open rows each carrying a label the other lacks, joining through a residual) | not understood; the bridge is built on union, and a partial join has no union to bridge through |

**Pin churn.** Across `examples/*.braid`, `test/Tests.hs` and the comments in
`src/`, 27 distinct multi-label arrow shapes occur, 126 occurrences counting
the `.md` files. Nineteen lines of `test/Tests.hs` pin an exact type string
with two or more labels, from `:850` to `:1597`. Every one moves, because
sorted order becomes application order.

**Backward compatibility.** Every pair that works today must get a commutor or
the sweep breaks. The pairs that occur on an arrow in `examples/`, `test/` or
`src/`:

| pair | kinds | verdict |
|---|---|---|
| `Log Counter` | resource, resource | free commutor |
| `Log GameState`, `IO GameState`, `IO Log`, `IO Counter`, `Dict IO` | resource with resource or `IO` | free commutor |
| `Metered Fuel` | functor, resource | free commutor; the chain's point is that the order is now visible |
| `RevThread Gradient` | model, resource | free commutor |
| `IO Recursive`, `Recursive Same`, `Recursive Traced`, `Opt Recursive`, `Fwd Recursive`, `Frame Recursive`, `Circuits Recursive`, `Enum Recursive`, `Sampler Recursive` | `Recursive` with a functor or a model | free **if** the transport-of-recursion law lands (§2g); otherwise nine declarations to sample |
| `IO Same`, `IO Traced` | `IO` with a functor | free commutor, but `IO Traced` is an open question (§6c) |
| `Circuits IO`, `Frame IO`, `Funcs IO`, `Enum IO` | a Doctrine model with a graded carrier, and `IO` | **needs a declaration**, or the graded-carrier fold of stage 11b has to be read as supplying one; audit required |
| `Alpha R` | neither is a declared label; a hand-written type in `test/Tests.hs:1282` | audit; rewrite the pin |
| `R R` | the same label twice, in a hand-written type (`test/Tests.hs`, `src/:5188`, `design-7b.md:34`) | **refused** under a chain; no label repeats. These pins must change |

Counting resources and `IO` as free: 13 pairs cost nothing, 9 hang on the
`Recursive` law, 4 need a declaration or an audit, and 2 pinned shapes become
invalid.

**Overall estimate: a 7b-scale stage**, 1,500 to 3,500 lines changed across
five or six commits, with the test sweep on top. The range is wide because the
risk is not spread evenly: the representation change, the display, the
elaborator's order and the `transformation` extension are mechanical and
bounded by the first table. The uncertainty sits in two places, both named
above, `prefix order modulo commutation against an open tail` and `the
keepSubs bridge once the join is partial`. If those want a different solver
rather than a modified one, the stage doubles.

---

## 5. What it buys, and when to build it

| | what it is |
|---|---|
| **for**: the universal reading | the intersection half, open since 2026-08-31 |
| **for**: the order-matters refusal | today `with Traced Fuel Metered` fails with *Cannot unify types: Str vs Fuel*, which names nothing about order (REPL) |
| **for**: no `=Metered>` after discharge | today `ranG : • ⇒ Fn⟨Int ρ0 =Fuel Metered> Int Int ρ0⟩` after the fuel is discharged (REPL) |
| **for**: explicit order where functors do not commute | today `both` and `bothR` have identical types (REPL) |
| **against**: the bottom-up scope cost | a `with` clause on every def in a metered world |
| **against**: a harder solver | §4, the two unknowns |
| **against**: pin churn | 19 pinned type strings, 2 of them invalid |
| **against**: principal types at non-commuting joins | given up, deliberately (§2l) |

**The standing decision is not now.** Use the language as it is, and reopen
this if `=Metered>` under-counting, or an ambiguity about which order two
functors ran in, ever hurts in practice. Until then the nominal wrapper
remains the documented idiom for "every stage did X", as `design-7b.md` §8 and
`examples/metered.braid`'s comment say.

---

## 6. Open questions

**6a. Is a commutor between a functor and a resource derivable in general?**
The free-commutor claim rests on routing pads: a resource's whiskering is `_`
padding and `swap` swaps the pads. Does padding commute with insertion for
**every** graph morphism? The counterexample to look for is a functor whose
inserted stage reads a wire, which `interpose` already refuses by name; the
question is whether that refusal is the condition for the commutor to exist.
If it is, the prelude declaration is a theorem; if not, "resources commute
with everything" is a claim per functor. §2j's elaboration failure is evidence
that this interaction is not yet understood even without chains.

**6b. What are a commutor's components for a carrier-less functor?** A
carrier-less label's fibre is a marked copy of the base, identity on objects,
so a component is a morphism `a ⇒ a`. Can such a component ever reorder a side
effect? If the only inhabitant is the identity, the square `(F∘G)(g) ; id = id
; (G∘F)(g)` reduces to an equality of spines, and "declare a commutor" becomes
"assert the two elaborations produce the same code", which `sameCode` decides
on the fragment. That is a smaller construct than a transformation, and it
makes the common case checked rather than sampled.

**6c. Should `IO` commute with `Traced`?** For: `IO`'s carrier is a singleton
`World` the elaborator never writes, so there is no wire to reorder and a
commutor's component is forced to be the identity. Against: the two orders
differ in the order of prints, which is what io observes, so calling them
interchangeable lets a composite claim an ordering of output it does not have.
The second argument wins on the semantics and loses on the type system, since
the manifest cannot see print order either way. Likely resolution: `IO`
commutes with every carrier-less functor whose insertions are not io, `Traced`
is not one of them, and `examples/traced.braid` gains a declaration.

**6d. Is the chain the universal set, or a second display?** The chain is the
universal set, if the leaf check holds: every letter in it was then applied to
the whole of this def and everything it calls. Without the leaf check the
chain records one level and needs a second display for "and all the way down".
Build the leaf check or do not build this.

**6e. Are Koka-style repeated labels ever wanted?** Two nested `Log` scopes is
the case. Today the inner and outer receipts are one label; `Log Log` would
say "logged, then logged again", a real distinction when the two scopes seed
different wires. Against: idempotence keeps the grade finite and keeps
provenance from becoming a count, which `design-7b.md` §8 names as a separate
arc. The fallback is the named composite, `functor LogTwice`, as for a
non-commuting pair.
