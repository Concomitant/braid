# Design note: metaprogramming (machines → paths → compilers) — POSITION TAKEN, NOT SCHEDULED

From the 2026-08-05/06 discussion. Status: design position, no
implementation planned yet. Answers the "Typed splice is future work"
hole in spec-code.md; depends on design-effects.md's result that Braid
is already an arrow, and does not supersede it.

The thread that produced this: `evalCode`'s `ρ2` is free, so a lying
context is not caught — a live REPL session printed `stack: 2 : •`, a
value and its own type disagreeing. Two patches were tried and
discarded (a witness-passing typed splice; a sealed dynamic region)
before the right question arrived: *we have the exponential `Fn⟨Γ ⇒ Δ⟩`
— why not typed code, with Braid's own rules as its indices?* Then:
*what is Forth's compilation process, mathematically, lifted to Braid?*
Those two answers organize everything below.

## 1. Every word is a little machine; the type is its connector

A word is a morphism `Γ ⇒ Δ`: a box with typed input and output ports.
Two ways to combine them, and only two — end to end (`>>`) and side by
side (juxtaposition). That is the string diagram, and it is the whole
combinatorial content of the language.

| kind | machine |
|---|---|
| prim | irreducible — a **generator** of the free category |
| def | a named composite: machines already wired together |
| stage | a **parallel bank** (tensor) |
| path | a **chain** of stages (composition) |
| quote / `Fn⟨…⟩` | a machine **in a box**, passed as a value, opened by `apply` |
| row | a **router**: runs one sub-machine per incoming track |

The difference from Forth is entirely in the connectors. Forth is
untyped, so every word is `Stack ⇒ Stack` — **one universal
connector**. Anything plugs into anything, which is Forth's power and
its whole class of runtime failures. Braid's connectors are shaped, so
mismatched machines do not plug in at all.

## 2. The lift: Forth is a one-object category

**A category with one object is a monoid.** Forth is untyped, so it has
one object, so its threaded code is the **free monoid** on its word
set, and compilation is a fold:

    compile = foldl append nil . map lookup

Because there is one object, *any two words compose*. The fold is
**total**. That is precisely why Forth needs no typechecker:
typechecking asks "do these two morphisms compose?", and with one
object the question is vacuous.

Braid has **many** objects — the stack types. Lift the same fold from a
monoid to a category and one thing changes:

    compile = foldM snocPath emptyPath

The fold is now **partial**, and its partiality is exactly the type
error.

> **Typechecking is not a separate pass. It is the partiality of the
> compile fold.** Replace the monoid with the category and the checker
> appears; you never write one.

| Forth | Braid, lifted |
|---|---|
| one object (the untyped stack) | many objects (stack types) |
| threaded code = free **monoid** | `Path` = free **category** on the quiver |
| compile = `foldl append` (total) | compile = `foldM snocPath` (**partial → the checker**) |
| `:` … `;` | `emptyPath` … install in the dictionary |
| inlining = splice the callee's list | `appendPath` — same move, checked at the seam |
| `IMMEDIATE` word patches the accumulator | a **type-preserving** `Path(Γ,Δ) ⇒ Path(Γ,Δ)` |
| `IF`/`THEN` backpatching addresses | unnecessary — rows and sums are semantic |
| `SEE` | `erase` then `unparse` |
| `'` / `EXECUTE` | quote / `runPath` |

The `IMMEDIATE` row is the one that pays. Forth extends its compiler by
letting words run at compile time and scribble on the accumulator — the
mechanism that makes Forth's compiler user-extensible, and the one
where a wrong address corrupts the dictionary. The lifted version is an
ordinary typed endomorphism (§5): same power, checked.

## 3. What a compiler looks like

    source text
      ↓  parse                       (exists: Str ⇒ (Code | Str))
    untyped Code — the spine, a list of stages
      ↓  foldM snocPath emptyPath    ←—— THIS IS THE TYPECHECKER
    Path(Γ,Δ) — assembled, typed, runnable
      ↓  type-preserving passes
    Path(Γ,Δ)
      ↓  runPath          or         emit (unparse / a backend)

**The interpreter and the compiler share the entire front end.** They
differ only in the last step: run the path, or print it. That falls
straight out of the lift, and it is the cleanest reason to want `Path`
at all.

Two passes worth naming now:

- **Flatten to generators.** Inline every def until only prim atoms
  remain. Legal because the spine is quotiented by associativity of
  composition (spec-code.md), and type-preserving, so it belongs to the
  safe class. The output is a pure diagram of generators — what a
  circuit backend, or a GLA analysis, actually wants.
- **A debug build is a compiler flag.** `compile` and `compileDebug`
  differ only by inserting `trace : a ⇒ a` (dup, print one copy) at
  wire boundaries. Because `trace` is type-preserving, inserting it
  anywhere preserves the program's type: checked once, correct
  everywhere.

## 4. Slice, dice, recombine — exactly three dimensions

A string diagram admits cuts in three directions, and that is all:

1. **Along the chain** — between stages. Prefix and suffix.
2. **Across the wires** — between atoms in one stage. And `f g ≡ f _ >>
   _ g` is the **interchange law**, so identity padding converts a
   vertical cut into a horizontal one: one mechanism covers both. It is
   licensed exactly on the central (pure) fragment, because interchange
   is what premonoidal categories lack for effectful maps
   (design-effects.md). *Which cuts are legal* and *which maps are
   central* are the same question.
3. **Into the boxes** — `reflect` opens a quoted machine.

Recombining: `appendPath` (sequential, checked at the seam), tensor
(limited — §6), quoting (box a path back into a value), and
substitution (replace a sub-path by one of identical type).

The asymmetry between cutting and splicing is **categorical, not a
Braid limitation**: in any category composition is total, but
*factorization is not canonical* — nothing determines where to split a
morphism, or what the intermediate object should be. So splicing in is
typed and free; cutting out is not. The data survives, though — a
`Path` still carries its spine — so a cut can return **erased** pieces:

    splitPath : Int Path(Γ,Δ) ⇒ (Code Code)

which typechecks today. Cut, transform on `Code`, re-check to re-enter.

## 5. The structure, named — and why it is constructible

Paths through a directed graph (a quiver) are exactly the **free
category** on it: objects are stack types, edges are tensor stages. In
programming the same structure is a **type-aligned sequence** — a list
whose consecutive elements' types must line up (van der Ploeg &
Kiselyov, *Reflection without Remorse*, ICFP 2014).

One correction worth recording: this is the free **category**
(equivalently, the free **arrow**), not the free *monad*. A monad's
bind hides the remainder of the program inside a function, so it cannot
be inspected; arrow composition is first-order and therefore reifiable
as data. That is the whole reason this works — see VanDomelen et al.,
*Freer Arrows and Why You Need Them in Haskell* (Haskell Symposium
2025, arXiv:2506.12212): freer monads are not amenable to static
analysis, freer arrows are. It is also, retroactively, an argument for
the arrows-over-monads choice in design-effects.md on a ground that
note did not claim — **analyzability**.

`Path(Γ,Δ)` is today's `Code` with the composition discipline lifted
into the type; `Code` is what erasing the indices gives back.

**The key move:** the intermediate type is existential only when you
take a path *apart*. Building never needs it, because composition
*shares* the join point between two arguments — ordinary unification
against a prenex universal:

    emptyPath  : • ⇒ Path(Γ, Γ)
    snocPath   : Path(Γ,Δ) Stage(Δ,Ε) ⇒ Path(Γ,Ε)      # Δ shared
    appendPath : Path(Γ,Δ) Path(Δ,Ε) ⇒ Path(Γ,Ε)       # the linker
    runPath    : Path(Γ,Δ) Γ ⇒ Δ                        # total — no railway
    erase      : Path(Γ,Δ) ⇒ Code                       # always safe

Every one of those is expressible with the `Forall` Braid already has.
Note what `runPath` does *not* have: a free stack variable. The
`evalCode` hole is not checked away, it becomes unwritable.

What is not expressible:

    unconsPath : Path(Γ,Δ) ⇒ ∃Μ. (Stage(Γ,Μ), Path(Μ,Δ))

`Scheme` is prenex-`Forall` only — there is no existential to name the
hidden `Μ`. This is the same wall as `take k`, whose result type
depends on a *runtime value*: that is dependent typing, ruled out in
design-exponents.md ("the type never computes with n, it only
*correlates* occurrences").

So the line is clean, and it is forced rather than chosen: **you can
build, compose, and run a typed path; you cannot take one apart.**
Analysis — cutting, stage-wise `map`, lifting a pipeline into a monad —
stays on erased `Code` behind one checked door. Which is also the
honest statement of the whole area: you cannot guarantee arbitrary code
is well-typed, so you write *typecheck, and if it checks, run it*.
Typed code is what you hold *after* that check, never a promise made
before it.

## 6. Feasibility, against the current source

- **`Path(Γ,Δ)` is cheap.** `TData name [SType]` already unifies
  argwise exactly as `TFn` does, and substitution, `varsOfTy`,
  `substOnce`, `matchAlias` and `showTyA` all traverse `TData` args
  generically — **zero new traversal cases**, against roughly twelve
  hand-written ones if it were a `TFn`-style former.
- It must be a **primitive** type, not a declared one: declarations
  require every parameter to occur in the body, which phantom indices
  violate.
- **No general `tensorPath`.** `Γ1 Γ2` — two open stacks concatenated
  in one stack — trips the splice-split guard, so the typed layer is a
  category with `first` but not `***`. This is the *same wall* as two
  independent open exponent regions, and as the missing `swapN`: two
  unknowns in one stack have no arity to anchor on. Three features
  hitting one wall is evidence the design is coherent, not evidence of
  three gaps.
- **Path values would be monomorphic** — quotes carry no `∀`;
  generalization happens only at `def`.
- Incidental, found while checking: the one-splice discipline does not
  recurse into `TFn`, so `type Hom(g,d) = Fn⟨g d ⇒ •⟩` slips past the
  "ambiguous product split" check. Half-acknowledged already in
  MANUAL.md §8's display-folding caveat.
- Worth one line for context: `evalCode` today already calls
  `inferTermIn` and **discards** the result. The type information
  exists and is thrown away, which is why a typed variant is cheap.

## 7. Bootstrapping

The question was whether an arrow gives more support for writing and
running programs than plain IO. It does: IO supplies read, write and
exec; the free arrow supplies *structure* — incremental assembly with
types checked at every `snoc`, inspection, typed rewriting, then run or
emit.

What is still missing for genuine self-hosting, stated plainly: a
Braid-hosted typechecker needs the **type language reified as ordinary
Braid data** (`Ty` and `Arrow` as declared types), which is a further
layer this note does not attempt. And a verdict computed *in Braid* is
evidence the host cannot verify — acting on it is the checked door
again. `Path` moves the boundary; it does not remove it.

## 8. Recommendation and staging

A `Path` spike is small — the type former is nearly free (§6) — and
would test the central claim, *that the compile fold's partiality is
the typechecker*, against real programs. A Braid-in-Braid interpreter
is a much larger lift and should wait until `Path` has earned its keep.

1. `Path(Γ,Δ)` primitive type + display.
2. `emptyPath` / `snocPath` / `appendPath` / `runPath` / `erase`.
3. `compileTo` — the fold — plus the debug-build variant.
4. The type-preserving kit: substitute-same-type, `trace` insertion,
   padding normalization, flatten-to-generators.
5. Reified `Ty` → a Braid-hosted checker.

Each stage is independently useful. Stage 2 alone closes the
`evalCode` hole for everything built compositionally; stage 3 is the
first real payoff; stage 5 is the bootstrapping tier.

## 9. Open questions

- Does the checked door take a witness quote, or read its expectation
  from the context?
- Is running a path effect-graded once effects land? design-effects.md
  already lists "Code⟨⟩ reflection of elaborated (wire-threaded) code"
  as open — this connects to it and does not pre-empt it.
- Does `Path` subsume `box`, whose type is currently derived from
  `evalCode`'s free `Δ`?
- Is `loop` reifiable in a free arrow? The freer-arrow literature
  suggests only fixed-iteration loops reify without additional
  datatypes; Braid's Elgot `loop` may need the same treatment.
- Do monomorphic path values bite in practice, or is `def`-level
  generalization enough?
