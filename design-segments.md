# Design note: segment variables — one word for the N-family

*Planning pass, 2026-09-20. No code was written for this note. Every
claim about current behaviour is marked `[REPL]` (verified in the
shipped REPL, docker `haskell:9.4-slim`) or `[code]` (read out of
`src/MiniConcatTypechecker.hs`). Nothing is decided until Daniel says
so. §4 and §6.1 contain the two findings that contradict the brief.*

## 1. The problem, in the language's own terms

The exponent tier has nine prims and none can be written in Braid
`[REPL: `:t` on each]`:

```text
foldExp  : Fn⟨a0 a1 ⇒ a0⟩ a0 a1ⁿ⁰ ⇒ a0          mapN  : Fn⟨a0 ⇒ a1⟩ a0ⁿ⁰ ⇒ a1ⁿ⁰
foldExp2 : Fn⟨a0 a1 a2 ⇒ a0⟩ a0 (a1 a2)ⁿ⁰ ⇒ a0  mapN2 : Fn⟨a0 a1 ⇒ a2⟩ (a0 a1)ⁿ⁰ ⇒ a2ⁿ⁰
dupN     : a0ⁿ⁰ ⇒ a0ⁿ⁰ a0ⁿ⁰                     zipN  : a0ⁿ⁰ a1ⁿ⁰ ⇒ (a0 a1)ⁿ⁰
at       : Fin(n0) a0ⁿ⁰ ⇒ a0                    unzipN: (a0 a1)ⁿ⁰ ⇒ a0ⁿ⁰ a1ⁿ⁰
indicesN : a0ⁿ⁰ ⇒ (Fin(n0) a0)ⁿ⁰
```

Everything above them is already derived `[code: `preludeSrc`]` —
`sumN`, `addN`, `subN`, `mulN`, `scaleN`, `firstTrue`,
`examples/index.braid`'s `argmaxN`. The nine are the floor. At a
**concrete** width a bundle is not a thing at all — `1 2 3 : • ⇒ Int
Int Int` `[REPL]` — so `zipN` at width 3 is a permutation anyone can
write by hand. At a **variable** width nothing is writable, because
all three facts that would let you write it are absent: the width is
erased (MANUAL §13 rule 3, "no runtime tags; the final segment's
actual extent is the witness"); there is no `unExp`, ruled out by name
in design-exponents.md §Stage 4–5 — *"unrolling one layer would need
n = 0 and n = S m to share a scheme — a dependent sum. The fold is the
honest eliminator"*; and there is no head/tail on a bundle, for the
same reason. So the family can only shrink by *generalising its
schemes*. The brief is right about which two schemes do that:

```text
#mapAccum:p,j,k : Fn⟨ρ aʲ ⇒ ρ bᵏ⟩ ρ (aʲ)ⁿ ⇒ ρ (bᵏ)ⁿ     p = |ρ|
#zip:j          : a₁ⁿ … a_jⁿ  ⇄  (a₁ … a_j)ⁿ
```

`mapN` is j=k=1, ρ=•; `foldExp` is k=0; `dupN` is k=2 then unzip;
`indicesN` is ρ the counter and k=2; `at` is a fold that keeps the
selected wire. `at`, `indicesN` and `checkedAt` are **index
introductions**, fenced already by design-indices.md — every
introduction's n must be forced by a relevant input — so they are
primitive by doctrine, not by accident.

Turning a **schema** into a **word** needs the brief's three things.
**(i)** The terminal object as an exponent base: `(•)^n` already
parses and checks in a `type` alias `[REPL]`; bare `•^n` is a parse
error `[REPL: "Expected '|' or ')' in sum type"]`, being fixed
concurrently. **(ii)** A variable standing for a closed segment of
unknown fixed width — this note's subject. **(iii)** `sⁿ = Σ` as a
deferred constraint (§5.3).

## 2. The mathematics

`Aⁿ` is the n-fold power, `Hom([n], A)` in Set, and design-indices.md
makes that the representation: tabulated normal form, flat on the
stack, "a vector with no box". The two exponentials are one operation
at two bases — `Fn⟨Σ ⇒ Θ⟩` is the internal hom, boxed; `Aⁿ` is the hom
out of a finite discrete base, unboxed.

**Why there is no `unExp`.** Unrolling inverts `[n] ≅ 1 + [n−1]`, and
its two tracks carry *different* indices — nil at n = 0, cons at
n = S m — so one scheme would have to quantify the index per track:
`Σ(m:ℕ). …` inside the arrow, a dependent sum, the one thing
design-exponents excludes outright. The fold survives because a fold
out of `[n] ≅ 1 + ⋯ + 1` is a function *out of* a coproduct,
decomposed case by case, and unary successor is exactly enough to
iterate that.

**Why a stack variable is not a segment variable.** Objects form the
free monoid on wire types and `|·| : Obj → ℕ` is the length
homomorphism. A tail variable `ρ` ranges over objects but is *pinned
to the right end of a context* `[code: `SType` is `SEnd | STail SVar |
SCons Ty SType | SExp SType Exp SType`, and `appendS` raises an
`error` — not a type error — on "nothing may follow the open tail"]`.
That pinning is not decoration: unifying `ρ ⊗ s = Σ` for two unpinned
object variables is **word unification in a free monoid**, infinitary
in general, and even `|ρ| + |s| = 2` has three solutions.
Right-anchoring keeps unification unitary, and unitary unification is
what makes principal types exist. `sⁿ = Σ` is the tractable shadow:
with `|s|` a known positive integer it is `|s|·n = w`, one division;
with `|s|` unknown it is finitary — `|s|·n = 6` has four solutions.

**Why the runtime can do what the language cannot.** The evaluator is
untyped — `evalTerm :: EvalM m => RCtx -> RunDefs -> VarEnv -> Term ->
[Value] -> m ([Value], [String])` `[code]` — so it has `length` and
`splitAt`, which the type system refuses itself. But a flat
bracket-free stack marks exactly one boundary, and design-indices.md
states the consequence as a theorem about erasure adequacy: an untyped
evaluator can find a segment boundary in exactly two situations —
**the segment runs to the end of the stack, or the segment is empty.**
Those are the positional rules ("final ⇒ open", "non-final ⇒ n := 0"),
implemented by `instantiateClosed` `[code: `spineExpVars` closes spine
exponents to 0; the same function closes non-tail stack vars to `•`]`.
§6.1 follows from that theorem.

## 3. Design A — a sixth parameter kind, `PSeg`

A segment variable `s` is a **closed** stack of **unknown but fixed**
width. Zero permitted in general; §5.3 shows one place it is not.

```haskell
data TyParam = … | PSeg GVar
data SType   = … | SSeg GVar SType     -- a segment variable, then a rest
```

`SSeg` sits where `SExp` sits, not where `STail` sits. `SExp SType Exp
SType` already carries a `rest`; `STail SVar` does not and cannot,
because `appendS`'s invariant is enforced with `error`. A variable
that may be *followed* by more stack is a new constructor no matter
what else is decided.

**Touch points, by name.** *Declarations*: `TyParam`, `pName`,
`pKind`, `isStackParam`/`isWidthParam`/`isWireParam` plus a new
`isSegParam`, `paramStack`, `lookupParam`, `parseTypeLine`'s
`reclass`/`occurs` pass. *Substitution*: `Vars` becomes a six-tuple
(`varsOfStack`, `varsOfTy`, `varsOfRow`, `varsOfArrow`, `catVars`,
`noVars`); `Subst` gains a sixth map beside `tySub`/`stSub`/`rowSub`/
`expSub`/`effSub`; `apply`, `substOnce`, `occursStack`. *Stack
algebra*: `appendS`, `sexp`, `expandCopies`, `splitStackAt`,
`openTailedS`, `closedArity`, `segArity`, `openVarsS`. *Unification*:
an `SSeg` case in `unifyStack`; `expSplit` defers on an indeterminate
base (§5.3). *Schemes*: `Scheme = Forall [TVar] [SVar] [RVar] [NVar]
[EVar] [EffSub] Arrow` gains `[GVar]` and `[WidthEq]`; `instantiate`,
`instantiateC`, `instantiateClosed`, `instantiateClosedC`,
`generalize`, a `freshSegVarName`. *Display and reflection*:
`normalizeArrow`, `Show SType`, `showSchemeA`, `reprStackV` /
`stackOfRepV` (§5.5).

`PWidth` — the last kind added — touches fifteen sites `[code:
grep]`; `PSeg` touches those plus the `SType` traversals, the larger
half. What it buys is that the kind is *declared*, so the checker
knows at declaration time which variables must become closed. That is
Braid's style — sorts are visible (`...` a stack, `---` a row, a
superscript a width), never inferred from use — and it gives the best
error at the earliest moment: *"`s` is a segment, so it may not be the
tail of a stack"*, at the declaration, not three files later.

## 4. Design B — a stack variable as an exponent base

Relax one check and carry the split as a constraint. The check is
literal and reachable:

```text
type X(a..., n) = (a)^n
error: Exponent base must be a closed segment          [REPL]
```

`[code: `goStackElem`'s `TokCaret` branch tests `openTailedS base`]`.
Unparenthesized `a^n` never reaches it — `goStack` sees the stack
parameter first and refuses with *"The stack parameter 'a' must be the
last thing in its stack"* `[REPL]`; the source states the rule in its
own words, **"a stack parameter is forced into tail position by the
parser"** `[code: `parseTypeLine`]`. So B looks like two edits — drop
`openTailedS base` from the parser, drop `bw == 0 || openTailedS base`
from `expSplit` `[code]` — plus a deferred constraint.

**B's premise is false, and this is the decisive fact.** `mapAccum`'s
type is `Fn⟨ρ s ⇒ ρ t⟩ ρ sⁿ ⇒ ρ tⁿ`: it puts `ρ` *before* `s`. Under B
both are `SVar`s, so building that stack calls `appendS (STail ρ)
(STail s)` — the branch that `error`s `[code]`. No `SType` spells it.
B therefore needs either a new medial constructor (design A's `SSeg`
minus the declared kind) or a rewrite of the tail-only invariant that
`normalizeArrow`, `openVarsS`, `instantiateClosed` and `bindStackVar`
all depend on.

Two smaller problems. `segArity = closedArity` silently returns `0`
for an open base `[code]`, so relaxing the parser sends `SExp (STail
ρ) e r ~ SExp (STail σ) e' r'` into the *pointwise* branch on
`0 == 0` — not unsound, but accidentally so. And `openTailedS`
conflates "has an open tail" with "has indeterminate width" `[code]`;
a segment variable is *closed* and *indeterminate*, a fourth state the
predicate cannot express. Both designs must split it; B has nowhere to
put the distinction, having no constructor.

## 5. Comparison and recommendation

### 5.1 Recommendation: **A**

**The single strongest reason: `STail` is structurally a tail.** The
tail-only invariant is enforced with `error`, not a type error, and
`mapAccum`'s type requires a variable in medial position. A new
`SType` constructor is therefore not A's cost — it is the *shared*
cost of both designs. Once it is paid, declaring the kind is fifteen
more sites and buys declaration-time errors, a printable sort, and a
checker that never guesses whether `ρ` meant "the rest" or "some fixed
amount". B's advertised saving does not exist.

Second, smaller but real: B makes `ρ` mean two things in one grammar.
A user reads `ρ` as *"and whatever else is on the stack"* (`pass : ρ0
⇒ ρ0`, MANUAL §9); under B, `ρⁿ` makes the same letter mean "a fixed
unknown amount", and the readings diverge exactly at a `Fn⟨ρ ⇒ σ⟩`
theory slot. A gives the second reading its own letter.

### 5.2 The adjacency question, answered

The quoted claim — *"two adjacent open stacks are unresolvable — the
unifier picks empty"* — **does not appear anywhere in the repository**
`[verified: grep over every `.md` for "adjacent open" and "picks
empty"; the only hit is design-exponents.md:101, about two adjacent
open *exponents*]`. What the REPL does is stronger and different:

```text
data TwoAdj(a..., b...) = Box(a b)
error: The stack parameter 'a' must be the last thing in its stack   [REPL]
```

**Adjacency is refused by the parser, at declaration time. The unifier
never sees it.** `examples/circuits.braid`'s own comment gives the
reason it boxed its successor, and that is not about unification
either: *"a passenger beside an OPEN stack is unwritable: `...` covers
the top, so nothing can be pushed above it (guide-open-arity.md, Rule
2)."*

**Does A fix adjacency? Representationally yes, semantically no.**
`SSeg g (SSeg s SEnd)` is a legal stack and `SSeg g (SExp … n SEnd)`
is the shape `mapAccum` needs — but unifying `g ⊗ s ~ Int Int` is word
unification with three solutions. A makes the type *writable*, not
*inferable*. **Does B fix it? No** — B cannot write it at all (§4).
The resolution is the one `Circuit` already found: **box the
passenger.** `Box : ρ0 ⇒ Box(ρ0)` `[REPL]`, so `|Box(ρ)| = 1` is known
at declaration time, `ρ` stays an ordinary `PStack`, and two
indeterminate segments never sit side by side:

```text
mapAccum : Fn⟨Box(ρ) a ⇒ Box(ρ) t⟩ Box(ρ) aⁿ ⇒ Box(ρ) tⁿ
```

Boxing the accumulator is not a workaround; it is the determinacy
discipline, and this is the third time the language has reached for it
(`Circuit`, `Frame`'s column store, now this).

### 5.3 When is `sⁿ = Σ` solvable? The precise rule

> An equation `sⁿ = Σ` with `Σ` closed of width w is discharged when,
> and only when, `|s|` is already determined and positive. Then
> `n := w / |s|` if `|s|` divides `w`, and the constraint fails
> otherwise. `|s|` is *determined* when `s` has an occurrence in a
> region that is closed and every other variable in which has a
> determined width — in practice the quotation argument's arrow. If a
> solver round determines no new width and constraints remain, the
> program is refused.

Two corollaries the brief does not state. **A base must be
non-empty**: if `|s| = 0` then `sⁿ = •` for every `n`, so `n` is free
— satisfiable but not *determining*, so not principal. A's "zero
permitted" and "usable as an exponent base" are in tension: zero is
fine for a segment variable in general and refused in base position.
Half-present already — `expSplit` rejects `bw == 0` today `[code]`
under the generic split message; commit 1 gives it its own words. And
**unitary only after determinacy**: `|s|·n = 6` with `|s|` unknown has
four unifiers, so principality means refusing rather than branching.
The constraint is never guessed; it waits, and if it waits forever it
fails, naming the repair — *"the width of the segment `s` is never
determined — give `s` an occurrence outside an exponent (a
quotation's arrow will do)."*

### 5.4 The `[EffSub]` precedent: what carries, what does not

`Scheme` carries `[EffSub]`; `instantiateC` re-emits them freshened at
every use site; `solve` partitions them out and runs `fixSubs` to a
least fixpoint under a counting bound; `residualSubs` and `keepSubs`
extract what the arrow can still talk about `[code]`. Width
constraints follow that **shape** exactly: a field in `Scheme`,
freshening in `instantiateC`/`instantiateClosedC`, a `fixWidths` pass
in `solve`, a residual extractor, a keeper.

What does **not** carry is the reason `fixSubs` may *act*. Effects are
a semilattice — labels under `∪` — so `p ⊆ c` has a unique least
solution and `flow` may grow a grade by exactly what it was missing.
Widths are arithmetic: `|s|·n = w` has several solutions and no order
in which one is least (smallest `n` is largest `|s|`, and conversely).
So `fixWidths` never *solves* a constraint; it only *notices* that one
has become determinate and then checks it — saturation of determinacy
propagation, not a climb to a least upper bound. Termination is
easier: each round either determines a previously-unknown width or
halts, so a no-progress test replaces the `rounds` bound.

### 5.5 What each design does to the TypeRep

Stage 7a added `rep List(TypeRep) WidthRep` (tag 7) and `fin
WidthRep` (tag 8), `WidthRep = lit Int | var Sym Int`, under the rule
*never flatten a variable width into a type* `[code: above
`reprWidthV`]`. Both designs break the same thing, so it is no
discriminator: tag 7's base is `List(TypeRep)`, a list of **wire**
types, and neither `sⁿ` (A) nor `ρⁿ` (B) has a base of that shape. The
base field must become a `StackRep`, or tag 7 must gain a sibling. A
needs one more `StackRep` alternative besides (a segment variable,
beside the open end at tag 5) and a `pKind` entry; B needs the base
widened and then has nowhere to record that the base was a *variable*
rather than a tail — the `openTailedS` conflation again. Either way
this is a **rep-format change to a shipped reflection surface**, with
its own commit and tests (§7 commit 6).

### 5.6 Scope discipline: the narrowest thing that works

**Prim schemes only, for now.** `data` already refuses width
parameters — *"width parameter 'n' is supported on `type` aliases
only, not on recursive/`data` declarations"* `[REPL]` — because
`TData`'s arguments are stacks `[code]`. A segment variable *is* a
stack, so it could ride there; but `Box(s)` and `Box(ρ)` would be a
distinction with no user-visible difference. `theory` parameters kind
their arguments one at a time (`k(..., ...)` is the hom-object, stage
7a); a third spelling there costs syntax and buys nothing until a
theory wants a fixed-but-unknown carrier width, which none does.
`type` aliases already take width parameters, so they are the cheap
second step — after a user program asks.

## 6. What becomes derivable, and what stays primitive

### 6.1 The finding the brief is wrong about

**Nine words do not become three, and the obstacle is erasure, not the
type system.**

`#mapAccum:p,j,k` carries three numbers and the runtime needs two —
`p = |ρ|` to find where the accumulator ends, `j = |aʲ|` to chunk the
bundle. A single word `mapAccum : Fn⟨ρ s ⇒ ρ t⟩ ρ sⁿ ⇒ ρ tⁿ` hands the
final atom **one** observable number, the remaining segment's length
`|ρ| + n·|s|`, and asks it to recover three. Segment variables are
erased exactly as widths are; nothing on the stack witnesses the
split. This is design-indices.md's own theorem (§2), not a new
restriction. The standing proof is in the prim table: **`mapN` and
`mapN2` differ only in a chunk width, and they are two prims for
exactly this reason**, as do `foldExp` and `foldExp2` `[code: each
runtime hard-codes its chunking — `mapN2`/`foldExp2` call `chunk2`,
`zipN` calls `splitAt (length stk `div` 2)`]`. `VFn RunDefs VarEnv
Term` carries no arity `[code]`, so the evaluator cannot read `|s|`
off the quotation either.

| the segment variable is… | the runtime must… | erasure-safe? |
|---|---|---|
| the quote's **output** (`t` in `⇒ ρ tⁿ`) | concatenate what came back | **yes** — free |
| the **accumulator** (`ρ`) | split `|ρ|` wires off the bottom | **no**, unless literal or boxed |
| the **input chunk** (`s` in `sⁿ`) | cut the segment into n chunks of `|s|` | **no**, ever |

Hence, extending design-indices.md's witness discipline one tier up:

> **The segment discipline.** A prim scheme may mention a segment
> variable in any position the untyped evaluator does not have to
> *split*. It recovers a boundary in exactly three situations: the
> segment runs to the end of the stack; the segment is empty; or the
> segment is being **produced**, in which case the evaluator
> concatenates whatever it was handed and never needs the number.

That is checkable on the prim table mechanically — the property that
makes design-indices' rule a well-modedness condition, not a hope.

### 6.2 What actually collapses

With `mapAccum : Fn⟨Box(ρ) a ⇒ Box(ρ) t⟩ Box(ρ) aⁿ ⇒ Box(ρ) tⁿ` and
its chunk-2 twin `mapAccum2 : Fn⟨Box(ρ) a b ⇒ Box(ρ) t⟩ Box(ρ) (a b)ⁿ
⇒ Box(ρ) tⁿ` — `Box` one wire, `a`/`b` wires, **`t` a segment variable
in output position only** — five prims become two:

```braid
## PROPOSED — none of these can be checked until commit 5 exists.
def foldExp  = (f b -> b Box ... >> [(s x   -> s (x   f ... >> ev))] ... >> mapAccum  >> unBox)
def foldExp2 = (f b -> b Box ... >> [(s x y -> s (x y f ... >> ev))] ... >> mapAccum2 >> unBox)
def mapN     = (f   -> • Box ... >> [(s x   -> s (x   f ... >> ev))] ... >> mapAccum  >> (b ... -> pass))
def mapN2    = (f   -> • Box ... >> [(s x y -> s (x y f ... >> ev))] ... >> mapAccum2 >> (b ... -> pass))
def dupN     =         • Box ... >> [(s x   -> s x x)]               ... >> mapAccum  >> (b ... -> pass) >> unzipN
```

`foldExp` is clean: `t := •`, so the output bundle is empty and the
box lands on top. The other four are the sharp edge — the box sits
**beneath an open bundle**, exactly the "passenger beside an open
stack" problem, and only an open binder can reach it (§8 R4).

**`zipN` and `unzipN`** stay primitive: pure rewiring at chunk width
2, and not an instance of `mapAccum` at any instantiation, because
`mapAccum` walks one chunk at a time and cannot correlate two bundles.
Binary `zipN` does **not** iterate to ternary — `(a b)ⁿ cⁿ ⇒ (a b c)ⁿ`
needs a base of width 2 on the left and `zipN`'s base is a wire
`[REPL: `1 2 3 4 >> zipN >> zipN` typechecks and is the identity; the
second `zipN` is a non-final atom closed to n := 0, not a re-zip]`. The
brief's "higher arities derive by iteration" is true of the *flat
product* (`((s t) u)` is `(s t u)`) and false of `zipN`. **`at`,
`indicesN`, `checkedAt`, `weaken`, `finInt`** stay primitive as index
introductions; `indicesN` produces a `Fin(n)` mentioning the bundle's
own width, which no user quotation can introduce.

Score: **nine prims become six** (`mapAccum`, `mapAccum2`, `zipN`,
`unzipN`, `at`, `indicesN`), with `mapN`, `mapN2`, `foldExp`,
`foldExp2` and `dupN` joining the eight words already derived.
Nine→three needs the width channel §9 puts out.

## 7. Staging

Six commits. Each green, each leaving the language usable, each with
its own byte-identical audit.

1. **The zero-width base, refused with a reason.** `expSplit`'s
   `bw == 0` arm gets its own message; the concurrent `•^n`
   relaxation lands with a test that `(•)^n` and `•^n` agree. One new
   refusal string, no type changes.
2. **`SSeg` in the representation, unreachable.** `SType`, `TyParam`,
   `Vars`, `Subst`, `appendS`, `sexp`, `openTailedS` split into
   closed-vs-determinate, `normalizeArrow`, `Show`, `showSchemeA`. No
   parser route reaches it and no prim uses it, so **every displayed
   type is byte-identical** and the whole suite is the test.
3. **Unification, and the constraint carrier.** An `SSeg` case in
   `unifyStack`; `expSplit` defers rather than refusing on an
   indeterminate base; `Scheme` gains `[WidthEq]`; `solve` gains
   `fixWidths`; `instantiateC`/`instantiateClosedC` freshen them;
   residual/keep analogues. Unification tests only, in the style of
   the 14 the exponent stage added.
4. **The segment discipline, as a check.** The well-modedness test on
   prim schemes (§6.1) over the existing table, which passes
   vacuously, plus its refusal. Landing it before 5 stops 5 cheating.
5. **`mapAccum`, `mapAccum2`, and the collapse.** Two prims, their
   runtimes (concatenate the quote's whole output), five prelude defs.
   **The audit is that `:t mapN`, `:t mapN2`, `:t foldExp`,
   `:t foldExp2` and `:t dupN` print character-for-character what they
   print today**, and that `gla.braid`, `index.braid`,
   `registrar.braid`, `tag.braid`, `ladder.braid`, `guards.braid` and
   `transpose.braid` produce byte-identical output.
6. **The rep, and the docs.** `reprStackV`/`stackOfRepV` learn the
   segment alternative and the widened `rep` base; MANUAL §5's sort
   table gains a row, §9's prim table loses five rows and its derived
   table gains five, §13 states the segment discipline; CONSTRUCTS.md;
   amendments to design-exponents.md (open question 5 answered) and
   design-indices.md (the same rule, one tier up).

## 8. Risks, and the byte-identical audit

The bar is that every example's printed output and every `:t` in the
manual stays byte-identical through commit 5, and that commit 6
changes only the rep and the prose.

- **R1, the sharpest — the passenger beneath an open bundle (§6.2).**
  Four of the five derivations need an open binder to discard a box
  under a variable-width bundle; `guide-open-arity.md` Rule 2 and
  design-exponents' Stage 5 finding ("binders close their body's
  input") both say that is where such things break. If it fails,
  `mapAccum` needs an accumulator-free sibling and the score is
  nine→seven. Settle it in commit 5's first hour, against `firstTrue`.
- **R2 — the derived types must print as the prims did.** If
  generalisation leaves `t` visible, `:t mapN` prints a segment
  variable where users expect `a1ⁿ⁰`. The derivation forces `t` to one
  wire, so it must be *solved*. Test: a golden file of the nine `:t`
  lines, diffed.
- **R3 — `normalizeArrow` needs a display letter.** `a0/ρ0/σ0/n0` are
  taken and `ς0` will be misread as `σ0`. Recommend `s0`, settled
  before commit 2 — every golden type depends on it.
- **R4 — `openTailedS` is asked two questions.** Splitting it into
  `openTailedS` and `determinateWidthS` is a pure refactor with many
  call sites, several inside `expSplit` and the recursive-call
  placement check that design-exponents' Stage 1–2 note records as
  having been broken once by this very confusion.
- **R5 — `instantiateClosed`'s closing policy.** A segment variable in
  a non-final atom should close to `•`, like a stack var; its
  interaction with a `tⁿ` whose `n` closes to 0 decides which error
  the user sees when one fails.
- **R6 — `sameCode` and the normalizer.** design-macros' `ev`
  amendment notes that a *declared* hom-object pins a width and makes
  laws decidable, while an unpinned arrow "has no arity" — a
  `mapAccum` whose `t` is unsolved exactly. `laws.braid` and
  `circuits.braid`'s law tables test it.
- **R7 — two shipped surfaces to diff at commit 6.** `reflect`,
  `evalAs` and `showsType` round-trip through `reprStackV` /
  `stackOfRepV` and `dictionary.braid` prints types; and `gla.braid`'s
  `Δ∇ = scale-by-2` now runs on a derived `dupN`.

## 9. What is explicitly out

- **Dimension arithmetic** `n+m`, `n·m`. design-exponents.md excludes
  it and sets the criterion any proposal must meet: reshape must be
  the **laws of exponents** from index-type algebra — `A^(n+m) ≅ Aⁿ
  Aᵐ` (the base coproduct `[n+m] ≅ [n]+[m]`) and `A^(n·m) ≅ (Aⁿ)ᵐ`
  (currying the index function) — not ad-hoc type-level maths. Nothing
  here needs it or brings it closer.
- **`unExp`.** design-exponents.md §Stage 4–5: unrolling one layer
  needs `n = 0` and `n = S m` to share a scheme, a dependent sum. The
  fold remains the honest eliminator; segment variables do not change
  that by one inch.
- **Term-level widths.** Rejected in design-exponents, still rejected.
- **A width channel from checker to runtime** — a per-call-site stamp
  on the `Term`, or an arity field on `VFn`. The only thing that buys
  nine→three (§6.1), and it costs the property Stage 4 bought: no
  elaboration, no tags, no monomorphization. If ever wanted it should
  be argued on its own, against design-indices.md's erasure story, not
  smuggled in behind a kind.
- **`tabulate`, `zeroN`, `unpack`, recursion on `Fin`,
  width-branching** — design-indices.md prices these as one purchase
  with Level-2 arithmetic; **segment variables in `data` and `theory`
  declarations** (§5.6); and **`A*` sugar**, which design-exponents
  open question 4 leans against and this note does not reopen.
