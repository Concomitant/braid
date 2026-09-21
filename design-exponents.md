# Design: exponent types `A^n` — dimension-indexed stack segments

Status: DESIGN, not implemented. One extension serving two masters:
variadic folds over stack products (control flow) and graphical linear
algebra (GLA). Supersedes the "starred tails `A*`" sketch — the star
survives only as an anonymous exponent.

## Motivation

Two independent needs turned out to want the same feature:

1. **Fold over products, not lists** (control flow). A guard ladder laid
   out as bare wires — `b1 a1 b2 a2 … d` — folds by `select`-chaining,
   but only at fixed arity: no single word can say "any number of
   `Bool Fn` pairs" because a bare stack variable `ρ` cannot constrain
   its elements. `List(…)` reifies the product to get one fold word;
   the type-level alternative is a homogeneous segment type.

2. **GLA**. Objects in graphical linear algebra are natural numbers —
   bundles of wires. Braid's stack *is* n wires already; what's missing
   is saying "n wires of ℝ" and *correlating* widths across positions
   (`add` takes two equal-width bundles). Matrices are then ordinary
   `Fn` values between bundles.

## Why exponents, not stars

`ρ : A*` welds width to element type — reusing the variable is the only
way to say "same width," and it drags the element along. `A^n` names
the width as its own variable, decoupled:

```text
zip    : Aⁿ Bⁿ ⇒ (A B)ⁿ            -- equal widths, different elements: star CANNOT say this
add    : ℝⁿ ℝⁿ ⇒ ℝⁿ                -- pointwise +: dimension equality by reusing n
dupN   : ℝⁿ ⇒ ℝⁿ ℝⁿ                -- copy a bundle (GLA Δ)
zeroN  : • ⇒ ℝⁿ                    -- the zero vector (GLA unit)
sumN   : ℝⁿ ⇒ ℝ                    -- fold a bundle (GLA counit ∘ add tree)
matrix : Fn⟨ℝⁿ ⇒ ℝᵐ⟩               -- an n → m linear map, as a value
firstTrue : (Bool Fn⟨• ⇒ r⟩)ⁿ Fn⟨• ⇒ r⟩ ⇒ r    -- the variadic guard ladder, no List
```
(Display forms; users type `A^n`, `R^n` etc. — see Syntax.)

`zip` is decisive: GLA pairing and pointwise ops need two same-width
bundles of *different* element types. Also future-proofing: dimension
arithmetic (`ℝ^(n+m)`) needs named exponents; a star can never grow
into it. `A*` may remain as sugar for `A^_` (fresh anonymous exponent)
or be dropped.

**Terminology — corrected**: `A^n` is the n-fold **product** (the n-th
*power*, not copower — the copower is the n-fold coproduct `n·A`), and
in Set that is exactly `Hom([n], A)`: **a vector is a function from a
finite index set to its element type.** So `A^n` is not a pun on the
exponential — it *is* an exponential object, with a finite discrete
base. `Fn⟨A⇒B⟩` and `Aⁿ` are the same operation (hom) at different
bases; the superscript is honest.

This exposes an operational split the spec should keep straight: the
same set-level object has a **spatial** presentation (n actual wires on
the stack — what GLA diagrams are) and an **intensional** one (a
quotation `Fn⟨Fin(n) ⇒ A⟩` from an index type — what lookup/arrays
want). Isomorphic in Set, as different as data and code operationally.
The iso is `tabulate`/`index`, and a future `Fin(n)` shares the same
exponent variable sort `n` — one NVar serving both roles.

## Syntax

- **Input**: caret — `Bool^n`, `R^n`, `Int^3` — following the existing
  ASCII-in convention (`...` for `…`, etc.). Unicode superscripts also
  accepted on input.
- **Display**: real superscripts — `Boolⁿ`, `ℝⁿ`, `Int³` — following
  the existing pretty-out convention (`•`, `⇒`, `⟨⟩`). Digits all
  superscript (⁰–⁹); exponent *variables* draw from the letters with
  Unicode superscript forms — `ⁿ ᵐ ᵏ ⁱ ʲ` — so the variable convention
  is `n, m, k, i, j`. (A variable outside that set would display with
  the caret as fallback; the pretty-printer should simply never
  generate one.)
- Patterned segments: `(Bool Fn⟨• ⇒ r⟩)^n` — the base may be any
  *stack segment* (SSplice precedent: segments are already first-class
  in type params, cf. `List(A B)`).
- `^` binds tighter than juxtaposition: `R^n Int` is a bundle then an
  Int. Parenthesize segment bases.
- Concrete exponents allowed: `Int^3` ≡ `Int Int Int` (pure notation —
  normalizes away; display folding may reconstitute it, open question
  2).

## Semantics and typing

**New variable sort**: NVar (exponent variables), kind Nat, joining
TVar/SVar/RVar in `Scheme`. Structure: **unary naturals — zero and
successor only.** No addition, no multiplication (Level 2, explicitly
excluded for now). At runtime exponents are erased; widths are concrete
on the actual stack. No term-level `n` — this is not dependent typing;
the type never computes with n, it only *correlates* occurrences.

**Unification**:
- `A^n ~ A^m` ⇒ `n := m`.
- `A^n ~ ε` (empty) ⇒ `n := 0`.
- `A^n ~ B s` (cons): requires `A ~ B`, `n := S m` fresh, recurse
  `A^m ~ s`.
- Discipline: at most **one open exponent per segment region**,
  right-anchored where ambiguous — the same rule that keeps SVar tails
  and `SSplice` principal. Two adjacent open exponents (`A^n B^m` with
  both unknown against a concrete stack) is rejected as ambiguous,
  like two open tails today.
- An exponent over a segment `(A B)^n` unifies stepwise by segment:
  `(A B)^n ~ A B s` ⇒ `n := S m`, recurse.

**Interaction with existing sorts**: `A^n` is a new SType constructor
(a splice with multiplicity), sitting exactly where `SSplice` sits.
The right-anchoring machinery generalizes; this is the main
implementation surface.

## Eliminators — the fold, generated like a data type's

`A^n` is the stack-level `List(A)`: same initial algebra `(• | A X)`,
unboxed, width in the type. It gets the same equipment a `data`
declaration gets:

```text
unExp   : A^n ⇒ (• | A A^m)        -- with n = S m on the cons track; n = 0 on nil
foldExp : r-cases … A^n ⇒ r        -- generated structural fold, mirrors foldList
```

The unroll is where successor structure is *required*: the cons track
refines `n` to `S m`. This is the entire reason exponents carry
zero/successor and no more — induction needs exactly that much.

Control-flow payoff (the original ask): the guard ladder as a product,
one fold word, any width:

```braid
def sign = x ->
    (x >> negative) ["neg"] (x >> zero) ["zero"] [x >> toStr]
    firstTrue
```

with `firstTrue : (Bool Fn⟨• ⇒ r⟩)^n Fn⟨• ⇒ r⟩ ⇒ r` defined by
`foldExp` — conditions pre-evaluated (product = probe all lanes, the
`||` negotiation's resolution), actions selected as quotes, one
`ev`. Fixed-arity remains writable today as `select`-chains; the
exponent buys the single variadic word.

## Level-1 GLA programme (what this unlocks, no arithmetic)

Generators, all width-polymorphic in `n`:
`dupN` (Δ, copy), `addN` (∇, pointwise add), `zeroN` (unit),
`dropN` (counit/discard), `zip`, `sumN`, scalar `scale : ℝ ℝ^n ⇒ ℝ^n`.

- Matrices are `Fn⟨ℝ^n ⇒ ℝ^m⟩` values; composition is `>>`-composition
  of quotes (`bake`-style), application is `ev`.
- The interacting-bialgebra laws (copy/add commutation, Frobenius/Hopf
  fragments as applicable) are **checkable in laws.braid style** —
  operational rewrite licenses, per the laws-are-programs doctrine.
- Transpose continues the `reverse >> map dualize` story from
  `examples/transpose.braid`, now dimension-checked.

## Explicitly excluded (Level 2+, defer)

- **Dimension arithmetic** `n+m`, `n·m`: needed only for
  flatten/reshape (matrix as `ℝ^(n·m)` block, splitting bundles at
  computed points). Unification modulo AC threatens principality;
  postpone until a concrete need. Successor is NOT a gateway drug: it
  stays unary and syntactic. **When Level 2 does come, its laws are
  already written**: since `Aⁿ` is an exponential with finite base,
  the reshape operations are exactly the **laws of exponents** —
  `A^(n+m) ≅ Aⁿ Aᵐ` (splitting a bundle is the base coproduct
  `[n+m] ≅ [n]+[m]`), `A^(n·m) ≅ (Aⁿ)ᵐ` (a matrix as m columns of n —
  reshape is *currying the index function*). Dimension arithmetic is
  index-type algebra, not ad-hoc type-level math; that is the design
  criterion any Level-2 proposal must meet.
- **Term-level exponents** (dependent types): rejected previously,
  still rejected. `n` never flows into terms; runtime widths are
  concrete.
- **Constraint kinds beyond element type** (e.g. "sorted", bounds):
  out of scope.

## Stage 1–2 implementation notes (2026-07-28)

Implemented: NVar sort (`Exp Int (Maybe NVar)` canonical form — k
successors over a variable or zero), `SExp base exp rest` stack node,
full Subst/Vars/Scheme plumbing, and unification: pointwise for
same-width bases, front-peeling `expSplit` against concrete stacks
(each peel refines the exponent by one successor; copies share the
base's element vars, so all chunks are forced equal), tail-binding and
splice-bridging for open stacks. Canonical form: concrete exponents
and concrete offsets expand into real copies (`base^(n+2)` ≡ two
copies then `baseⁿ`), so equal stacks are structurally equal. 14
unification tests; the pre-existing 380 unaffected.

**Known limitation**: a region with TWO exponents over the same
variable — `ℝⁿ ℝⁿ`, the `addN` input — unifies against symbolic
stacks (`ℝᵐ ℝᵐ`, pointwise) but not yet against concrete ones: that
needs the linear special case `2n = w` (all exponents in the region
sharing one variable and one base width ⇒ divide). Deliberately
deferred to the stage where a prelude def actually demands it; the
general multi-variable case stays rejected (ambiguous, non-principal).

## Stage 4–5 implementation notes (2026-07-28)

**Stage 4 — the eliminator.** `foldExp : Fn⟨b a ⇒ b⟩ b aⁿ ⇒ b` (and
the pair twin `foldExp2` over `(a c)ⁿ`) shipped as prims. Open
question 1 is ANSWERED: erased exponents execute via the existing
final-atom convention — a width-polymorphic prim in final position
receives the whole remaining segment, and that segment's runtime width
is the erased n's witness (the forget/rotLast/loop mechanism; no
elaboration, no tags, no monomorphization). One polymorphic def runs
at every width, n = 0 included. `instantiateClosed` closes SPINE
exponents to 0 for non-final atoms (the ρ := • policy one level up);
element-type exponents still freshen. **No `unExp`**: unrolling one
layer would need n = 0 and n = S m to share a scheme — a dependent
sum. The fold is the honest eliminator.

**Stage 5 — the payoffs.** The linear same-var chain shipped in
`expSplit` (k exponents over one variable, bases may differ, closed
tail, closed other ⇒ divide), which is exactly what `addN` and `zipN`
need against concrete stacks. Prims `dupN/addN/zipN/scaleN` + derived
`sumN`; `examples/gla.braid` runs Δ∇ = scale-by-2 as an operational
bialgebra check and a dimension-checked dot product. `firstTrue`
landed as a derived prelude def over `foldExp2` — the guard-lanes
product from the control-flow arc, `(Bool Fn⟨•⇒r⟩)ⁿ Fn⟨•⇒r⟩ ⇒ r`,
first-true-wins via a (decided | default) accumulator sum so exactly
one action runs.

Findings for the record:
- **Binders close their body's input** — a `(d -> …)` cannot take one
  wire and leave an open bundle below; `firstTrue` routes the default
  through `rotLast` and the accumulator sum instead. Any future
  exponent-consuming def faces the same constraint.
- **`zeroN : • ⇒ Intⁿ` is operationally uninhabitable**: an
  output-only exponent has no witness (nothing on the stack determines
  n at runtime). Producing bundles from nothing needs value-directed
  width — the `tabulate`/`Fin(n)` side, or literal-exponent
  monomorphic uses only. Excluded for now.
  **Split 2026-08-25** (`design-indices.md`): the `Fin(n)` side has a
  cheap half and an expensive half, and this note conflated them. The
  cheap half — `Fin(n)` as a type with WITNESSED introductions only
  (`at`, `indicesN`, `checkedAt`, `weaken`, literals) — needs no
  singletons, no inequality solver, no branch refinement, and no
  unerasure, so it ships. The expensive half — `tabulate`, `zeroN`,
  `unpack`, recursion on `Fin`, width-branching — is exactly the set
  whose n must be RUNTIME DATA, and it stays excluded as one joint
  purchase with Level-2 arithmetic. The dividing line is the rule that
  every index introduction's n must be forced by a relevant input.
- ~~Observed (pre-existing, not exponent-related): grouped compounds
  close with freshened element vars, so a binder param used only
  inside groups/quotes can display unconstrained (`sign : a0 ⇒ Str`
  where Int is forced at runtime).~~ **FIXED 2026-07-28**: this was a
  genuine soundness hole (`"oops" >> sign` typechecked, crashed at
  runtime). Cause: the grouped-compound non-final path in
  `inferOperand` solved the group's constraints locally (to find
  closable tails) and then DISCARDED them, losing any binding between
  the group's interior and outer metavariables (binder params). Fix:
  propagate `cs`. Fallout was all good news: `dot` tightened from the
  fake-polymorphic `aⁿ bⁿ ⇒ Int` to the honest `Intⁿ Intⁿ ⇒ Int`.

## Amendment 2026-09-20 — the terminal object has a name

**`one : • ⇒ •`.** The empty stack had a glyph and no word, which meant
the identity on it had no spelling at all: `1 ; drop` was the only way
to write the morphism, two atoms with an Int allocated in order to be
discarded. `pass : ρ0 ⇒ ρ0` is the same morphism at every width and so
pins NOTHING — `[pass]` cannot stand where `[one] : • ⇒ Fn⟨• ⇒ •⟩` is
wanted — which is why the word had to be monomorphic and had to be a
prim (a prelude def would have had to be `1 ; drop`, keeping the
allocation).

**Why `one` and not the alternatives.** `•` is the TERMINAL object:
exactly one member, the empty stack. Braid has no initial object and no
empty sum, so `none`, `nothing` and `empty` would each have named a
thing the language does not have — the empty type — and named it with
the one symbol reserved for the thing that has exactly one inhabitant.
`unit` is taken in practice: `examples/theories.braid` declares a
Monoid slot `unit : • ⇒ a`, and a prim of that name would shadow a slot
name people write. `.` is unavailable to the lexer, which already
answers *Unexpected '.' (did you mean '...'?)*: it is the symbol prefix
in `.dup` and the ellipsis prefix. `()` is unavailable in both
positions — *Expected a type expression* in type position, *Expected a
tensor stage, got: TokRParen* in term position. `one` is left, and it reads correctly in both: the
type and the word for its identity are the same three letters, so
`Fn(one -> a)` is `Fn⟨• ⇒ a⟩` and `[one]` inhabits it.

The ambiguity worth saying out loud: **"one" means one INHABITANT, not
one wire.** `•` is zero wires and one value.

**`•` as an exponent base.** `(•)^n` and `(• )^n` already parsed —
the exponent parser reads a 1-ary parenthesized sum as a segment, and
`(•)` is one. The bare `•^n` did not: `•`'s equation in `goStack`
returned before anything looked for a `^`, so the caret fell through to
the caller as *Expected '|' or ')' in sum type*. That is fixed, and
nothing downstream needed to change: `sexp SEnd` is an ordinary
zero-width base, `•^k` collapses to `•` for literal k through
`expandCopies`, and `•^n` is the zero-wide bundle.

**Why this is worth its own stage.** It is the **k = 0 case of a single
width schema**. The N-family as it stands is a pile of words that are
one word each under a general enough scheme: the whole family reduces
to `#mapAccum:j,k` plus `#zip:j` (fold, map, scan, unzip and the GLA
generators are all instances), and those two collapse to ONE WORD EACH
given three things:

1. **the terminal object as an exponent base** — this stage. `j = 0` and
   `k = 0` are the cases where a lane is absent, and without `•ⁿ` they
   are unwritable, so the schema could not be stated at its own
   boundary;
2. **a SEGMENT VARIABLE sort** — a variable ranging over *closed
   segments of unknown fixed width, including zero*. It sits between a
   wire (`a`) and a stack (`ρ`): a stack variable is a tail and may not
   be repeated, which is exactly what an exponent base needs to do. With
   it, `s^n` is the schema's shape and `j`/`k` stop being numerals in
   the word's name;
3. **`sⁿ = Σ` as a DEFERRED CONSTRAINT** — solved once `|s|` is fixed by
   the quotation's type, rather than at the point the exponent is met.
   This is what lets one word serve every arity: the width of the base
   is not known when the bundle is split, only when the step function
   handed alongside it is.

(2) and (3) are **not built** and are not proposed here. They are
recorded so the reason this stage is small is on the record: it is the
first of three, and the only one of the three that costs nothing.

## Amendment 2026-09-21 — every N prim is one catamorphism at a different motive

**SHIPPED**: `mapAccumN : Fn⟨r a ⇒ r b⟩ r aⁿ ⇒ r bⁿ` is a prim;
`foldExp`, `foldExp2`, `mapN` and `mapN2` are prelude defs printing
character-for-character the schemes they printed as prims. 67 → 64.

**The reading.** `Aⁿ` is a stack SEGMENT repeated n times, and the
family `n ↦ Aⁿ` is the **initial algebra** in `[ℕ, C]`. A catamorphism
out of an initial algebra is determined by its **motive** — its
carrier — and the N-family was one catamorphism listed four times:

| word | motive `n ↦ …` |
|---|---|
| `foldExp` | `r` (constant carrier) |
| `mapN` | `bⁿ` |
| `mapAccumN` | `r ⇒ r bⁿ` |
| `unzipN` | `aⁿ bⁿ` |

The family was plural because **Braid cannot write a width-indexed
motive**: no scheme can say "the carrier at n is `bⁿ`". Carrying the
accumulator explicitly writes them all anyway, because **traversal in
the State applicative is all of traversability for a finitary
container** (READING: Gibbons & Oliveira, *The essence of the iterator
pattern*; Jaskelioff & Rypáček, *An investigation of the laws of
traversals*) — which is exactly why ONE generator covers map, fold and
index.

**Lambek, and what is actually missing.** The Stage 4–5 note says
there is no `unExp`. Read from the mathematics' side that is not a
statement about existence: Lambek's lemma says the structure map of an
initial algebra is an **isomorphism**, so the inverse — the unroll —
EXISTS, and `Aⁿ` is genuinely `• ⊕ (A × A^m)` with n = S m. What is
missing is the ability to **NAME its codomain**: `Σ m. (n = S m) × A ×
A^m` is a dependent sum, and a Braid row runs one component per
alternative with every other wire's type identical across arms. The
note's existing phrasing — "n = 0 and n = S m would have to share a
scheme" — is that same fact seen from the type system's side. The fold
is the honest eliminator because the fold is the half of the iso the
scheme language can spell.

**The erasure rule, in general form.** *Catamorphisms are
erasure-safe; anamorphisms are not.* A catamorphism CONSUMES the
structure, so the runtime counts the wires that are present and never
needs n; an anamorphism BUILDS from a seed, and nothing on the stack
tells the runtime how big. `tabulate` is the anamorphism, and
`zeroN`'s "operationally uninhabitable" (Stage 5) is the special case
of that rule at the constant coalgebra. This subsumes the positional
rules: an untyped evaluator finds a segment boundary only when the
segment runs to the end of the stack or is empty, and a catamorphism's
argument is always one of those.

The same rule fixes the prim's shape. **The accumulator is a WIRE, and
so is the element.** With a wire accumulator the runtime reads
`n = total − 1` off the final segment and the split is determined; a
stack accumulator leaves `|ρ| + n = total` and a k-wire element leaves
`k · n = total`, neither of which anything fixes. That is the erasure
argument of `design-segments.md` §6.1 — whose analysis is sound — and
it is why the reduction went through BOXING rather than through a
segment-variable sort. A multi-wire element always fits in one wire
(`Box : ρ0 ⇒ Box(ρ0)`), so `zipN` now merges two lanes into
`Box(a b)ⁿ` while `unzipN` still splits the flat stack-native
`(a b)ⁿ`; `unzipN >> zipN` is the flat → boxed normalizer and the
two-wire twins are one line each over it. Segment variables are NOT
being built: the boxing discipline buys the same collapse for the cost
of one `Box` per element, with no new sort, no deferred width
constraints, and no change to the rep format.

**Two independent structures on `Aⁿ`.** The initial algebra gives the
fold. The **Naperian / representable** view — `Aⁿ ≅ A^Fin(n)` (READING:
Gibbons, *APLicative programming with Naperian functors*) — gives the
zip, and it is what makes `zip` total and canonical rather than a
choice. `dupN` is the diagonal of that second structure, not a fold,
which is why it stays a prim: a catamorphism whose step returns one
wire per element cannot produce two bundles. `unzipN` stays for the
same reason.

**What did NOT collapse, and why.**
- `foldExp` is not `mapAccumN` at `b := •`. `b` is a WIRE variable and
  `•` is not a wire, so that instance is unreachable by instantiation.
  Derived `foldExp` emits a copy of the accumulator as its element and
  discards the bundle with `(r ... -> r (... >> forget))` — the only
  idiom that drops a segment of unknown width from under a wire (a
  binder that omits `...` CLOSES the segment to `•` instead).
- `at` is not a `mapAccumN` selecting on a matching index. Comparison
  is not the obstacle — `finInt` then `eq?` is fine. The obstacle is
  that the accumulator must be inhabited before the first element, and
  the result type `a` is a variable: there is no `a` to start from, and
  a sum-typed accumulator only moves the problem to the `merge`, whose
  other track still has to produce an `a`. Also `at` is O(1) and the
  derivation is O(n).
- `indicesN` introduces a `Fin(n)` mentioning the bundle's own width,
  which no user quotation can write. Both index words remain fenced by
  `design-indices.md`'s witness rule.

Open question 5 (2026-07-30, "the exponent functor has no morphism
action") is **ANSWERED**: `mapN` is `mapAccumN` with the quotation
itself as the accumulator, threaded untouched and dropped. `(-)ⁿ` is
functorial, and its fmap is a prelude def.

## Open questions

1. Does `unExp`'s nil/cons refinement interact with the persistent
   REPL stack the way `unList` does, or does erased-`n` need a runtime
   width witness in the interpreter? (Likely free: the stack's actual
   width is the witness.)
2. Display: fold `Int Int Int` back to `Int^3` in printed types, or
   only display exponents the user wrote? (Precedent: alias display
   folding — fewest-params-bound wins.)
3. Patterned exponents `(A B)^n` in *element* position of `List(…)` —
   compose with SSplice or restrict initially?
4. Whether `A*` sugar is worth keeping once `^` lands (leaning: no).
5. (2026-07-30, from the functors discussion) **The exponent functor
   has no morphism action**: `mapN : Fn⟨a ⇒ b⟩ aⁿ ⇒ bⁿ` is not
   derivable — `foldExp`'s accumulator is a single wire, so a fold
   cannot *grow* a bundle. `(-)ⁿ` currently has objects but no fmap.
   Needs a small prim in the foldExp family; it is the pointwise lift
   GLA wants (scaleN = mapN of a section, etc.) and would make the
   bundle tier functorial like List already is (`fmapList`,
   examples/functors.braid).
