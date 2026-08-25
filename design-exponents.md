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
`apply`. Fixed-arity remains writable today as `select`-chains; the
exponent buys the single variadic word.

## Level-1 GLA programme (what this unlocks, no arithmetic)

Generators, all width-polymorphic in `n`:
`dupN` (Δ, copy), `addN` (∇, pointwise add), `zeroN` (unit),
`dropN` (counit/discard), `zip`, `sumN`, scalar `scale : ℝ ℝ^n ⇒ ℝ^n`.

- Matrices are `Fn⟨ℝ^n ⇒ ℝ^m⟩` values; composition is `>>`-composition
  of quotes (`bake`-style), application is `apply`.
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
