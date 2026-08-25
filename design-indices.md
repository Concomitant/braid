# Design note: indices — Fin(n) with witnessed introductions (CONVERGED, staged)

Consolidates the 2026-08-24/25 discussions; status: design position +
implementation plan in flight.

## The reading

Braid's `Aⁿ` IS the function space `Fin(n) → A` — the power (cotensor)
of A by the canonical n-element set. In any cartesian category the
power by a finite discrete object collapses to an iterated product
`A × ⋯ × A`; Braid takes that isomorphism as the REPRESENTATION,
storing the function in tabulated normal form, laid flat on the stack.
That is the precise content of "a vector with no box" (README idea 10).

Braid therefore has TWO exponentials, distinguished by whether the base
is general or finite-discrete:

- `Fn⟨Σ ⇒ Θ⟩` — the internal hom. Boxed into one wire, eliminated by
  `apply`.
- `Aⁿ` — the hom out of `Fin(n)`. Unboxed, because finiteness lets the
  product representation exist; eliminated by the fold.

If `Fin(n)` existed as a type, `Aⁿ ≅ Fn⟨Fin(n) ⇒ A⟩` would be a
theorem IN the language, not a slogan about it.

Read the existing primitives as the function-space structure they are:

- `mapN f` is postcomposition — functoriality of `(−)^X` in A.
- `zipN`/`unzipN` witness `Aⁿ × Bⁿ ≅ (A×B)ⁿ`: powers preserve products,
  because `(−)^X` is a right adjoint. That is why re-splitting is free
  — `1 2 3 4 >> zipN >> zipN` typechecks — and why the iso is
  definitional in the flat representation: the same wires, read
  differently.
- `dupN` is `Δ` pointwise followed by that iso. Which is exactly why
  deriving it would need `mapN12` + `unzipN`: that IS the
  factorization, not a workaround for the absence of one.
- `foldExp` is elimination by the base's cell structure,
  `[n] ≅ 1 + ⋯ + 1` — functions out of a coproduct decompose case by
  case, and unary successor is exactly enough structure to iterate that
  decomposition. Hence "the eliminator is a fold, not an unroll"
  (design-exponents.md, stage 4).
- Sharing element variables across copies (`expSplit`'s peels reuse the
  base's vars) is the statement that the codomain is NON-dependent:
  `Fin n → A`, one A.

The splice was the language flirting with the dependent version,
`Π i. A(i)` — a heterogeneous segment of unknown length. That is
exactly what broke unification; see design-flexible-arity.md.

## Extension vs intension — what was missing

A function has two sides: extension (its graph, its tabulation) and
intension (a rule, plus application at an index). Braid has only the
extensional side — map, zip, fold — and nothing intensional: no
`Fin(n)` as data, no `at`, no `tabulate`. In Haskell terms it is a
Representable functor whose representing object is kept abstract and
erased.

That erasure is exactly why `zeroN : • ⇒ Intⁿ` is "operationally
uninhabitable" (design-exponents.md, stage 5) even though the FUNCTION
λi.0 obviously exists. The function has a finite description
independent of n; the TABULATION does not, and the tabulation is the
representation. Same story for `unpack : List(a) ⇒ aⁿ`.

## The witness discipline, type-theoretically

"Witness" is not house jargon. It is four standard notions coinciding
on the same rule.

1. LOGICALLY, the witness of an existential. "This segment has some
   width" is `Σn. Aⁿ`; a constructive proof exhibits the pair. Braid's
   twist is that the data IS the proof — a proof-relevant existential
   where you were going to carry the proof anyway. `List` is this Σ
   sealed shut; a final-position `Aⁿ` is the same Σ lying open on the
   stack. `pack : aⁿ ⇒ List(a)` is Σ-introduction (forgets the static n
   into the box); the folds are eliminators that consume the pair
   without letting n back out to the type level; `unpack` is the
   projection that would unseal it. Refusing `unpack` is refusing
   dependent elimination.

2. IMPLEMENTATIONALLY, forced indices. Brady, McBride, McKinna,
   *Inductive Families Need Not Store Their Indices* (TYPES 2003):
   `Vec n a` need not store n because the index is FORCEABLE — uniquely
   recoverable from the value's structure. Braid runs this backwards,
   as legislation rather than optimization: an index may only OCCUR
   where it is forceable from relevant data. "The stack is the witness"
   means every index sits in a forced position. The witnessed-intro
   rule is then a well-modedness condition on primitive schemes — every
   n in an output must be forced by some input — the same SHAPE of
   condition as strict positivity: a syntactic check on signatures
   buying a global theorem.

3. THE THEOREM BOUGHT: adequacy of erasure. In quantity-annotated
   systems (Atkey, *Syntax and Semantics of Quantitative Type Theory*,
   LICS 2018; McBride, *I Got Plenty o' Nuttin'*, 2016; Mishra-Linger &
   Sheard, erasure PTSs, FoSSaCS 2008) an erased variable is one the
   runtime never scrutinizes. Naively `sumN` scrutinizes n — it
   performs n additions. The resolution: the untyped machine never
   computes n at all. The final-atom convention hands it the whole
   remaining stack and it recurses on data until empty; the dependency
   on the index factors completely through relevant arguments.

   And now the payoff observation. An untyped evaluator can determine a
   segment boundary without types in exactly two situations: the
   segment runs to the end of the stack, or the segment is empty. Those
   are precisely "final ⇒ open" and "non-final ⇒ n := 0". THE
   POSITIONAL RULES ARE THE ERASURE-ADEQUACY CONDITION STATED
   SYNTACTICALLY. The typed language exceeds the untyped machine only
   in ways the machine can decide by position.

4. PHASE DISTINCTION (Harper, Mitchell, Moggi, *Higher-order modules
   and the phase distinction*, POPL 1990). n is static, the stack is
   dynamic. The usual sins are functions across the boundary: `asFin`
   (dynamic → static) and `widthOf` (static → dynamic). Braid forbids
   both AS FUNCTIONS and permits the phases only to AGREE — at a forced
   position the constructor that built the data determined the index
   simultaneously, so no information flows in either direction. The
   phases are correlated at a common origin, not communicating.

   That is why parametricity in n survives erasure: with no runtime
   avatar of n and no observation channel, a width-polymorphic body is
   uniform by construction — which is what gives a law checked at n = 3
   its force at every width.

## The rule

EVERY INDEX INTRODUCTION'S n MUST BE FORCED BY A RELEVANT INPUT.

Two constructive modes, mirroring proof-vs-data:

- STATIC witness — a literal offset in the type. `fin2 : • ⇒ Fin(n+3)`,
  where the offset IS the derivation `2 < 3+n`, maintained by `weaken`.
  `at` then needs no runtime check.
- DYNAMIC discharge — `checkedAt : Int aⁿ ⇒ (Fin(n) aⁿ | Int aⁿ)`. The
  hit track IS the witness: refinement by routing, the same move `odd?`
  makes for parity.

Proofs static where possible, data where necessary, nothing in between.

`asFin : Int ⇒ (Fin(n) | Int)` with no bundle present stays unspellable
by the same mechanism that excludes `zeroN` — an output-only n. No
special case needed; the existing rule already rejects it.

## What the fragment dodges

Four costs a full `Fin` normally carries, each dodged, and why.

- NO inequality solver. The type never PROVES `i < n`; every
  introduction establishes it and every operation preserves it. Bounds
  by construction, not by constraint. (Contrast DML/ATS, where index
  constraints are shipped to a linear-arithmetic solver.)
- NO branch refinement. `Fin` is never eliminated structurally — it is
  consumed by `at` or forgotten by `finInt`. Comparisons of indices are
  ordinary data ops returning Bool; the type system is not consulted.
  Structural recursion on `Fin` would need GADT-style per-branch
  refinement, which Braid's rows deliberately lack: a row runs a
  component per alternative, and every other wire's type is identical
  across arms. That is `unExp`'s rejection resurfacing as an
  elimination problem.
- NO singletons. Nothing has an output-only n, so no runtime avatar of
  a static natural is needed. (Contrast DML's `int(n)`, Haskell's
  singletons library.)
- NO unerasure. Non-erasure would cost three things. (i) Parametricity
  in n: `widthOf` becomes writable, code branches on width, and a law
  checked at one width certifies only that width — gutting the rewrite
  licenses that laws-are-programs depends on. (ii) The free
  isomorphisms: `zipN >> zipN` retyping the same flat wires has zero
  runtime content only because width lives in the type; tagging turns
  every re-reading into a retagging operation, and "a vector with no
  box" IS the erasure. (iii) The untyped evaluator: tags mean
  evidence-passing threaded through execution, and `evalCode`'s dynamic
  splicing gets much hairier.

  The clinching observation: THE UNERASED BUNDLE ALREADY EXISTS. It is
  `List` — `Σn. Aⁿ` with n stored, cons-structured instead of tagged.
  Unerasing `Aⁿ` would build a second, worse list whose width leaks
  into the type.

## The fence (excluded, priced, not "not yet")

`tabulate`, `zeroN`, `unpack`, structural recursion on `Fin`,
width-branching. Each requires n as runtime data.

Together they cost: a singleton mechanism; Level-2 width arithmetic
WITH inequalities (a Presburger-ish solver inside inference); qualified
displayed types (constraints appear in `:t` output); and branch
refinement (a different checker, not an extension). Do them together or
not at all — the same purchase as design-exponents.md's Level 2, via
the Kennedy-style route priced in design-flexible-arity.md.

The escape valve in the meantime is `List`, the sealed Σ. Whenever a
width genuinely must be data, that is what a list is for.

## Two exponent regions

A prim with two DISTINCT exponent regions on one spine — a hypothetical
`gatherN : Fin(n)ᵐ aⁿ ⇒ aᵐ` — is outside the unification fragment:
`expSplit` right-anchors, requiring the rest to be closed ("one open
exponent per segment region", design-exponents.md).

Gather is therefore DERIVED, never a prim: box the source frame and
thread it through a fold's accumulator. This generalizes to the
multi-frame convention below.

## Forward check: dataframes

A frame factors along the axis the language already enforces: SCHEMA
STATIC, ROWS DYNAMIC.

- Equal-height columns = shared n. `Intⁿ Strⁿ` is a two-column frame
  whose height correlation the checker enforces. `Box(Intⁿ) Box(Strⁿ)`
  is a column-store frame whose columns provably match, and boxed
  columns can go in lists, cross branches, and be named. The README's
  syllabus-vs-transcript dimension error is already a frame-shape
  error.
- Dynamic row counts = `List`, by the fence. Row-major
  `List(Box(row))` preserves the equal-columns invariant by
  construction; column-major `List(a) List(b)` loses it. Recommend
  row-major.
- `Fin`'s dataframe roles: `indicesN` = row numbers, so `(Fin(n) a)ⁿ`
  is a keyed column; `at`/`checkedAt` = safe row access with a miss
  track; a join index from an n-frame into an m-frame is `Fin(m)ⁿ` —
  pointers as data with bounds in the type — and gather-via-`Box` IS
  join application; `argmaxN : Intⁿ ⇒ Fin(n)` is derivable (`indicesN`
  + `foldExp2` with a `Box(idx val)` accumulator), a witnessed index of
  the maximum.
- MULTI-FRAME CONVENTION: one open frame on the spine, every other
  frame in a `Box`. The one-open-region principle applied to frames.
- HONEST SCOPE: for list-resident frames — filtered, grouped — `Fin`
  contributes little; folds and `nth` cover access, no witness needed.
  `Fin`'s value concentrates in the static/analytics tier:
  bundle-resident data, joins, permutations, argmax. Filter and
  group-by live in list-land by the fence, and that is the right
  factoring, not a gap.
- Column NAMES today are binder labels on boxed columns
  (`-> prices qtys`) — lexical, free, no machinery. Type-level column
  names are record rows (design-flexible-arity.md, route 2); dataframes
  are the forcing function that would cash that route in, and that
  discussion should start from this use case.

## Honest gaps

- No `tabulate` means bundles can only be transformed, never generated.
  `zerosLike = 0 ... >> scaleN` — zeros OF the width you gave me — is
  the idiom; a bundle from nothing is spellable only at concrete width,
  where it is just a stack.
- `Fin` values print as bare integers. Erasure is honest here, but a
  reader cannot tell a `Fin` from an `Int` in output.
- `at` and `indicesN` are open-arity, hence final-atom-only. The usual
  placement discipline — but it means index-heavy pipelines need one
  stage per indexing operation.

## References (checked 2026-08)

- E. Brady, C. McBride, J. McKinna, *Inductive Families Need Not Store
  Their Indices*, TYPES 2003 (forcing, detagging, collapsing).
- R. Atkey, *Syntax and Semantics of Quantitative Type Theory*, LICS
  2018; C. McBride, *I Got Plenty o' Nuttin'*, 2016 (quantities, erased
  variables).
- N. Mishra-Linger, T. Sheard, *Erasure and Polymorphism in Pure Type
  Systems*, FoSSaCS 2008 (erasure adequacy).
- R. Harper, J. C. Mitchell, E. Moggi, *Higher-order modules and the
  phase distinction*, POPL 1990.
- H. Xi, F. Pfenning, *Dependent Types in Practical Programming*, POPL
  1999 (DML index language, singletons, constraint solving — the
  contrast case).
- design-exponents.md (the `Aⁿ` tier, the fold eliminator, Level 2).
- design-flexible-arity.md (the tail-only fragment, the three priced
  routes; value-directed width is route 3).
