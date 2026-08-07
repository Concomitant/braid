# Design note: effects (arrows → theories → wires) — CONVERGED, NOT SCHEDULED

Consolidates three discussions (2026-07-30 … 08-03). Status: design
position, no implementation planned yet. Supersedes the effect-row
sketch in the old plan file; extends design-control-flow.md §7.

## The design, zoomed out

**Effects are wires.** The classical effect zoo decomposes into
structure Braid already has: state = a threaded wire, writer/log = a
wire, reader = closure capture, exceptions = the railway sum,
nondeterminism = List. Verified in-session: a `Log GameState` arrow is
expressible today as `A GameState Str ⇒ B GameState Str`, with pure
stages threading the bundle by a single `...` (data at the bottom,
bundle on top). Only **IO** is irreducible — a genuine observational
capability, not plumbing.

**IO is a linear wire.** The true string diagram for a premonoidal
category (Jeffrey 1997) reifies effect order as one linear control
wire threading every effectful box; pure boxes float free. Interchange
holds/fails as topology. GHC's `State# RealWorld` and Clean's unique
`World` are this wire in production. Braid's `⇒!` / `=IO>` annotation
is bookkeeping for that wire, unexposed because Braid lacks linearity
— so far.

**Labels are the wires' names.** `A =IO Log GameState> B` is not a
list of effect labels; it is the set of resource wires the def
touches. Three zoom levels, one semantics (ambient desugars to
explicit):

| level | user writes | user sees | linearity exposure |
|---|---|---|---|
| ambient (default) | `note`, `print`, plain `;` in `use` scopes | `=Log>`, `⇒!` inferred | zero — the elaborator draws the wire, so linearity holds by construction |
| explicit (opt-in) | `w -> … ; print! ; …` | `World` in types | one error family, at genuine bugs |
| split (opt-in) | `splitWorld : World ⇒ Stdout Fs …` | per-resource wires | same; disjoint wires commute BY GEOMETRY (per-resource fusion licenses) |

**Theories supply the machinery tier.** theory = named slots (+ laws
as runnable checks — instances are audited models, the laws-are-
programs doctrine given a front door); instance = values; `use` =
scoped, explicit, coherent selection (ML-modules lineage, not
typeclasses — see below). Candidate extension: `use M ( … )` blocks
that rebind sequencing itself (F# computation expressions, made
coherent by naming). Ambient bundles ride on the same scoping.

**The shared variable sort.** Higher-order combinators need
effect/bundle polymorphism: `apply : Fn⟨Γ ⇒ε Δ⟩ Γ ⇒ε Δ`, `map :
Fn⟨a =γ> b⟩ List(a) =γ> List(b)`. The arrows plan's ε and the ambient
bundle's γ are ONE new variable sort. Since all labels but IO are
wires, the elaborate effect-row unifier collapses to: bundle naming +
one IO bit + this variable.

**The placement rule** (≤1 effectful atom per tensor stage) is the
textual shadow of the undrawn wire: parallel effectful boxes cannot be
drawn without routing the one control wire. Forbid first (backward-
compatible to relax to decreed left-to-right, which the evaluator
already implements); at the explicit level the rule dissolves —
mis-ordered effects are unwritable, not illegal.

**Refinement (08-06): the placement ladder.** "≤1 effectful" is the
conservative floor of a three-step ladder, each step a strictly larger
legal fragment, each licensed by something checkable:

1. **≤1 effectful atom per stage** (the launch rule above).
2. **n atoms of one shared *commutative* grade.** When the effect
   commutes, order is unobservable, so juxtaposition is an honest
   (bifunctorial) tensor again — this is the old expanded-spec note
   "effectful tensor only for commutative effects with a lawful
   `zipM`", now with grading machinery to express it. Commutativity is
   a LAW: per-theory, runnable, instances are audited models — passing
   the check is the license to tensor. The killer instance is
   probability: two Dist atoms side by side ARE independent draws —
   the ambient product literally means statistical independence, which
   is the defining structure of Markov categories (Fritz, *A synthetic
   approach to Markov kernels…*, Adv. Math. 2020). A commutative-grade
   stage is also a parallelism license (any execution order is
   correct), the same way parallel.braid treats associativity as the
   split license.
3. **Pairwise-disjoint-or-commutative resources** — the wire-true
   rule, available once wires are explicit (split level). Same-grade
   is neither necessary nor sufficient for step 3: two `tell`s share
   the Log WIRE, so they commute only if the carrier monoid does
   (set/counter yes, list no) — same grade is the *worst* case; while
   a Log atom beside a GameState atom touch DISJOINT wires and commute
   by geometry — mixed grades are the *safe* case. Step 2 is the cheap
   syntactic gate that happens to coincide with the deep rule exactly
   where it matters most. IO stays ≤1 forever at the ambient level:
   everything IO touches the one world wire, and world-order is
   observable.

**The left-to-right alternative.** Instead of forbidding, decree
left-to-right order for effectful atoms in a stage (the evaluator
already does this; it is the left-biased premonoidal tensor). Under
the decree everything is *legal* and the ladder changes job: it stops
being a legality boundary and becomes the **license structure** — only
stages at step 2/3 may be reordered, parallelized, or fused; step-1
stages execute in textual order and are rigid. Trade-off, stated
honestly: forbid makes a mis-ordered effect a type error;
left-to-right makes it a silent behaviour. Everything-exact
temperament says forbid; every strict language's pragmatics says
decree. Either way the ladder is the part that carries the theory —
the choice only decides whether its floor is an error or a default.

**Linearity is cheap in a concatenative language.** Contraction and
weakening are WORDS (`dup`, `drop`, `forget`, ignored binder params) —
a closed set of sites. Linearity = an internal "must be copyable" mark
on those prims' variables; unifying the mark against a resource type
fails with one error message. No annotation syntax (there is none to
extend), no signature infection (contrast Clean's `*World`, Rust), no
display form; invisible propagation through inference; principality
untouched (it is a refinement of unification failure, resolved from
nothing).

## Why not typeclasses (recorded from the 08-03 discussion)

Classes don't cost principal types (qualified types keep them). They
cost: (1) annotation-freeness — ambiguity (`show . read`) forces
annotations Braid has no syntax for; inference-completeness (the term
determines everything) is the actual invariant; (2) coherence —
trivial in Haskell's nominal world, ill-posed in Braid's structural
one (is `(• | •)` Bool or a sum?); (3) erasure — dispatch makes types
drive behavior; (4) Monad/Functor classes need higher kinds (type-
language overhaul; kinds over stacks are open research). Meanwhile
Eq/Show/Ord-style overloading is moot (structural `eq?`, `toStr`,
`print` are already polymorphic prims). What remains — write generic
code once, don't pay the dictionary per call — is exactly what
theories + `use` deliver (once per scope), and monads/functors/arrow
classes are already first-class VALUES (examples/functors.braid,
state built in four lines in-session; dictionaries are data — pick a
monad at runtime).

## Prior art audit (every joint load-tested by someone)

- Wires: Clean/Mercury world-passing; GHC `State# RealWorld`; Koka's
  evidence-passing translation (their compiled form = our source).
- Labeled arrows + ε: Gifford–Lucassen → Talpin–Jouvelot → Koka rows;
  Scala 3 context functions.
- Theories: Plotkin–Power (effects ARE algebraic theories; handler =
  model); ML signatures/structures/functors; Scala givens for scoped
  named selection.
- Ambient scopes: Frank/Unison abilities (silence in bodies, arrows
  record abilities); F# computation expressions.
- Placement: Power–Robinson premonoidal; Paterson's proc
  linearization; Jeffrey's control-wire diagrams; Hughes arrows as
  the interface (examples/arrows.braid: Braid satisfies it natively).
- Novel-ish: instances audited by runnable laws; no transformer-
  ordering problem (bundles are unordered products; state×exception
  interaction chosen per wiring site, not per stack order).

## Formal grounding (references, checked 2026-08)

The two intuitions this note leans on are theorems, not analogies, and
the design is the *combination* of two established lineages:

- **"Effects are an invisible wire" = Jeffrey's runtime object.** To
  make a premonoidal/Freyd category's string diagrams well-defined you
  thread ONE extra wire — the "runtime" — through every effectful box;
  a wire can't pass two boxes in parallel, so it forbids the interchange
  (sliding) that would reorder effects. It is a generic *control/order*
  token, not necessarily a data value (state/log carry data; IO's wire
  is an abstract sequencing token). Now known to be a *faithful*
  internal language, not merely sound.
    - A. Jeffrey, *Premonoidal categories and a graphical view of
      programs*, 1997 (the original diagrams).
    - M. Román, *Promonads and String Diagrams for Effectful
      Categories*, arXiv:2205.07664 (2022).
    - Earnshaw, Hefford, Román, *String Diagrams for Premonoidal
      Categories*, arXiv:2305.06075 (2023) — faithfulness.
- **"Arrows are the interface" = arrows ≅ Freyd categories.** An arrow
  is an identity-on-objects functor from a cartesian category (pure
  maps) into a premonoidal one (effectful maps) — NOT "arrow = monad"
  and NOT "arrow = state".  This is why Braid, already cartesian, is
  already an arrow (examples/arrows.braid).
    - R. Atkey, *What is a categorical model of arrows?*, ENTCS 2011
      (the precise correspondence).
    - Power, Thielecke, *Closed Freyd- and κ-categories*, ICALP 1999.
    - Power, Robinson, *Premonoidal categories and notions of
      computation*, MSCS 1997 (premonoidal, the central/pure subcat).
- **The `=IO Log GameState>` grade = a graded (parametric) effect
  monad.** Hom-sets indexed by an ordered effect monoid; composition
  multiplies grades, `⊗` joins, grade 1 = pure = the central subcat.
    - S. Katsumata, *Parametric effect monads and semantics of effect
      systems*, POPL 2014.
- **The fusion actually built** (graded + premonoidal/Freyd), the
  closest single anchor for "graded premonoidal category" as a
  constructed object — it is otherwise the natural product of the two
  lineages above, not a single canonical named gadget:
    - Earnshaw, Hefford, Román (et al.), *Effectful Semantics in
      2-Dimensional Categories: Premonoidal and Freyd Bicategories*,
      ACT 2023, arXiv:2312.14964 (Freyd bicategory from a bistrong
      graded monad).

Framing: Braid's `>>` is the premonoidal composition, its `_`/`...`
framing is Jeffrey's wire made explicit (the three zoom levels =
invisible → named → drawn runtime wire), and the effect row is
Katsumata's grade.  The one genuinely new-ish move is presenting this
graded-Freyd structure as a *concatenative surface syntax* with the
grade inferred.

## Honest gaps

- Tail-resumptive fragment only: wire-discharge covers Reader/Writer/
  State/exceptions but NOT multi-shot control (backtracking,
  generators) — handler systems (Eff, Koka, OCaml 5) have those;
  Braid's answer stays structural (List, loop). Say so; don't imply
  parity.
- Crossing levels needs a named adapter (`withWorld`-style, one word).
- Library code that `dup`s a generic argument silently inherits the
  copyable mark; third parties meet it only as an (accurate) error.
- Open: quotes capture their `use` scope lexically (position taken:
  yes, closure-like); Code⟨⟩ reflection of elaborated (wire-threaded)
  code; what a `scope` is syntactically.

## If implemented, the staging

1. IO bit on Arrow (the old arrows-plan stage 1; display `⇒!`, pure
   displays as today so all tests survive).
2. Bundle declarations + `=Name>` display sugar over wire suffixes.
3. Theories/`use` (elaboration only).
4. Ambient threading (elaborator frames pure stages inside `use`).
5. Resource mark + linear `World` + explicit/split levels.
Each stage independently useful; 1–2 are small; 4 is the big
ergonomic payoff; 5 unlocks the power tier.
