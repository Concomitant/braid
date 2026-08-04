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
