# Design note: effects (arrows → theories → wires) — STAGE 1 SHIPPED

Consolidates three discussions (2026-07-30 … 08-03). Status: **stage 1
of the staging below — the IO grade — shipped 2026-08-25**; stages 2–5
remain design position. One decision was reversed at implementation
(the placement rule; amendment in place, below). Supersedes the
effect-row sketch in the old plan file; extends
design-control-flow.md §7.

## Stage 1 as shipped (2026-08-25)

Every arrow carries a **grade** — the set of resource wires it
touches. Stage 1 has exactly one label, `io`. A pure arrow prints as
it always did (`⇒`); an effectful one prints `⇒!`. Effect tails never
display: the same information hiding `ρ` already gets inside `Fn⟨…⟩`.

**Five prims are marked; everything else is inferred.** There is no
effect annotation anywhere — not in the prelude, the examples, or the
tests.

```text
print     : a0 ⇒! •
readLine  : • ⇒! (Str | Str)
readFile  : Str ⇒! (Str | Str)
writeFile : Str Str ⇒! Maybe(Str)
evalCode  : Code ρ0 ⇒! (ρ1 | Str ρ0)
```

`evalCode` is unconditionally io because it runs arbitrary code: the
dynamic escape hatch sits at the top of the lattice even when the code
it happens to run is pure. `reflect : Fn⟨ρ0 ⇒ ρ1⟩ ⇒ (Code | Str)`
stays pure — it READS code, it never runs it.

**Grades unify; they do not join.** Composition forces two arrows'
effect rows *equal*. The join everyone expects falls out of label
absorption into an open tail — tail-only, the same discipline stacks,
sums and widths already obey, which is what keeps inference principal.
The corollary is the **auto-opening rule**: every instantiated closed
grade gets a fresh tail, or a pure word could not sit beside an
effectful one.

**ε is a fifth variable sort.** The higher-order prims — `apply`,
`loop`, `foldExp`, `foldExp2`, `mapN`, `mapN2` — share ONE ε between
the inner `Fn` and the outer arrow, which is why a single `apply`
serves pure and effectful quotes alike. Prelude defs (`map`, `filter`,
`while`, `until`, `cond`) needed no changes at all; their
ε-polymorphism is inferred.

```text
1 >> print                    : • ⇒! •               composition propagates
def shout = toStr >> print    : a0 ⇒! •              inferred through defs
def quiet = toStr >> drop     : a0 ⇒ •               pure stays bare
[print]                       : • ⇒ Fn⟨a0 ⇒! •⟩      PUSHING is pure
[print] 5 >> apply            : • ⇒! •               apply transfers it out
[dup >> *] 5 >> apply         : • ⇒ Int              same apply, pure quote
[dup >> print ...] ... >> map : List(a0) ⇒! List(a0) ε-polymorphic
print print                   : a0 a1 ⇒! •           legal; left-to-right
```

**A declared `Fn` type MEANS its grade.** New surface syntax `⇒!`
(ASCII `->!`) writes the io form: `Fn⟨Str ⇒! •⟩`. A declaration that
says `Fn⟨Str ⇒ •⟩` refuses an io quotation — *Cannot unify effects: io
vs pure*. That strictness is the point, and it is also the limit:
there is no subeffecting, so a pure quote unified into an io context
types as io. Let-generalization at `def` boundaries restores per-use
freshness; inside one expression nothing does.

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

**Refinement (08-06): the placement ladder** — *step 1 amended 08-25
(below): the steps are licences, not legality.* "≤1 effectful" is the
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
   observable. *(Amended 08-25: several io atoms in a stage are legal
   and run left-to-right; what IO never earns is the reordering
   licence.)*

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

**Amendment (2026-08-25, at implementation): the decree won.** Stage 1
ships left-to-right, not ≤1. What settled it, in order:

- The ≤1 rule, once implemented, broke **11 existing sites**. `print
  print print` is the idiomatic way to print several wires; it stood
  in 2 examples and 7 tests. A rule that outlaws the idiom the
  language already teaches carries the burden of proof.
- The premise fails for Braid's surface syntax. The premonoidal
  obstruction is that a tensor has *no canonical order* — but Braid's
  tensor is not the abstract bifunctorial ⊗. Atoms are positionally
  aligned to wires (leftmost takes the deepest), so the text ALREADY
  fixes the order the obstruction says is missing, and the evaluator
  has implemented exactly that order since long before grades existed:
  the left-biased premonoidal tensor. The error the placement check
  wanted to print ("no canonical order — separate lines") would have
  been false.

The cost, stated plainly: **reversibility now runs the other way.** A
decree can be relaxed further but not tightened without breaking
programs — the reverse of the direction the 08-07 argument below banks
on ("partial can relax to total, not vice versa"). So ladder step 1
stops being a legality boundary and becomes the floor of a LICENCE
structure, exactly as this paragraph anticipated: steps 2 and 3 are
licences to reorder, parallelise and fuse, which a future grade must
EARN; step-1 stages are legal, rigid, and execute in textual order.
The implementation-stance invariant survives with its subject changed
— the check that was to be the PCM's definedness predicate is now the
licence predicate, and every ladder step must still re-verify that
equation before it lets a rewrite run. And the trade-off named just
above is the one now being paid: a mis-ordered effect is a silent
behaviour, not a type error.

**Formal home for the ladder (08-07): grading by a partial commutative
monoid.** The literature separates what our first sketch conflated:
sequential and parallel composition act on grades by DIFFERENT
structures (duoidally enriched Freyd categories — Heunen & Sigal,
RAMiCS 2023, arXiv:2301.05162, whose worked examples include "basic
separation semantics for resources"); our join-for-both is the
degenerate idempotent case. The parallel operation is honestly a
PARTIAL commutative monoid: grading a monoidal category by a PCM,
where side-by-side grades combine iff the PCM product is defined
(Sarkis & Zanasi, arXiv:2501.18404). Their hierarchy lands the punch:
trivial PCM = monoidal, and the TWO-ELEMENT PCM (eff ⊗ eff undefined)
= premonoidal/effectful — so ladder step 1 is not a conservative hack
but the canonical minimal choice, step 2 is the PCM with e⊗e = e for
law-certified commutative e, and step 3 is the resource-separation
PCM. Slogan, same shape as the compile-fold one: **the placement rule
is the partiality of the grade product.** The left-to-right decree =
totalizing that product by left bias (partial can relax to total, not
vice versa — the reversibility argument, now formal). Graded Freyd
machinery also carries quantitative grades — cost, differential
privacy (Gaboardi, Katsumata, Orchard, Sato, arXiv:2007.11235) — so
the ε sort is not forever effects-only.

**Implementation stance (08-07): keep the degenerate case; the PCM is
the spec.** The total idempotent join plus the placement check is
extensionally equal to the PCM: the partial product's only job is to
be undefined on illegal pairs, and the check forbids exactly those
pairs, so the join is never consulted where it would lie. Factoring
the partial operation into total-join + domain-predicate buys three
things: no partiality plumbed through unification (effJoin never
fails; the solver stays total on grades); better errors ("two
effectful atoms in one stage — no canonical order; separate lines"
instead of a grade-mismatch deep in the solver); and ladder upgrades
that touch only the domain predicate, never the grade algebra. THE
INVARIANT that keeps this honest: **the placement check must remain at
least as strict as the intended PCM's definedness — the check IS the
definedness predicate**, and every ladder step must re-verify that
equation; relax the check without its license and the join silently
grades meaningless tensors. Caveat for later: label-SET grades are
rightly idempotent, but quantitative grades (cost, privacy) need
non-idempotent SEQUENTIAL composition — idempotency is a property of
the effects instance, not the framework.

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

## The staging (1 shipped, 2–5 not scheduled)

1. IO bit on Arrow (the old arrows-plan stage 1; display `⇒!`, pure
   displays as today so all tests survive). **SHIPPED 2026-08-25** —
   see "Stage 1 as shipped" above; the placement rule it was to carry
   became the left-to-right decree instead.
2. **Resource** declarations + `=Name>` display sugar over wire
   suffixes. (Decisions taken 2026-08-25, before implementation:)
   - **Called `resource`, not `bundle` or `environment`.** "Environment"
     already means the TYPING environment here (`Env`/`VarEnv` — name
     resolution), and reusing it for runtime wires would collide on the
     one word that sounds like it fits. There is no canonical category
     theory term to borrow: `A S ⇒ B S` curries to `A → [S, B ⊗ S]`, so
     these are the Kleisli category of the state monad and S is the
     "state object" — accurate for state, wrong for a log (Writer) or a
     config (Reader). Threading is tensorial strength and S its
     parameter, but Para's parameter is CONSUMED, not threaded. Optics
     calls the carried-along object the *residual*, which rows already
     took. So: the note's own word, which stage 5 already speaks
     ("resource mark", "per-resource wires").
   - **An ordered suffix, juxtaposed.** A resource names a run of
     wires, and `=A B>` is their juxtaposition — the same reading as
     everywhere else, and forced by the tail-only discipline: threaded
     wires ride on top, in order.
   - **NOMINAL, not a structural alias** (corrected 2026-08-25, before
     any code). The first draft said a resource folds like `Maybe` —
     structurally, on shape. That cannot work: nothing distinguishes
     "this `Int Int` is a GameState" from "these are two Ints", so
     `resource GameState = Int Int` would silently rename every def
     that happens to thread two Ints. Structural folding is only honest
     when the shape IS the meaning (`(a | •)` really is optionality);
     a resource's meaning is exactly the part the shape does not carry.
     So a resource declares a DISTINCT type, `data`-style: it rolls and
     unrolls, and only a genuine GameState wire ever displays as one.
   - Which reconciles the suffix reading rather than breaking it: each
     resource contributes ONE wire (its contents boxed), so
     `=Log GameState>` is still an ordered suffix, still juxtaposition
     — a suffix of nominal wires instead of raw ones. Rolls are free at
     runtime, as every `data` roll already is, and threading is still a
     single `...`.
   - The cost, stated: touching a resource's contents needs an explicit
     unroll, where raw threaded wires needed none. That ceremony is
     what buys the fold its meaning — an accidental GameState is now
     unspellable.
3. Theories/`use` (elaboration only).
4. Ambient threading (elaborator frames pure stages inside `use`).
5. Resource mark + linear `World` + explicit/split levels.
Each stage independently useful; 1–2 are small; 4 is the big
ergonomic payoff; 5 unlocks the power tier.
