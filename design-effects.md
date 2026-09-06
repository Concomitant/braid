# Design note: effects (arrows → theories → wires) — STAGES 1, 2, 3, 4 SHIPPED

Consolidates three discussions (2026-07-30 … 08-03). Status: **stages 1,
2, 3 and 4 of the staging below — the IO grade, `resource`
declarations, `use`, and theories/instances with runnable laws —
shipped 2026-08-25/26**; only stage 5 (the resource mark and the linear
`World`) remains design position. THREE decisions were reversed at
implementation — the placement rule, which end of the stack the
resource wires ride on, and the display form of the io label; all amendments
are in place below, and neither rewrites what it replaced. Supersedes the
effect-row sketch in the old plan file; extends design-control-flow.md §7.

**Amendment (2026-09-06): IO display changed from `⇒!` to `=IO>`.** The
io grade was originally given its own glyph (`⇒!`) when it was the only
label and could afford one. With functors and modes about to mint labels
beside it, one spelling for all of them is the honest one — io is not
inherently special, it is the label whose carrier you cannot touch. The
`=IO>` form displays consistently with resource labels like `=Log>`, where
the label rides on the arrow. The old `⇒!` and `->!` spellings still lex
for source compatibility. See stage 1 below for detail.

## Stage 1 as shipped (2026-08-25)

Every arrow carries a **grade** — the set of resource wires it
touches. Stage 1 has exactly one label, `io`. A pure arrow prints as
it always did (`⇒`); one marked io prints `=IO>`. The label rides on
the arrow like resource names do. Effect tails never display: the same
information hiding `ρ` already gets inside `Fn⟨…⟩`.

**Five prims are marked; everything else is inferred.** There is no
effect annotation anywhere — not in the prelude, the examples, or the
tests.

```text
print     : a0 =IO> •
readLine  : • =IO> (Str | Str)
readFile  : Str =IO> (Str | Str)
writeFile : Str Str =IO> Maybe(Str)
evalCode  : Code ρ0 =IO> (ρ1 | Str ρ0)
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
1 >> print                    : • =IO> •              composition propagates
def shout = toStr >> print    : a0 =IO> •             inferred through defs
def quiet = toStr >> drop     : a0 ⇒ •               pure stays bare
[print]                       : • ⇒ Fn⟨a0 =IO> •⟩    PUSHING is pure
[print] 5 >> apply            : • =IO> •              apply transfers it out
[dup >> *] 5 >> apply         : • ⇒ Int              same apply, pure quote
[dup >> print ...] ... >> map : List(a0) =IO> List(a0) ε-polymorphic
print print                   : a0 a1 =IO> •          legal; left-to-right
```

**A declared `Fn` type MEANS its grade.** The `=IO>` spelling writes
the io form writable in declarations: `Fn⟨Str =IO> •⟩`. A declaration
that says `Fn⟨Str ⇒ •⟩` refuses an io quotation — *Cannot unify effects:
io vs pure*. That strictness is the point, and it is also the limit:
there is no subeffecting, so a pure quote unified into an io context
types as io. Let-generalization at `def` boundaries restores per-use
freshness; inside one expression nothing does. (ASCII `->!` and the old
`⇒!` spelling still lex for backward compatibility.)

## Stages 2 and 4 as shipped (2026-08-26)

**A `resource` is a `data` declaration under another keyword.**

```text
resource Log     = Str
resource Counter = Int
```

It is NOMINAL, which was the corrected decision of the stage-2 entry
below and is the whole reason the fold can mean anything: an `Int Int`
stack is never silently a GameState (`resource GameState = Int Int` ⇒
`def notState = swap : a0 a1 ⇒ a1 a0`, unfolded, as it should be). It
contributes exactly ONE wire, its contents boxed. It generates the roll
`Log` and the unroll `unLog` — and NO `foldLog`: you unroll a resource,
you do not eliminate it by points (`foldLog` is *Unknown primitive*).
Rolls are free at runtime, as every `data` roll already is.

**A shared resource PREFIX folds onto the arrow, and the grade joins
it.** When both sides of an arrow begin with the same run of resource
wires, that run is what "threaded through" means, so it moves onto the
arrow itself:

```text
note  : Str =Log> •
bump  : • =Counter> •
score : Int ρ0 =Log Counter> Int ρ0
peek  : • =IO Log> •            -- grade and resources are ONE arrow
```

The last line is the note's `=IO Log GameState>` spelling arriving
intact: the io grade and the resource list are the same statement said
twice — the set of resource wires the def touches — so one arrow
carries both, and with no resources it displays as the label `=IO>`.
The fold is display only; nothing about it is inferred, and that is
structural rather than an omission: `unifyEff` ABSORBS (which is how
`io` propagates with no annotation anywhere), while `unifyStack` is
rigid and front-anchored with no suffix matching, so a remainder
variable eats `Log Counter` and nothing records that they were there.
ε and γ are not one variable sort in the code — the survey under stage
3 below has the detail — and that is precisely why stage 4 is an
elaborator with inference as its checker, rather than an extension of
the solver.

**Stage 4: `use` is a scope-taking form**, in the same family as the
binders `x y ->` and `-> x y` — `use Log Counter` takes the REST of the
enclosing scope as its body. An elaborator running between parse and
infer writes every `_` and `...` from the resource signatures alone:

```braid
def score =
    use Log Counter
    dup ; *
    bump
    "scored "
    note
```

The same program without it, which is what the language gave you before
stage 4 — and note that adding a third resource renumbers every line:

```braid
def scoreByHand =
    _ _ (dup ; *) ...
    _ bump ...
    _ _ "scored " ...
    swap ...
    _ note ...
    swap ...
```

Both infer `Int ρ0 =Log Counter> Int ρ0`. Inference is the CHECKER of
the elaboration, never an input to it.

**`use` ASSERTS its claim.** The scope opens with `unLog >> Log` per
resource — the identity on a Log that typechecks on nothing else — so
the incoming wires must really be those resources even when the body
never touches one: `def f = use Log >> dup : a0 ρ0 =Log> a0 a0 ρ0`.
Without the assertion a `use` header whose body ignored a resource
would be padding rather than a statement.

**Strength is an ordinary word.** `lift` shipped in the prelude:

```text
lift : Fn⟨ρ0 ⇒ ρ1⟩ ⇒ Fn⟨a0 ρ0 ⇒ a0 ρ1⟩
def lift = (f -> [_ (f ... >> apply)])
```

Run a program one wire deeper; compose it once per context wire. This
is tensorial strength — the action of `(A ⊗ −)` on a morphism — and it
is exactly what `use` does to a pure stage, which is why stage 4 needed
no new machinery for the pure case: the elaborator writes the padding
that `lift` would otherwise compose. The categorical content of the
ambient scope is a prelude def, not a compiler feature.

**The limits, stated plainly.** A stage may contain **at most one
resource operation, and it must be alone in that stage** — anything
else is rejected with *"a stage may contain at most one resource
operation, and it must be alone — put X on its own line"*. An operation
touching a *subset* of the scope's resources is rejected (*"X threads
Log, but this scope is over Log Counter"*): the router brings one
resource wire up, acts, and puts it back, and a subset at once would
need a solved permutation rather than a fixed `_`-prefix. Both limits
are the elaborator's, not the type system's, and both relax without
breaking programs.

**Amendment (2026-08-26, from writing a program with it): scopes
compose.** The rule above was first implemented as "one resource per
operation, full stop", which had a consequence nobody noticed until a
real program hit it: a word threading two resources could be *written*
under `use` and then never *called* from one, because the call site is
itself a stage inside a scope. `use` was a notation for a def body
rather than an abstraction, and the composite word — the ordinary unit
of program structure — was exactly what it could not express. The fix
needs no routing: a word threading precisely the scope's resources, in
order, already has the stack's shape, so it applies with an empty
`_`-prefix. The general subset case still wants the permutation and is
still rejected. The lesson is the one this note keeps relearning: the
limits that matter are found by writing programs, not by reading the
elaborator.

**Amendment (2026-08-26, at implementation): resources ride DEEPEST,
not on top.** The note says "data at the bottom, bundle on top", and
the stage-2 entry below calls the resources an ordered *suffix*. That
flipped during implementation, and the reason is routing, not taste:

- Braid's positional vocabulary is **deepest-anchored** — `_` counts
  from the deepest wire. With the resource on top, the value width
  between the data and the resource is not statically known, and every
  padding FIXES it: `bump : • =Counter> •`, `_ bump : a0 =Counter> a0`,
  `_ _ bump : a0 a1 =Counter> a0 a1`. Writing "bump the Counter,
  whatever lies below" would need `ρ Counter ⇒ ρ Counter` — a SPLICE,
  the construct design-flexible-arity.md deleted for being
  non-principal. (This retroactively explains why `rotLast` existed at
  all: top-anchored routing needs it, and it died with the splice.)
- Bottom-anchored, every offset is known from the `use` header alone
  and the words stay width-polymorphic: `bump ... : Counter ρ0 ⇒
  Counter ρ0`, `_ bump ... : a0 Counter ρ0 ⇒ a0 Counter ρ0`.
- The preference for top-anchoring was that a pure stage is then a tidy
  `X ...` rather than `_ _ X ...`. But the ELABORATOR writes that
  padding — the elegance being protected is invisible at the surface,
  while the routability it costs is decisive.
- Consequence, recorded because it changes a display rule: the `=Name>`
  fold reads a **prefix**, not a suffix.

## Stage 3 as shipped (2026-08-26)

**A theory declares slots and laws; an instance supplies programs.**
Both are BLOCK declarations — a header line ending in `=`, then
indented lines, the same shape `def name =` already had. A theory's
entries are `slot : Σ ⇒ Θ` and `law name = <program>`; an instance's
are `slot = <program>`. Theory parameters are kinded exactly like
type-declaration parameters: a bare name is one wire, `...` a stack.

```braid
theory Monoid(a) =
    unit   : • ⇒ a
    op     : a a ⇒ a
    sample : • ⇒ a
    law leftUnit = (sample ; unit ... ; op) sample ; eq? ; (forget ; true | forget ; false) ; merge

instance IntSum : Monoid(Int) =
    unit   = 0
    op     = +
    sample = 7

instance StrCat : Monoid(Str) =
    unit   = ""
    op     = cat
    sample = "x"

def total  = use IntSum ; [op] unit ... ; foldExp     -- Intⁿ⁰ ⇒ Int
def joined = use StrCat ; [op] unit ... ; foldExp     -- Strⁿ⁰ ⇒ Str
```

**Nothing is inferred and nothing is dispatched.** `use IntSum` selects
an instance BY NAME, and the selection is a RENAMING at elaboration:
each slot resolves to a generated def, so it costs nothing per call,
once per scope. That is precisely the trade the "Why not typeclasses"
section below records — you give up inferring *which* instance and get
back annotation-freeness (no ambiguity forcing annotations Braid has no
syntax for), coherence in a structural type system (`(• | •)` being
both Bool and a sum makes instance-uniqueness ill-posed), and freedom
from higher kinds.

**`use` now takes BOTH resources and instances, and mixes them
freely.** One word for both kinds of scoped selection — stage 4's form
did not need a sibling.

**The audit — three checks, three distinct messages, all verified.**

1. Slot signatures are checked against the theory, read at the
   instance's own argument: *instance Bad: slot 'unit' is • ⇒ Str but
   theory Monoid declares • ⇒ Int*.
2. Completeness, and no extras: *instance Partial: no binding for 'op'
   (declared by theory Monoid)*; *instance Extra: 'huh' is not an
   operation of theory Monoid*.
3. A law must be a program of type `• ⇒ Bool`: *law 'silly' of I must
   be a program with type '• ⇒ Bool', but is • ⇒ Int*.

**Laws RUN.** They are ordinary Braid programs and they execute at
module start, before main. A failing one rejects the module: *law
'leftUnit' fails for instance BadUnit: an instance must be an audited
model of its theory*. That is this note's own phrase — the
laws-are-programs doctrine given a front door — with a front door now
actually cut. See `examples/theories.braid`.

**The limits, stated plainly.**

- A law body must be a **single line**: the block parser reads one
  entry per line.
- A law over a **parametric** theory cannot invent a value of `a` —
  there is no way to write a literal at an unknown type — so a theory
  that wants sampled laws must declare a witness slot (`sample : • ⇒
  a`) and each instance supplies it. That is not a workaround: an
  audited model supplies the evidence its audit runs on.
- Laws are checked by **running**, on whatever samples the program
  names. Next to QuickCheck this is property testing's poor cousin —
  no generation, no shrinking. What is different is that the check is
  part of *being an instance* rather than a separate test suite.
- `theory` and `instance` are file declarations, not REPL lines (the
  REPL says so).

## The design, zoomed out

**Effects are wires.** The classical effect zoo decomposes into
structure Braid already has: state = a threaded wire, writer/log = a
wire, reader = closure capture, exceptions = the railway sum,
nondeterminism = List. Verified in-session: a `Log GameState` arrow is
expressible today as `A GameState Str ⇒ B GameState Str`, with pure
stages threading the bundle by a single `...` (data at the bottom,
bundle on top). *Amended 2026-08-26, at implementation: the bundle
rides at the BOTTOM and the data on top — `GameState Str A ⇒ GameState
Str B` — because Braid's positional vocabulary counts from the deepest
wire; the shipped section above has the argument.* Only **IO** is
irreducible — a genuine observational capability, not plumbing.

**IO is a linear wire.** The true string diagram for a premonoidal
category (Jeffrey 1997) reifies effect order as one linear control
wire threading every effectful box; pure boxes float free. Interchange
holds/fails as topology. GHC's `State# RealWorld` and Clean's unique
`World` are this wire in production. Braid's `=IO>` label (displayed on
the arrow like a resource name) is bookkeeping for that wire, unexposed
because Braid lacks linearity — so far.

**Labels are the wires' names.** `A =IO Log GameState> B` is not a
list of effect labels; it is the set of resource wires the def
touches. Three zoom levels, one semantics (ambient desugars to
explicit):

| level | user writes | user sees | linearity exposure |
|---|---|---|---|
| ambient (default) | `note`, `print`, plain `;` in `use` scopes | `=Log>`, `=IO>` inferred | zero — the elaborator draws the wire, so linearity holds by construction |
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

*IMPLEMENTED 2026-08-26 (stage 3, above). The resolution mechanism
turned out to be a **renaming at elaboration**: `use IntSum` rewrites
each slot to a generated def for the rest of the scope, so there is no
dictionary, no dispatch, and no per-call cost — resolution happens once
per scope, by name.*

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
  code. *Settled by stage 4: a `scope` is syntactically what the
  binders already were — `use R…` takes the rest of the enclosing scope
  as its body, the same rule as `x y ->` and `-> x y`, so the form
  needed no new notion of scope.*
- Shipped limits of the `use` elaborator (both relaxable): one resource
  operation per stage, alone in that stage; and no operation that
  touches two resources at once. Ladder step 2/3 licences are untouched
  by this — these are routing limits, not commutativity ones.

## The staging (1, 2, 3 and 4 shipped; 5 remains)

1. IO bit on Arrow (the old arrows-plan stage 1; display `=IO>` as a
   label like resource names, pure displays as `⇒` so all tests survive).
   **SHIPPED 2026-08-25** — see "Stage 1 as shipped" above; the placement
   rule it was to carry became the left-to-right decree instead.
2. **Resource** declarations + `=Name>` display sugar over wire
   suffixes. **SHIPPED 2026-08-26** — see "Stages 2 and 4 as shipped"
   above; *suffix* became *prefix* at implementation (amendment there,
   and on the bullet below). (Decisions taken 2026-08-25, before
   implementation:)
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
     wires ride on top, in order. *Amended 2026-08-26, at
     implementation: the juxtaposition and its order survived, the END
     did not — threaded wires ride DEEPEST, so `=A B>` folds a leading
     PREFIX. Top-anchored routing needs a splice (`ρ Counter ⇒ ρ
     Counter`), which is exactly the non-principal construct
     design-flexible-arity.md deleted; bottom-anchored, every offset is
     known from the `use` header alone. The argument in full is in the
     shipped section above.*
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
3. Theories/instances — the machinery tier. **SHIPPED 2026-08-26** —
   see "Stage 3 as shipped" above; the `use` half of this entry had
   already gone out as stage 4, and theories, instances and their
   runnable laws followed it, sharing the same `use` word.
   **Architecture settled 2026-08-26, from a survey of the checker**
   (and confirmed by the implementation)**.**
   The note has been saying ε (effects) and γ (ambient bundles) are ONE
   variable sort. In the code they are not, and the difference is the
   whole design:
   - `unifyEff` ABSORBS — an open grade takes on the other side's
     labels. That is why `io` propagates through composition with no
     joins and no annotations: inference discovers it.
   - `unifyStack` is rigid and front-anchored. `(STail v, st) ->
     bindStackVar s v st` swallows the entire rest greedily, and there
     is no suffix matching anywhere in the unifier.
   So a resource suffix can never be INFERRED — a remainder variable
   eats `Log Counter` and nothing records that they were there. Stage 4
   is therefore an ELABORATOR, not a solver extension: it puts the
   wires at statically known positions and lets inference CHECK the
   result. (Inference as the verifier of elaboration, not an input to
   it — which is also what keeps the error messages tractable.)
   It can be syntactic, consulting `Env` for arities the way
   `compileAbsOpen'.classify` already does, on three commitments:
   - **(a) `use` names only resources, never raw stacks.** One name =
     one wire, so the parser survives on syntax alone. This is what
     nominality bought.
   - **(b) Resource wires are topmost, in `use` order, never reordered
     mid-scope.** Lets each stage take a fixed `_`-prefix instead of a
     solved permutation. A word that consumed one resource and
     produced a different one would break it and force the
     type-directed path. *Amended 2026-08-26: DEEPEST, not topmost —
     the commitment is that the position is statically known, and only
     the bottom end gives that (see the amendment in the shipped
     section). Everything else in this bullet stands, `_`-prefix
     included.*
   - **(c) Open-arity atoms keep their final-atom obligation.** A
     stage's resource `...` and an open word's `...` are the same slot;
     if both want it, reject rather than permute.
   The template is `dataFoldSrc`, which already generates `_`-padded
   routing from a declaration alone, with zero unification, and hands
   the result to the ordinary parse+infer path.
4. Ambient threading (elaborator frames pure stages inside `use`).
   **SHIPPED 2026-08-26** — see "Stages 2 and 4 as shipped" above. The
   frame a pure stage gets is `lift`, which shipped as an ordinary
   prelude word; the elaborator writes its `_`s directly.
5. Resource mark + linear `World` + explicit/split levels. **NOT
   shipped** — the one stage still position only.
Each stage independently useful; 1–2 were small; 4 was the big
ergonomic payoff, and was cheap because 2 made the wires nominal; 3
rode in on 4's `use`; 5 unlocks the power tier.
