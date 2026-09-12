# Elaboration as a library — functors, Code, and the transport of `⇒`

STATUS: CONVERGED on the design; stage 1 (the splice check) shipped
2026-08-31 as e812da5. This note consolidates the 2026-08-26…31
design discussions. The staging and per-stage mechanics live in the
working plan; this is the record of *what* was decided and *why*, in
the style of design-effects.md: dated decisions, amendments where
implementation or a later argument reversed one, honest gaps at the
end.

## The position

The elaborator is already a set of `Code ⇒ Code` functions — binder
desugaring (abstraction elimination to wiring), the railway operators
`>=>`/`>?>`/`>!>` (fixed term rewrites in the parser), `use` routing
and instance renaming, the generated data folds. Every one is a
function from program-spine to program-spine, hard-coded in Haskell.
`weave` — one line of Braid, `(f h -> [(s -> (s ; pack) h ; append)]
f ; flatMap)` — proved the language expresses such functions itself.

So the house rule ("special forms die or become words") applies to the
elaborator: make the set open. A **functor** is any pure `Code ⇒ Code`
word; `use` applies it to the rest of the scope at elaboration time.
The compiler's rewriting layer becomes user-space.

The north star, stated once: **transport.** A Braid program —
especially once reflected — is a morphism of the *free* cartesian
category over its vocabulary. Initiality means there is a functor from
it to every category with the right structure, determined by where the
generators go. The evaluator is one such functor (the default
interpretation, into values). A `use`-applied functor is another —
into instrumented code, circuits, dual numbers, weighted lists.
`unparse` plus a backend is a third, into categories that are not
inside Braid at all. "Doing things in other categories" is not a
feature to add; it is the factorization the language is built on, and
this arc makes the middle case — user-written transports, applied at
elaboration, audited by runnable laws — a first-class construct. What
the design refuses is only *unmarked* transport: the reader must be
able to see, in the text, which category a block is in.

## The five invariants

1. **Inference never sees a functor.** Everything that reaches `infer`
   is a plain Term; the type system is untouched and principality
   undisturbed.
2. **Elaboration never performs IO.** A functor's arrow must carry no
   `IO` — the io label doing double duty as the phase distinction
   (Harper–Mitchell–Moggi, enforced by machinery that already ships).
   Purity here does not mean totality: a functor can loop, so
   elaboration-time evaluation is fuel-bounded.
3. **No expansion is trusted.** Every splice is re-inferred at its
   site with principal types. This is also why the functor layer does
   not inherit `evalCode`'s hole: the expansion is typed before
   anything downstream depends on it.
4. **No names, no capture.** Code is stages of atoms over wires;
   binders are compiled to wiring before reification. The macro-hygiene
   problem — the one Lean needed a research paper's worth of scope
   machinery for — vanishes by representation. Concatenative syntax is
   the degenerate case where there is nothing to capture.
5. **Markers are written, receipts are inferred.** A scope *names* the
   labels whose elaboration rules apply (`use K …` — one line,
   refactor-stable). The arrow's manifest (`=K>`) is inference's
   *record* of what the elaborated code needs, propagating by
   unification. Rewriting is never triggered by inferred types.
   (Since 2026-09-08 the manifest also records what REWROTE the code:
   `use F` mints `F`. Minting is still a consequence of a written
   marker, never of an inferred type — see the provenance amendment.)

   **Amendment (2026-08-31, the Lean question).** "Type-triggered
   rewriting is circular" is true of *this* language, not of languages
   generally — Lean ships type-directed elaboration soundly. The
   difference is where the directing type comes from: Lean's
   elaboration is bidirectional, and the expected type flows down from
   things the user *wrote* (signatures, ascriptions, goals). That is
   markers-written/receipts-inferred with types as the markers. Braid
   has no written types — the no-annotations bet — so there is no
   expected type before inference, and inference cannot run before
   elaboration fixes the term. The scope header is Braid's written
   type, spelled as a name. If optional type ascriptions ever land
   (plausible independently, for error messages), type-directed scope
   selection reopens as exactly Lean's move, and would be sound for
   the same reason.

## The one ordering rule

A functor must be checked and runnable before its first `use` — it
actually executes there, against the prefix of the module above it.
This is the only place in the language where source order is semantic
(ordinary defs became mutually visible in the theories arc; laws run
after all checking). Forth has the same rule for the same reason: the
dictionary a compile-time word sees is the dictionary so far.

## The taxonomy: four levels, split by what the type can promise

Two representations of a program, with an honest map between them:

| | type | build | inspect | typing |
|---|---|---|---|---|
| typed code | `Fn⟨Σ ⇒ Θ⟩` | `compose`, `lift`, `around`, CSP | ✗ | full arrows, today |
| untyped code | `Code = List(Stage)` | splice | total — it is a list | recovered by re-inference |

`reflect : Fn⟨ρ0 ⇒ ρ1⟩ ⇒ (Code | Str)` is the erasure between them,
and the erasure is forced: cutting typed code at a stage boundary
yields `∃Ξ. Fn⟨Σ ⇒ Ξ⟩ × Fn⟨Ξ ⇒ Θ⟩`, an existential cut type, and HM
has no existentials. `Code` is precisely the quotient of typed code by
its intermediate types. (MetaML forbids inspecting typed code for this
reason; the systems that allow both pay in modal machinery. Braid
takes the Template-Haskell/Scala-3 position: typed quotes for
building, an untyped layer for inspecting, checked splices between.)

The levels:

- **Level 0 — wiring on code values.** Code is a value; `dup`, `drop`,
  `swap` act on it; `(f -> [f ...])` is cross-stage persistence
  (`a ⇒ Fn⟨ρ ⇒ a ρ⟩`) and `ev` is its inverse. Ambient structure,
  not machinery.
- **Level 1 — typed macros**, `Fn ⇒ Fn`: `compose : Fn⟨ρ0 ⇒ ρ1⟩
  Fn⟨ρ1 ⇒ ρ2⟩ ⇒ Fn⟨ρ0 ⇒ ρ2⟩`, `lift` (strength — in the prelude all
  along), `around`, retry/bracket/span wrappers. Fully typed, checked
  intermediate types, parametric by their row variables (they *cannot*
  inspect — free theorems). **Gluing programs lives here and needs
  neither `Code` nor `evalCode`.**
- **Level 2a — by-generators functors**: `stagewise`/`atomwise` —
  a generator map extended homomorphically (`flatMap` on the spine).
  Determined by the action on generators, so **functorial by
  construction**: respecting `;` is unviolatable, not audited.
  Renamings, interposition (tick, trace), dialects, `arr`/`thenP`
  interpretation all live here. (Functoriality is not liftability —
  see the 2026-09-08 amendment for the rows that are *known to
  type*, of which `interpose` is the checked one.)
- **Level 2b — whole-spine** `Code ⇒ Code`: routing, optimizers,
  anything needing context beyond one generator. Functoriality, if
  claimed, is **audited** — laws at module start, `sameCode` deciding
  the wiring fragment.

Each level down trades a static guarantee for reach, and the language
makes you say which rung you are on.

## The construct

```
functor Traced = tracer          -- tracer : Code ⇒ Code, pure — checked here

def process =
    use Log Traced               -- one scope form for all three kinds
    …
```

Decisions, dated 2026-08-29 unless noted:

- **Keyword `functor`** — the categorically correct name (it is one,
  from the free category). Collision management: the
  instance-parameterized defs `f(C)` are called *templates* in all
  docs, never functors; one MANUAL sentence disambiguates for Haskell
  readers (`Functor`/`fmap` ≠ this).
- **No `macro` keyword.** A functor's word is any def whose type
  unifies with `Code ⇒ Code` at pure grade. Existing combinators
  (`weave`, `transposeC`) qualify with no ceremony.
- **No new Term node.** `Use` already carries names; the elaborator's
  partition grows a third kind (instances / resources / functors).
- **Header order is not a decree.** Functor composition of
  `Code ⇒ Code` words *is* `;`, so `use Metered Circuitry` is sugar
  for one composed functor, applied left-to-right in pipeline order:
  `⌜body⌝ ; metered ; circuitry`. When order carries meaning, the
  recommended spelling is `functor Both = metered ; circuitry` — a
  named, testable def. Instances (renaming) and resources (routing)
  apply first, so a functor always sees fully routed code.
- The typing rule the hook enacts:

  ```
  M : Code ⇒ Code  pure     ⟦M⟧ ⌜body⌝ ⇓ c     splice(c) : Σ ⇒ Θ
  ──────────────────────────────────────────────────────────────
                       use M ; body  :  Σ ⇒ Θ
  ```

  Three premises, three phase-crossings: M checked statically (once),
  M run at elaboration (per site, fuel-bounded), the output inferred
  statically (per site, principal). Errors carry the `unparse` of the
  expansion — functors are debugged by printing what they wrote.

## Transport, categorically

Recorded because the vocabulary keeps earning its keep:

- The ambient system is a **graded Freyd category** over the label
  semilattice: an identity-on-objects inclusion of the pure cartesian
  base, with the grade row as the grading. Each carrier-label fiber is
  a **Power–Robinson state construction** `K_E(Σ,Θ) = C(E⊗Σ, E⊗Θ)` —
  *representable*, which is the design's distinctive claim: fiber
  composition IS base composition of representatives, so `;` never
  changes meaning and the elaborator's padding (strength, `lift`) is
  the only glue. The left-to-right decree for effectful atoms is
  premonoidal non-interchange showing through.
- **Effects are arrows with named state; Hughes arrows are arrows with
  hidden state.** Named state (`resource`) folds into the manifest;
  hidden state (`Circuit(a,b)` — the existential/coend completion of
  the same state construction) stays a value, entered by a functor
  scope, run via install/reify (pack and unpack of the existential).
- A functor scope is an identity-on-objects functor out of the free
  category — Elliott's compiling-to-categories as a user-level
  construct, with the advantage that Braid programs already *are* the
  free-category morphisms (Elliott's hard part, recovering categorical
  structure from lambdas, is free here).
- The manifest records a transport's **consequences**, never the
  transport itself: a functor that adds effects shows up as those
  effects (`=Fuel>`, `=IO>`); a functor that moves to a non-representable
  category shows up as different types (`Circuit(Int,Int)`); the cause
  is the `use` line, one line up. Only representable structure can be a
  label, because only it leaves a wire there is anything to fold.

## Amendment (2026-09-04): the lift view, front and center

The user-facing face of every functor is one function:

    Fn⟨a ⇒ b⟩  ⇒  (something better)

— its action on morphisms. Level 1 is that function *directly*
(`logged : Fn⟨a ⇒ ρ⟩ ⇒ Fn⟨a =Log> ρ⟩`, `play : Fn⟨Int ⇒ Int⟩ ⇒
Fn⟨• =Game> •⟩`, `lift` itself); a `use`-applied `Code ⇒ Code` functor
is the same action applied to a whole region's spine instead of one
quotation. Teach the level-1 form first — "take an ordinary function,
get back the better version, in one word" — because it is the
experience the arrows literature promises, and here it needs no
classes and no lifting choreography (`examples/lifting.braid`). The
reframe worth stating in every doc that touches this: **lifting is
word application, not type coercion** — the cool behavior arrives
because you applied a word, and that application is itself the mark.

On marking, since the question recurs: a level-1 lift is marked by its
own application in the text, and its *receipt* is the result's arrow
(`=Log>` appears). A region functor is marked by its `use` header. The
only unmarked residue is type-unchanged provenance for region functors
— exactly the OPEN coeffect/tagging question below, unchanged by this
amendment.

## Amendment (2026-09-08): the fibration picture, and the functors known to type

Stage 4 shipped `interpose`, and with it a correction to how level 2a
was described above. "Functorial by construction" is true of
`stagewise`/`atomwise` and is *not the property anyone wants*:
`stagewise [s -> s ; garbage]` respects `;` perfectly and produces
Code that will not type. The property that matters is
**liftability**.

`reflect : Fn⟨ρ0 ⇒ ρ1⟩ ⇒ (Code | Str)` is a forgetful functor from
typed programs (the total category) to `Code` (the base). Level-1
macros work in the total category and carry a typing along by
construction. A `Code ⇒ Code` functor works in the base, and typing
its output is a **lifting problem** — does a typing exist over this
base morphism? — answered by re-inference at the splice. "Won't run" =
no lift exists. (Melliès & Zeilberger, *Functors are type refinement
systems*: a type system is a functor from typed to untyped terms, and
the questions are about lifts. Conjecture worth chasing, NOT recorded
as fact: principal typing = cartesian lift, i.e. `reflect` is a
fibration on its typeable part.)

**The functors known to type** — one theorem: a functor out of the
free category `Code = Free(G)` lifts whenever it is determined by an
action on generators (or on typed local patterns) whose images have
schemes *at least as general* as what they replace — a morphism of
refinement systems. Six rows, five checked ONCE at declaration and
free at every use, one checked per program:

1. level 1 (`Fn ⇒ Fn`): never leaves the total category;
2. tensoring with a resource, `E ⋉ –` (`use E` routing; abstraction
   elimination is the same functor with the parameter block as `P`);
3. whiskering, `interpose [η]` with `η ∈ K(I,I)` — an endomorphism of
   the unit, whiskered by the cut; with a resource, `η ∈ C(E,E)`.
   In Jeffrey's graphical premonoidal picture these are the boxes
   touching only the control wire, and the resource wire IS that
   wire. `interpose [η]` is the functor out of `Free(G)` given by the
   graph morphism `s ↦ s ; (η ⋉ cod s)`; the class of all of them is a
   monoid action of `K(I,I)` on `Free(G)` by right-whiskering, where
   the monoid multiplication is `append` on the marker Code:
   `interpose [η₁ ; η₂]`. Note what is NOT the action of the product:
   `interpose [η₂]` applied after `interpose [η₁]` instruments η₁'s
   insertions too (Code carries no provenance, so the second functor
   sees one spine, as it stands — `s ; η₁` becomes `s ; η₂ ; η₁ ;
   η₂`). Compose markers, not interpositions, when the product is
   meant. Liftability = being in the image of the whiskering map
   `K(I,I) × Ob → Mor`. Checked by **subsumption**: `scheme(η) ≥ ∀ρ.
   E ρ =IO> E ρ` with ρ skolem and E read off η's own arrow.
   Unification would bless `Int ρ ⇒ Int ρ` at `ρ := Int ρ'`. The
   check is possible because Code carries names, not closures — `.η`
   re-instantiates at every splice; a `Fn⟨ρ ⇒ ρ⟩` value is at one ρ
   (the rank-1 wall). Cross-references: Plotkin–Power arity-one
   algebraic operations (`tick : 1 → 1`); Dantas–Walker harmless
   advice; the `a ⇒ a` counterpoint is `K(I,I)` being nontrivial (an
   io `ρ ⇒ ρ` is not central: naturality holds on the wires, not on
   the log).
4. models (`use Inst`; `atomwise` with typed generator images) —
   `checkInstance`;
5. local rewrites `p ↦ q` with `scheme(q) ≥ scheme(p)` — the `rule`
   design of stage 5b. **Unification blesses a call; subsumption
   blesses a rule.** A `replace : Fn⟨a ⇒ b⟩ Fn⟨a ⇒ b⟩ Code ⇒ Code`
   types, and the shared variables say only that p and q have a
   common instance — symmetric, where "q may stand wherever p stands"
   is not (verified: `dupInt ↦ dup` safe everywhere; `dup ↦ dupInt`
   breaks the `Str` program; `two ↦ dup` narrows `a ⇒ Int` to `Int ⇒
   Int` and the witness refuses it). The sufficient property is
   rank-2, inexpressible as a `Fn` type, and already has a routine
   with three consumers: `subsumes`. So a rule is a declaration over
   names, checked once.
6. **`lift2`** — the runtime lift of any `Code ⇒ Code` functor: `def
   lift2 = (m f -> [f (m (f >> getCode) >> ev >> (c -> c)) ... >>
   evalAs >> (... | drop ... >> f ... >> ev) >> merge])`, typed
   `Fn⟨Code ⇒ Code⟩ Fn⟨Γ ⇒ Δ⟩ ⇒ Fn⟨Γ ⇒ Δ⟩`. Output arrow = input
   arrow by construction; the untyped middle is discharged at the
   boundary by the fibre the program started in, per program, and a
   refused rewrite runs the original. This is the runtime counterpart
   of `use F`: the two ways a level-2 functor becomes level 1.

Non-local functors (delete, reorder, reverse, neighbour-dependent
choice) are outside the class permanently: level 2b, re-inferred per
application, audited by laws. The MANUAL carries the table; the
"marker tracer" (`examples/traced.braid`) is the worked instance of
row 3 — the stage that lifts everywhere reads no wire and gets its
content from the functor, which has the stage in hand.

## The splice check (stage 1, shipped 2026-08-31)

`evalCode : Code Γ ⇒! (Δ | Str Γ)` let the caller choose Δ and never
checked it — the one deliberate hole, now closed: each site is stamped
after solving with the type its context settled on; at runtime the
spliced code's inferred output is unified against the stamp; mismatch
rides the miss track. A stamp that would generalize is frozen into
rigid constants (`∃0` — skolems, not existential types: no `∃a. T`
former, no pack/unpack; they unify only with themselves), so callers
stay parametric. The honest cost: `box : Code ⇒ Fn⟨ρ0 ⇒! (∃0 | Str
ρ0)⟩` — deferring the *run* costs the result's *type*. Full record in
spec-code.md and design-metaprogramming.md (amendments of the same
date).

The skolem is the **residue of erasure that could not be recovered**:
a functor's output exists at elaboration, so re-inference recovers the
erased type totally — no residue, no `∃` ever appears from the macro
layer. `evalCode`'s code exists only at runtime, so the type can only
be checked late, and freezing is what soundness costs when the
expectation escapes a scheme. Same obstruction as the untyped-`Code`
decision, at the other end of the pipeline.

**Decision (2026-08-31): `evalCode` is kept, removal reserved.**
Gluing needs level 1; the functor layer splices internally; `evalCode`
earns its keep only for code that did not exist at compile time (disk,
input, REPL-of-the-REPL). If it is later dropped, the stamp machinery
is a deletion, not a redesign, and `∃` goes with it.

**AMENDMENT 2026-09-07: the stamp is replaced by a witness, and `∃` is
gone.** The reservation above was exercised. Stamping was sound but
paid for ONE primitive with skolems threaded through unification,
generalization, display, and the REPL — and its cost fell where the
paragraph above admits: deferring the run cost the result's type. The
replacement applies invariant five to runtime splicing. *The directing
type is written:*

```
evalAs : Fn⟨Γ =ε> Δ⟩ Code Γ =ε> (Δ | Str Γ)
```

The first operand is a **witness**: an ordinary program whose arrow is
the expectation the loaded code must meet, never applied, spelled as a
value because Braid has no type syntax inside terms. A program at the
type you mean is how you name that type. The context types against
`Γ ⇒ Δ` with ordinary variables, so nothing existential enters the
system; at runtime the loaded code's scheme must **subsume** the
witness's arrow.

Subsumption, not unification, is what makes it sound: types are erased
by then, so the check cannot know which instantiation of a polymorphic
witness the context chose, and must demand code that handles every one.
Under `[_]` (`a ⇒ a`), code that is merely `Int ⇒ Int` is refused —
unification would accept it at `a := Int` and then run it on a `Str`.
The routine is `subsumes`, and it is the same check at two phases: a
theory slot's declared arrow is an expectation written in the theory, a
witness is one written in the program. (Writing it exposed a live hole
in the other caller — `checkInstance` compared stacks only, never the
effect row, so an io body under a pure slot passed and `functor F =
<that slot>` carried IO into elaboration. Fixed the same day.)

Three things are gained beyond the deletion. Results are ordinarily
typed, so a boxed program's output is usable rather than merely
forgettable (`box : Fn⟨ρ0 ⇒ ρ1⟩ Code ⇒ Fn⟨ρ0 ⇒ (ρ1 | Str ρ0)⟩`). The
witness is a real program, so it is the fallback: on a miss it is still
there to run. And sharing ε with the witness makes the grade a
**sandbox** — a pure witness admits only pure code and the splice stays
pure, where `evalCode` was unconditionally io.

The cost is real and worth stating: a cut must now state its own
witnesses. Splitting a program names an intermediate the whole program
never mentions, and it differs per cut — after one stage the wires are
`Int Int`, after two just `Int`. That is exactly the existential cut
type from the typed-code section above, and the witness is where the
existential went: not eliminated, but *discharged at the site by the
programmer* instead of inferred and frozen. The type between two halves
is a fact about the cut, not about the program, so someone has to say
it. `examples/cuts.braid` says it five times, once per boundary, and
reads better for it.

## Laws for functors

Functor laws are *easier* than value-level laws, because functor
outputs are `Code` — ordinary list data. So structural `eq?` gives
syntactic equality today; `sameCodeC` (planned) gives semantic
equality on the free-cartesian wiring fragment, where the word problem
is decidable. Law kinds:

1. **Functoriality** — free (unviolatable by construction) at level
   2a; audited only for raw whole-spine functors.
2. **Identity preservation.**
3. **Interaction laws** between a pair of functors — `s ; F ; G` vs
   `s ; G ; F` on witness programs: the graded-distributive-law
   question landed as a runnable law an instance must pass.
4. **Idempotence** — `F(F(p)) = F(p)`: true of optimizers,
   normalizers, canonicalizers.
5. **Image membership** — for *idempotent* F only, "p is in the image
   of F" ⟺ `F(p) = p`: an assertion about a particular program (it
   lives beside the def), whose meaningfulness depends on law 4, so a
   theory offering it must declare idempotence. Verified 2026-08-31
   that the fixed-point test does NOT characterize interposing
   functors (weaving twice interposes twice) — their image can be
   remembered, not detected. See the open question below.

The audited-optimizer position is worth naming: rewrite rules proved
by the language's own normalizer at module start sit between GHC
RULES (user rules, trusted, silently miscompile when wrong) and
Alive-style external verification — in-language, zero-infrastructure,
refusing rather than guessing outside the decidable fragment.

## Amendment (2026-09-08): provenance labels — the receipt is a stage

Shipped as stage 4½. Invariant five said receipts are inferred; until
now the only receipt a functor left was whatever its rewrite happened
to make the code *need* (`interpose [burn]` moves the spine into the
Fuel fiber, and `=Fuel>` is the record). A functor that changes no
requirement — a tracer, an optimizer, a twinning transport — left
nothing at all, and "which functors built this word" was not a
question the type could answer. Now it is:

- `EffRow` widens from `Bool` to `Set String`. io is one label among
  many, spelled `IO` in exactly one place in the source; unification is
  the same label-absorbing row algorithm, now on sets. Two open rows
  with each side carrying a label the other lacks bridge through a
  shared residual tail, named from the pair (`solve` is a pure fold
  with no fresh-name supply, and a pair can be bridged only once —
  both its variables are bound by that step). Labels are **idempotent**:
  a set, not a multiset, which is why `⟨A|ε⟩ ~ ⟨B|ε⟩` is satisfiable
  at `ε := ⟨A B|υ⟩` and why a tail may absorb a label the other side
  already carries.
- `use F` **mints** `F`, unconditionally, onto everything it
  elaborated. Composition carries it to every caller by row
  unification, so `=Traced>` on a word two calls away is a fact about
  how that word was built.

**The mechanism is the fragment.** The only way to put a label on an
inferred arrow is to compose with an arrow that carries it — that is
how `print` has always minted io. So the receipt is a WORD:
`use@F : ∀ρ. ρ =F> ρ`, `pass` with a label, prepended to the
expansion. A unit endomorphism whiskered by whatever the cut carries:
stage 4's `K(I,I)` again, at zero cost, doing nothing but being
typed. Consequences worth stating, all verified:

- It is a stage, so it **reflects with the code** it was minted onto
  (`use@Ticked >> dup >> "tick" pass >> …`) and re-inference at a
  splice site recovers the label rather than losing it.
- It cannot be written by hand. The elaborator walks the source before
  any expansion is spliced in, and refuses the name there: *a label is
  minted by a scope, never written by hand*. Without that check the
  label would be an annotation, and provenance that the author can
  forge is not provenance.
- The **sandbox generalizes for free**. `evalAs`'s witness, a theory's
  declared slot arrow, and any `Fn⟨…⟩` written in a declaration all
  compare manifests by subsumption, so an unlabelled `Fn` type now
  refuses instrumented code exactly as a pure one refuses io: *Cannot
  unify effects: IO Ticked vs pure*. An unlabelled type is a claim
  that no functor touched the code.
- `interpose` had to give up the reverse. Its check skolemized the
  effect tail along with the wires, which would refuse any stage
  carrying a receipt; the question it asks is about SHAPE, so it now
  skolemizes the stacks only (`subsumesShape`) and lets the manifest
  absorb. Enumerating the labels a stage may carry would be a list to
  keep up to date; an open tail is that list.

**What this does NOT do**, restated so the next stage does not
over-claim it: a label says the functor ran over this code, not that
every stage of it is in the functor's image. Adding one unmetered
stage to a `=Metered>` word keeps the label. That is the intersection
problem below, and it is still open — this stage makes the *union*
half exact, which is the half a type system with an effect row can
carry.

## Amendment (2026-09-09): imports, and why they needed no machinery

Shipped as stage 4¾. A module is a presentation (generators plus
defined words); an import is a morphism of presentations, and Braid's
kind is the **inclusion**: objects added, never merged (a clash is an
error naming both files), injective on names, the standing mono policy.

The implementation is the argument for the framing. Inclusion is
TEXTUAL — the imported file's declaration lines are placed above the
importing file's source and the composite is checked as one module — so
`type`, `resource`, `theory`, `instance` and `functor` all cross a file
boundary with nothing added to the checker. The alternative considered
and rejected was chaining checked modules as bases (the way the prelude
is threaded in): it works for defs, but a theory declared in one file
and instantiated in another would then need base theory/instance tables
threaded through `checkModuleWith`, own-vs-inherited handling in the
instance path, and a merge for every field of `Module`. Textual
inclusion has none of that, and it is what the presentation reading
predicts: a presentation has no notion of "checked already", only of
generators in scope.

What the loader owns, and why it is not elaboration: the file READ.
That is IO, at the same boundary that reads the program you ran, and
it is the reason `import` is not a Braid `functor` — those are `Code ⇒
Code`, per-def and pure. Import acts on the DICTIONARY (stage 8's
declaration-word class, `Str =Dict> •`). Elaboration still sees only
parsed declarations; invariant two is untouched. A module checked
without a file context — a REPL line, an embedded string — has nothing
to resolve an import against and says so rather than ignoring it.

Two continuations are left as continuations, not redesigns:
- *Qualified import is the inclusion composed with a renaming functor*
  (`import "g.braid" as G` sends `f ↦ G.f`). The renaming functor
  already exists — it is what `use Inst` does to slot names — so
  namespacing is instance renaming at file scope, never a second
  implementation. Deliberately not in v1.
- *Importing through a functor* (`import "rules.braid" use Traced`) is
  a functor applied to a whole presentation, which is file-scope `use`.

One thing did have to be added, and it was for the REPL, not for
files: `ModuleBase`, carrying the instance and functor tables a session
has accumulated. A file needs none of it (its imports are textually
present), but a session has no text to include into, so `:import` is
the only way a session gets a theory, an instance or a functor — it
cannot declare one.

## OPEN: coeffects, and tagging the non-idempotent image

The concern (2026-08-31): a maintained program drifts out of a
functor's image and nobody notices — `=Fuel>` says fuel is *used*,
not that *every* stage is metered, so one added unmetered stage keeps
the label and silently under-counts.

"Every stage did X" is not an effect and cannot ride the effect row:
effects **union** (any part io ⟹ the whole is io); image membership
**intersects** (any part outside ⟹ the whole is outside). It is the
dual — a graded *comonad* (Petricek–Orchard–Mycroft coeffects),
sharing machinery with capabilities/permissions. Options, in
ascending cost, **undecided**:

1. **Fixed-point law** (shipped with stage 5) — covers idempotent
   functors only.
2. **Nominal wrapper** — the scope boundary emits `Metered(a)`;
   consumers requiring metered input say so. No type-system change;
   costs explicit wrap/unwrap. The documented idiom meanwhile.
3. **Rigid labels** — reuse the stage-1 skolem machinery: F stamps its
   output with a marker that unifies only with itself; unmarked code
   cannot compose with marked code (forbid, rather than compute a
   weaker label). Needs pure wiring to be transparent (⊤) so the
   marker doesn't poison plain plumbing. Smaller than a row.
4. **Full coeffect row** — intersection-semantics labels dual to the
   effect row. The principled version; an arc, shared with
   capabilities.

Also noted: for "every stage must do X" specifically, **linearity**
(the row arc's linear `World`) makes skipping X a type error rather
than a silent omission — possibly the more direct fix than any
tagging.

## What a functor can silently change — the bounded answer

A pure functor that preserves types can change behavior only in what
the type system already declines to track: **termination** (dead-code
elimination deleting a divergent computation) and **cost** (unrolling,
fusion, reordering of pure stages). Semantic changes are covered by
laws; observable changes surface in the manifest; the remainder is
exactly the two properties deliberately out of scope (cost needs a
non-idempotent grade monoid; termination was never tracked — the same
reason macro evaluation is fuel-bounded rather than totality-checked).
Recorded as a known boundary, not papered over.

**Sharpened (2026-09-04, from the `a ⇒ a` counterpoint).** The
crispest statement: Braid's free theorems hold only *up to termination
and cost*. Verified: `a ⇒ a` is inhabited by the identity, by the
identity-at-a-cost (`(x -> 1000 >> (n -> n) >> drop >> x) : a0 ⇒ a0`),
and by divergence (`def dvg = recurse` types `ρ0 ⇒ ρ1` — divergence
inhabits everything). So "the receipt is the mark" fails exactly on
this slack: the wrong functor applied to `id` still reads `a ⇒ a`.
Consequences for the open routes: provenance tagging marks the
*derivation*, not the extension (the right alarm, not a proof);
quantitative grades close the cost half properly (`a ⇒⁵ a` — this
counterpoint is the standing argument for eventually paying that
arc's price); the termination half closes only with totality
checking, i.e. never, here.

[Superseded on the termination half — see the 2026-09-09 amendment
"recursion at a typed boundary" below. `recurse` is gone, and
divergence now types `ρ0 =Rec> ρ1`, so a bare `a ⇒ a` is no longer
inhabited by it: the half that was to close "never, here" closed by
subtraction rather than by totality checking, modulo an unfinished
audit of the primitive set. The cost half stands exactly as written.]

## Amendment (2026-09-04): representability demoted — the multimodal direction

The claim "a label can decorate composition but not change it; a
non-representable category must appear as values" was stated as a
theorem. Checked against the literature, it is an **artifact of the
single-judgment architecture**, not a fact about the design space. If
the typing judgment itself is indexed — `a ⊢_m b` at mode m — then
arrows in a different category carry their own objects and their own
composition judgmentally, and nothing needs to be squeezed into one
category's types. The type theory for this exists and is mature:

- **MTT** (Gratzer–Kavvos–Nuyts–Birkedal): a type theory parametrized
  by a *mode theory* — a strict 2-category whose objects are modes
  (categories), 1-cells are modalities (functors), 2-cells are
  transformations. Sound; canonicity; normalization; conversion
  decidable when equality of modalities and 2-cells is decidable.
- **Adjoint logic** (Reed; Pfenning–Davies lineage; Licata–Shulman,
  and Licata–Shulman–Riley's fibrational framework): modes may have
  *different structural rules* — linear here, cartesian there — and
  crossing between modes happens by adjunctions (the shifts), with
  the triangle identities as the crossing laws.
- **Melliès–Zeilberger**: "a type system is a functor" over a category
  of untyped terms — multiple refinement systems over one base, which
  is precisely the Braid picture (Code as the base; type systems
  above it).
- **Elevator** (Jang–Pientka 2024): metaprogramming *as* adjoint
  modes — code and programs are two modes C ≥ P, code is a suspended
  object at C, shifts move between them, and per-mode substructural
  discipline gives resource guarantees about generated code. Our
  phase distinction (Code/program, the ordering rule) is their mode
  preorder.

The mapping onto Braid is uncomfortably good: modes declared like
theories (the mode theory is a *presentation* — generators and
relations); `use`-style markers as modal shifts (modes are named,
never inferred — the marker invariant survives verbatim, since these
theories are checking-style and annotation-rich, and our markers ARE
the annotations); install/reify as the unit/counit of an adjunction;
laws between transports as 2-cells, with the decidability condition
on 2-cell equality landing exactly on the `sameCode`/fragment story;
linearity (the `World`) as a *mode*, not a special case; a Circuit
mode with its own feedback rule (ArrowLoop judgmentally).

What is NOT off the shelf: principal HM-style inference in a
multimodal setting under a no-annotations constraint — the literature
checks, it does not infer. The plausible line: with a finite nominal
mode set and marked shifts, mode inference never happens (shifts are
written) and per-mode inference is each mode's own HM problem. Open
research, honestly labeled.

**Objects: added, never merged (2026-09-04, from the "illusion"
question).** Rung-2 object sharing is representation, not illusion:
the fiber's `Int` is literally the base `Int` with the carrier beside
it (`:t!` shows `Log Str ⇒ Log` under `Str =Log> •`) — same objects,
new morphisms, the Kleisli/Freyd definition taken at its word. What is
policy rather than discovery: every supported transport is
**injective on objects** — identity-on-objects (carriers, grades) or
an embedding reified by declaration (`Circuit(a,b)` joins the shared
vocabulary as a nominal type). Functors that merge or quotient objects
are ruled out, because receipts must stay univocal: a displayed name
must mean one thing regardless of whose image you are reading. The
multimodal rung is where forced sharing WOULD become a lie — a mode
whose composition differs pretending its objects are stacks — which is
exactly why that rung gives modes their own objects and makes crossing
an explicit adjunction rather than a nominal pun.

**The bridge, which is why this costs nothing to defer:** the current
label route is the degenerate mode theory in which every mode shares
its objects and every modality is identity-on-objects. Grade labels
ship now; the multimodal architecture is their strict generalization;
moving later wastes nothing. Recorded as the third architecture in
the design space — (1) single judgment + labels (current), (2) rows
with carriers (stage 7), (3) multimodal (research-grade, with real
metatheory to lean on when wanted).

## Amendment (2026-09-04): rung 2½ — shared objects, owned composition

The ladder gains a rung, from the question "what if we kept
monomorphisms on objects but allowed other composition behavior?" —
which turns out to name a shipping architecture: **Hughes arrows** are
exactly a family of categories sharing one object vocabulary (Hask's)
while each owns its hom and composition. Braid's version substitutes
nominal modes + written markers for type classes, and runnable laws
for trusted instances:

```
mode Circuit = CircuitPipe        -- a mode IS an instance of theory
                                  --   Arrow(k): thenP/arrP/idP, with
                                  --   the category axioms as laws
def pipe = use Circuit ; f ; g    -- the scope inserts arrP/thenP
pipe : a =Circuit> b              -- the receipt carries the mode
```

- **Typing**: `Arrow` grows a nominal mode field (default base — zero
  cost when unused); unification requires modes equal; cross-mode
  composition without `arrP` is a type error; declared functors
  convert, laws audited.
- **Elaboration**: the stages-2–5 functor machinery, scope-marked, so
  markers-written is untouched.
- **Execution**: shared objects make representation cheap — the mode's
  hom reifies as the nominal `K(a,b)` data type, so the mode's
  judgment layer *refines* the value layer (Melliès–Zeilberger,
  load-bearing at last).
- **Inference**: survives because the term and type languages are
  unchanged and there are no mode variables — the mode is fixed per
  scope by the marker; mode-generic code is templates.

This dissolves the "the arrow must have one operational reading"
objection from the type-directed-composition discussion: that
objection was really about the run/construct ambiguity being invisible
in the type, and the mode tag is what makes it visible — `a ⇒ b` runs
now, `a =Circuit> b` denotes a machine, and the tag says which. The
operational-honesty requirement is discharged BY the receipt, not
violated by the second composition.

**Exits (2026-09-04, from "how do we get back out?").** Entering is a
marker; leaving is a model. Entry functors are generically available
(`arrP`, strength, a stamp); exit is a semantic choice — a functor
`K → Base`, an algebra of the mode (handlers-are-models, for
categories). Because homs reify as data, exits are ordinary words:
**observe/run** (eliminators — `stepC`, folds, `probe`; codata modes
exit only this way, which is why `theory Pipeline` already carries an
`observe` slot — a mode's exits are theory slots beside `thenP`),
**discharge through the adjunction** (`install`/`reify`, unit/counit,
triangle laws runnable; specializing to plain handlers for carrier
modes), and **interpret** (a functor out, given the generators'
images — reflect's purpose). The `use K` scope's END is free and
separate: leaving the scope costs nothing; leaving the type is where
the models apply. Round-trip laws are honest per mode (`reify ∘
install = id` runs; `observe ∘ enter = id` fails for Circuit and the
mode says so). Corollary nobody planned: a mode exporting no
eliminators is SEALED — abstraction and capability-safety fall out of
the mode system for free.

Exclusive to rung 3 after this: per-mode object languages and per-mode
structural rules (linearity as a mode). The ladder, complete:
(1) labels — shared objects, shared hom, annotation index;
(2) carriers — shared objects, representably-shifted hom;
(2½) modes-lite — shared objects, owned composition, reified homs;
(3) multimodal — owned objects, owned everything. Each a strict
specialization of the next; markers survive at every rung; inference
guaranteed at 1–2½, open at 3.

## Amendment (2026-09-09): the manifest, stated once — and modes as carrier labels

*Written because every remaining stage adds a kind of label and this
record had never said what a label IS. Supersedes the "mode field" of
the rung-2½ amendment above; keeps its objects-shared/composition-owned
reading.*

**What a manifest is.** Every arrow is `Σ =L> Θ` for a finite set `L`
of labels; the pure arrow is `L = ∅` and prints `⇒`. Braid is a
category graded by the join-semilattice `(P(Labels), ∪, ∅)` —
Katsumata's grades from an ordered monoid, with the monoid idempotent,
so a grade is a set and not a count. Composition: `Σ =L> Θ` then
`Θ =M> Ξ` is `Σ =L∪M> Ξ`.

Every label names a functor that a WRITTEN `use` applied to code — the
four io prims being the one pre-applied case — and the fibre over `L`
is the image of the composite of those functors. Union is the right
monoid because a label is *provenance* ("this code went through F"),
and provenance is monotone under composition. That is invariant five
in one sentence: markers are written, receipts are inferred, and only
a `use` can mint.

A label's **carrier** is what its functor adds to the objects:

| label | its functor | carrier | the fibre over it |
|---|---|---|---|
| resource `E` (stage 7) | `E ⊗ –`, routing | a wire of type `E` | `C(E⊗Σ, E⊗Θ)`, Power–Robinson's state construction |
| `IO` | `World ⊗ –`, pre-applied to four prims | the linear World, abstract | the same, with a carrier you cannot touch |
| functor receipt `F` | the declared `Code ⇒ Code` word | none | the base category, marked |
| mode `K` | `;` ↦ `thenP`, atoms ↦ `arrP`, from an instance of `Arrow(k)` | the hom-object `K(a, b)` | the category the instance presents, embedded as its hom-objects |

The order `L ≤ L ∪ M` induces a functor between fibres: for carriered
labels, whiskering by the extra carriers — what absorption does in the
solver and what `use` routing writes as `_` padding; for carrier-less
labels, the identity on homs, the fibre being a marked copy of the
base. One mechanism, four readings; every difference is in the carrier
column.

**Display** is where label and carrier meet: a carrier shared by both
sides folds away and the label stands for it. `Log Str ⇒ Log` prints
`Str =Log> •` today; `• ⇒ K(a, b)` carrying `K` will print `a =K> b`.
The label and the carrier are one thing said two ways — which is why a
mode receipt and a functor receipt look alike: they are alike.

**Inference** is design-effects.md's: label-absorbing row unification
with tails, an inferred manifest meaning "at least `L`", composition
unifying tails rather than joining sets (principal, single pass), the
join recovered by absorption. Written types are compared by
subsumption with the tail skolemized, so an unlabelled written type
refuses labelled code — the sandbox reads provenance exactly as it
reads io.

*(Amended 2026-09-12. **Composition joins** — the sentence two
paragraphs up always said so, and the implementation now matches it.
Composition emits a SUBEFFECTING constraint `part ⊆ composite` against
a fresh composite row and `solve` takes the least solution, so a
composite's labels are no longer pushed back into the rows its parts
share with their arguments; every derived higher-order word recovered
its prim's scheme. Unification is kept where two rows genuinely ARE one
row — inside a `Fn` type, and the shared `ε` of `ev`/`fix`/the folds —
and the subsumption rule above is unchanged, now stated as `⊆`, which
IS the semilattice order. Principal constrained types, Talpin–Jouvelot.
Full record and evidence: design-effects.md, "composition JOINS".)*

**Not a coeffect** (labels union; "every stage is in the image" is the
intersection half, still open), **not a rewrite trigger** (receipts are
inference's output), **not a count** (idempotent; cost is another arc).

**Modes, restated (Daniel, 2026-09-09).** The rung-2½ amendment above
gave `Arrow` a nominal mode field and made a K-word outside its scope
"the reified `K(a,b)` value" — two views of one word, and a rule that
composing two of them outside `use K` is a type error. Both go. A mode
is a label with a carrier, and nothing else on the arrow is new:

- `mode K = Inst` declares a functor (`;` ↦ `thenP`, atoms ↦ `arrP`)
  whose receipt is `K` and whose carrier is `k(a, b)`. `use K` applies
  it and mints `K`, like any functor scope.
- A K-word is, at the base, `• ⇒ K(a, b)` carrying `K`, displayed
  `a =K> b` by the fold. There is one view: the carrier.
- Outside `use K`, `f ; g` is base composition of two carrier-producing
  words — two circuits side by side, displayed UNFOLDED because the
  fold wants one carrier. Well-typed, honest, visibly not composition
  in K. Composition in K is written under the marker. No error, because
  there is no second kind of arrow to protect.
- Inside `use K` the elaborator leaves an atom alone iff it is a
  K-word — declared under `use K`, syntactic knowledge in the same
  table as functors — and `arrP`s everything else. The table is exact
  because **exits are the only way out**: a mode's eliminators
  (`observe`, step/run, `reify`) are theory slots, legal only outside
  `use K` and refused by name inside it, so every K-scoped word
  produces a carrier. Entering is a marker; leaving is a model.

**Templates, restated (same day; no `@`).** A def whose `use` names a
THEORY is a template — its body waits for an instance; a def whose
`use` names an INSTANCE instantiates every template it calls, the body
expanded there, renamed by that instance, re-inferred (no rank-1
wall). ML-functor application by the renaming that already exists;
`def f(C)` and `f@C` are withdrawn. And `@`-names are the compiler's
spelling only: `use@F` cannot be written, and `Inst@slot` joins it.

## Surface decisions (2026-08-29)

- **Declaration layer, direction 3**: fixed name-first surface
  notation (`def name = body` and kin) over an eventually-open table
  of declaration words carrying a `=Dict>` manifest — the metalanguage
  is the language, one resource richer. Forth-style parsing words are
  ruled out permanently: they break uniform reading and the
  hygiene-by-representation story; post-parse Code functors only. The
  keyword-initial surface is kept *deliberately* — it marks "an act on
  the dictionary" vs a morphism, the phase distinction made visible.
- **Type application stays applicative** (`List(a)`) until reflected
  types (TypeRep) land; postfix/concatenative types (ML's `int list`,
  and `Int Str Result` where ML needs tuples) are revisited as one
  decision with them, since neither alone pays for re-pinning ~680
  displayed-type expectations.

## Prior art audit (every joint load-tested by someone)

- **Factor** — `MACRO:`, quotations-as-lists manipulated by the list
  library, the compiler extensible from within: this design minus
  types, grades, and audits. **Forth** — IMMEDIATE words and the
  explicit dictionary: the common ancestor, and the model for the
  declaration layer.
- **Lean 4** — macros as ordinary functions of the language, run
  during elaboration, expansion re-checked; user-extensible
  elaborators; a custom hygiene system Braid gets structurally.
  Nearest single relative. **Idris** elaborator reflection — the same
  family; the model for exposing `infer` as a word if theory-checking
  is ever self-hosted.
- **MetaML/MetaOCaml** — typed code forbids intensional analysis;
  **Template Haskell** — untyped code with checked splices; **Scala
  3** — both tiers shipping together (typed quotes over an untyped
  reflection API), the closest architecture to the `Fn`/`Code` split.
  **Mœbius / layered modal type theory** — the price of having both
  typing and inspection at once; declined.
- **Racket** — languages as libraries, a real phase system; Braid
  replaces the phase system with the io grade.
- **Elliott, Compiling to Categories** — the transport vision as a GHC
  plugin; here a user-level word, with the free-category structure
  already present in the syntax.
- **GHC RULES vs Alive** — the two poles the audited optimizer sits
  between. **egg / equality saturation** — the upgrade path if rule
  sets grow.
- **Plotkin–Pretnar** — handlers correspond to models of the theory of
  the operations; Braid's instances are already models, so discharge
  is a wrapping functor, not a new construct.

## Formal grounding (checked 2026-08)

Free cartesian category word problems and normal forms (`sameCode`'s
license); initiality as the transport principle; graded monads
(Katsumata) and effect–coeffect grading (Gaboardi–Katsumata–Orchard–
Breuvart) for the row and its dual; Freyd categories as enriched
Lawvere theories (Staton) tying arrows, theories, and effects into one
object; premonoidal categories (Power–Robinson) for the state fibers
and the ordering decree; the existential cut-type obstruction for why
`Code` is the quotient of typed code.

## Amendment (2026-09-09): constructor parameters, and what a slot may name

*Stage 5a items 0 and 1. Two changes to `theory`, no change to
inference, and one renaming the record should carry: what this document
calls `theory Pipeline` — the one-object category `circuits.braid` could
express before this — is now `theory Arrow(k(_, _))`, and its `observe`
slot survives unchanged.*

**Slot-local variables.** A slot may name type variables the theory does
not declare; each slot is generalized over its own. Any lowercase name
that is neither a theory parameter nor a type in scope is such a
variable, and a `...` in a slot of a theory with no stack parameter is a
slot-local stack. This needed nothing from the checker: `declaredSlots`
already generalized a slot's arrow, and `checkInstance` already compared
a body to it by `subsumes`, so the variables only had to survive the
parser. The refusal is the parametricity message, naming the slot.

**Constructor parameters.** A theory parameter may be a type
constructor, its arity written as underscores — `theory Arrow(k(_, _))`.
The kind is visible because the two bare readings are already spoken
for: a name is a wire, `...` is a stack. The instance head names a
**declared data type**, not a type expression, and `slotArrowAt`
substitutes the NAME into the slot's arrow before any slot is
forward-declared. So this is the ML-functor move and not higher kinds:
`Ty` gains nothing, `TyParam` gains `PCon String Int`, and inference
never meets a constructor variable. `k(a, b)` is recorded as
`TData "k" [a, b]` inside the slot signature only, and the rename runs
before the wire/stack substitution so it cannot reach into a type the
instance supplied.

**Two consequences worth naming.**
- *Strength is what forced it.* `firstP : k(a, b) ⇒ k(Pair(a, c),
  Pair(b, c))` mentions `k` at three different pairs of wires. A `PWire`
  parameter can only name ONE hom-object, which is why the old theory
  was a monoid — a category with one object — rather than a category.
- *`Fn` cannot fill a constructor parameter.* It is built in and takes
  an arrow rather than wires. The refusal says so and names the one-line
  wrapper (`data Arr(a, b) = Fn⟨a ⇒ b⟩`), which is how
  `circuits.braid` gets its second, deliberately boring model.

**What stage 5c can rely on.** An instance of `Arrow(k)` is nothing but
a table of generated defs `Inst@arrP`, `Inst@thenP`, `Inst@firstP`, …
whose types are ordinary: `Inst@thenP : K(a, b) K(b, c) ⇒ K(a, c)` for
the concrete `K` the head named. `mode K = Inst` therefore has
everything it needs syntactically — the carrier's data name is
`inArgs`' `IACon`, and the hom-object is `TData K [a, b]` — with no
inference change and no new sort of arrow, exactly as "the manifest,
stated once" predicted.

## Amendment (2026-09-09): templates as shipped — four deviations

*The design above ("Templates, restated") shipped as written: a def
whose `use` names a THEORY is a template, a def whose `use` names an
INSTANCE expands it there and re-infers it there, and `@` is now
refused in source by the character rather than by the word. Recorded
here are only the four places the implementation departed from it, and
why.*

1. **Template expansion is its own phase, before renaming.** The plan
   said `elabUseWith` "inlines the template bodies it meets" under
   `use Inst` — interleaved with the existing walk. That loses a case:
   with a resource scope *between* the instance and the call
   (`use IntSum … use Log … total`), the inner scope routes the spine
   first and an inlined body would arrive after its own routing. So
   `use` now has FOUR ordered kinds — templates expand, instances
   rename, resources route, functors rewrite — and expansion walks the
   whole term carrying a stack of enclosing instances, innermost
   first. An expanded body is then elaborated by every scope it landed
   in, exactly as if it had been written there. Innermost-wins costs
   nothing: it is the head of the stack.

2. **The optional pre-check against the theory's signature was not
   taken, on a reason worth keeping.** The idea was a `Theory@slot`
   forward environment analogous to `declaredSlots`, so a broken
   template failed once rather than per instantiation. It cannot be
   general: a theory with a CONSTRUCTOR parameter (`theory Arrow(k)`)
   has no carrier before an instance, so `thenP : k(a,b) k(b,c) ⇒
   k(a,c)` has no arrow to forward-declare — `k` is substituted at the
   instance, which is the whole ML-functor move. A check that exists
   for parameter-free theories and silently does not for the
   interesting ones is worse than no check: it teaches a rule that is
   not true. Errors surface at each instantiation, which is where the
   expansion is, and expansions already render.

3. **Two refusals the plan did not name**, both consequences of
   expansion being inlining rather than linking: a template may not
   call itself (*template loopy calls itself: a template is expanded at
   the call, so it cannot recurse*), and a `use` header may name at
   most one theory (*a template waits for one instance*). Recursion
   inside a template is still ordinary — `foldExp` and friends are
   defs, and the template calls them.

4. **A template is over a theory, never over a resource — decided,
   with the alternative verified.** Stage 5a item 3 wanted a generic
   handler. It does not want a resource template: a resource scope is
   ROUTING, and its offsets come from the header's arity, so a body
   waiting for a resource waits for an arity rather than for a name.
   What a handler actually needs is two per-carrier words, and naming
   words is what a theory is for:

   ```braid
   theory Collector(e, a) =
       seed   : • ⇒ e
       unwrap : e ⇒ a

   def collected = use Collector ; (f -> [f (seed) ... ; ev ; unwrap ...])
   ```

   which comes out `Fn⟨ρ0 =Log> ρ1⟩ ⇒ Fn⟨ρ0 ⇒ Str ρ1⟩` under
   `use Logs` and `Fn⟨ρ0 =Counter> ρ1⟩ ⇒ Fn⟨ρ0 ⇒ Int ρ1⟩` under
   `use Counts` (verified; `examples/resources.braid`). So the recipe
   *resource + macro + theory* discharges generically with the pieces
   already on the table, and the theory is doing the same job it does
   everywhere: turning "the operation for this carrier" into a name.

**A REPL bug the templates found.** `:t` did not elaborate: it parsed
and inferred, so an ambient `use IntSum` did not resolve slot names for
it (`:t op` said *Unknown primitive: op* while `:t IntSum@op` worked),
and a template — whose entire existence is elaboration-time — could not
be inspected at all. `:t` now goes through the same door a program line
does. Note the ordering this forced: the bug had to be fixed *before*
`@` was sealed, since `Inst@slot` was until then the only way to read a
slot's type in a session.

**What stage 5c can rely on.** Two tables, both in `ElabCtx` beside
`ecFuncs` and both carried by `ModuleBase`/`Module` so `:import` and
the REPL keep them: `ecSlots :: SlotTable` is now instance ↦ (theory,
slot names) — it gained the theory, which is what makes a template
resolvable — and `ecTmpls :: TemplateTable` is name ↦ (theory,
unelaborated body). `mode K = Inst` wants a third of exactly this
shape (K ↦ its instance), and the K-word table 4b needs is the same
kind of syntactic, prefix-scoped record. `ecThs` (theory names) is
already threaded, which is what let `use` tell a theory from a
resource; a mode name will want the same.

## Amendment (2026-09-09): recursion at a typed boundary

*Stage 5a½, two commits: `a02e635` (no self-reference; recursion is
`fix`) and `a188dd0` (totality as a label). Written after both landed;
every type quoted below was read back from the checker, and every
refusal was reproduced.*

**The change.** A definition is no longer in scope in its own body.
`def f = … f …` is refused — *"`f` refers to itself: a definition is
not in scope in its own body — write the recursion with `fix` (MANUAL
§8)"* — and the older `recurse` spelling is gone, together with
`inferDefTermIn`'s monomorphic self-reference path and the self-knot
`extendRunDefs` used to add (a prefix scope is now exact at inference
and at run time alike). Recursion is a word with a type:

```text
fix : Fn⟨Fn⟨ρ0 =Rec> ρ1⟩ ρ0 ⇒ ρ1⟩ ⇒ Fn⟨ρ0 =Rec> ρ1⟩
```

written `[(self args -> …)] ... >> fix ... >> ev` — quote the body,
tie the knot, `ev` it. The knot arrives **deepest**, so the recursive
call is an ordinary quoted call (`… >> self ... >> ev`); tying it is
pure, and the `Rec` label sits on the arrow `fix` hands out and on the
`self` it hands in, never on `fix`'s own arrow. At run time the knot is
tied by the module's own lazy early-binding cycle, under a name the
parser cannot produce — the machinery that already knotted defs, kept
and made unreachable from source.

Structural recursion did **not** move to `fix`. `dataDeclArtifacts`
emits a structural recursor beside roll/unroll/merge, with the scheme
the old generated fold had, byte for byte; the prelude's `fold` derives
from `foldList`, so `map`, `filter`, `reverse`, `append` and `concat`
are recursor-only and unlabelled (`reverse : List(a0) ⇒ List(a0)` —
checked). `downFrom`, `take`, `skip`, `zip` and `partitionSum` are
`fix`-built and carry `Rec` (`zip : List(a0) List(a1) =Rec>
List(Box(a0 a1))`); codata — `from` and `repeat` in
`examples/stream.braid`, the circuits in `examples/circuits.braid` —
keeps its self-call under the quote, through `fix`, and stays
productive.

### The three payoffs, each with its current truth

**(1) Every def is a closed spine — delivered for inference, not yet
for `reflect`.** Every stage of a def now has a principal scheme
computable from the prefix scope alone, because there is no atom
without one: the `.recurse` atom that named the def being inferred is
gone, and nothing replaced it. For *inference* the fibration picture of
the 09-08 amendment holds with no exception, and `principal : Free(G) ⇢
Sch` is total on typeable code — a def is literally a morphism of the
free category over its vocabulary.

*(Superseded 2026-09-12 — see "the closed structure" below: the gate is
lifted and this demo now runs.)* For *functors* it was not yet true, and
the obstruction was stage 3⅞'s parked gate rather than anything
recursion added. `fix` hands the knot
in as a **binder parameter**, so a self-call inside a row component or
a quotation is a captured parameter — a true closure — and `reflect`
refuses those. Reproduced:

```text
def tr =
    use Traced
    [(self n -> … self ... >> ev …)] ...
    fix ...
    ev

error: in def tr: `use Traced`: Unknown primitive: self
```

`self` is a binder-bound name, and Code's vocabulary has no such
generator, so the reflection stops there. What lifting the gate needs
is named in row 2 of the functors-known-to-type table: abstraction
elimination is `P ⋉ –`, tensoring with the parameter block, and it does
not yet **distribute the parameter block over a sum or under a quote**.
Until it does, `P` cannot follow the self-call into the row arm where
the self-call lives. Pinned as a limit, not worked around.

The gate is narrower than "functors and recursion don't mix". A functor
over a *call* to an already-recursive word is fine — the functor sees
one atom, the def having been elaborated outside the scope — and the
labels union as they should. Verified:

```text
def fac2 = [(self n -> …)] ... >> fix ... >> ev
def tr = use Traced ; fac2 ; _ 1 ; +
tr : Int =IO Rec Traced> Int
```

**(2) Recursion is an operator with laws — statable now, not yet run.**
Two operators, and the literature names both. `fix` is the fixpoint
operator at the exponential: read `Fn⟨A ⇒ B⟩` as `B^A`, and the body
`Fn⟨Fn⟨A =Rec> B⟩ A ⇒ B⟩` is `B^A × A → B`, i.e. `B^A → B^A` after
currying, of which `fix` takes the fixpoint. The *parameterized* form `C(P × X, X) →
C(P, X)` is what actually runs — the parameters enter through the
quote's closure — but `P` is invisible in the type, which is worth
saying out loud: Braid's `fix` is a Conway/parameterized fixpoint whose
parameter object is the quote's environment. `loop` is Elgot iteration,
and its type is that signature and nothing else:

```text
loop : Fn⟨ρ0 ⇒ (ρ0 | ρ1)⟩ ρ0 =Rec> ρ1        C(X, X + Y) → C(X, Y)
```

The laws that become **statable**: fixpoint (unrolling), parameter
(naturality in the argument), dinaturality/rolling, and Bekič for two
knots; for `loop`, Elgot's fixpoint, uniformity and codiagonal. Bloom &
Ésik axiomatize the equational theory; Hasegawa (and Hyland
independently) identify a Conway fixpoint operator on a cartesian
closed category with a trace on it, which is why `fix` and `loop` are
the same operator wearing two types here; Simpson & Plotkin give the
completeness result for those axioms. All three are now in `READING.md`.

What is **true today**: the fixpoint law is an ordinary Braid program
and it runs, at sample points —

```text
def facBody = (self n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> self ... >> ev) >> *)) >> merge)
def fac    = [facBody] ... >> fix ... >> ev
def unroll = [fac] ... >> facBody
5 >> fac  →  120        5 >> unroll  →  120
6 >> fac  →  720        6 >> unroll  →  720
```

— and both sides type `Int =Rec> Int`, which is the law's statement in
the type as well as in the values. What is **not** true: nothing in the
repo runs these laws, and nothing decides them. `sameCode` refuses the
pair outright (*sameCode: outside the structural fragment: [facBody]*),
as it must: one unrolling is not a structural rewrite. Running them the
way `theory` law blocks run associativity — extensionally, at sample
points, audited — would need `fix` to be reachable as a theory slot,
which nobody has tried. And the payoff the plan wanted from this —
"does this functor preserve the trace?" as a *checkable* statement —
needs (1) first: a functor cannot yet see inside a `fix` body at all,
so it cannot yet be asked whether it transports the knot.

**(3) The precondition for interleaving inference and elaboration.**
With every def a closed spine, a left-to-right pass along one def can
carry schemes plus the left context and never consult a caller — which
is what would let a functor read the cut (width-aware tracers, rules
with type side-conditions, 5c's K-word table by type, routing by type,
errors at the cut). **Not in this stage, and nothing was built toward
it.** Recorded because the reason for the change should outlive the
change.

### Totality, and exactly what `Rec` says

`Rec` is a label like any other: minted by `fix` and `loop`, union
along composition, written wherever a type is written (`=Rec>`, `=IO
Rec>`, sorted on display), never annotated onto inferred code. It says
*may recurse without bound*. It is **provenance, not a proof** — the
same sentence the manifest amendment above makes about `IO` and about
functor receipts, said a fourth time.

The reading it buys is the one worth having: **fix-free pure code
terminates by construction**, so the `a ⇒ a` counterpoint's "free
theorems hold only up to termination and cost" closes on the
termination half for unlabelled words. Divergence used to inhabit every
type; it now inhabits every `=Rec>` type and — modulo the audit two
paragraphs down — no bare one. Verified:

```text
[(self ... -> self ... >> ev)] ... >> fix ... >> ev : ρ0 =Rec> ρ1
(x -> 1000 >> (n -> n) >> drop >> x)                      : a0 ⇒ a0
```

The cost half is untouched, and remains the standing argument for the
quantitative-grade arc; `fix` and `loop` being the only unbounded sites
is where that arc now starts.

**Modulo the prim audit.** "Fix-free ⟹ terminates" is *believed*, not
proved. Nobody has audited the whole primitive set for another
unbounded construct, and until someone does, the claim is a design
intent with strong evidence, not a theorem.

**What `Rec` does not do**, stated beside what it does:

- It **bounds nothing.** Grades are idempotent, so `Rec` ∪ `Rec` is
  `Rec`; a word that recurses once and a word that recurses forever
  have the same type. Counting is the cost arc.
- It **unions**, so it inherits the intersection gap `=Metered>` has:
  a `=Rec>` word is one *some* of whose stages may recurse, never one
  *all* of whose stages do. "Wholly in the image" is still the open
  dual question (the coeffect section above).
- **Elaboration-time recursion escapes it entirely.** `checkFunctorWord`
  rejects a functor word that is not `Code ⇒ Code`, and rejects one
  that is io — the io grade *is* the phase distinction — but it tests
  `eIO` alone and never looks at the rest of the label set. A
  `Rec`-labelled functor word is therefore accepted, runs while the
  module is being elaborated, and leaves **no `Rec` on what it
  elaborated**: the recursion happened in the other phase, and the type
  says nothing about it. Verified end to end, and the receipt is the
  tell:

  ```text
  def shrink = (c -> (c >> unparse >> drop) 0 c ... >> skip)   -- Code =Rec> Code
  functor Shrink = shrink
  def p = use Shrink ; dup ; * ; _ 1 ; +
  p : Int =Shrink> Int            -- no Rec anywhere: the recursion ran at elaboration
  ```

  What catches a *diverging* one is not `Rec` but the elaboration step
  budget, which was already there and still fires: *elaboration step
  budget exhausted: a functor did not terminate (or needs a larger
  budget)* (verified against a `fix`-built spinner). So the compiler
  does not hang — but fuel is a bound and not a proof, and that gap is
  unchanged by this stage. Template expansion is the same story from a
  third direction, bounded by a third mechanism: a template that calls
  itself is refused at the call (*template loopy calls itself*),
  because expansion is inlining rather than linking.
- A functor **cannot yet claim "I do not transport recursion"** and be
  checked. That claim was the R2 note's most interesting item and it is
  the one thing R2 did not deliver: it needs (1), for the reason given
  there.

### The functors-known-to-type table gains no row

Deliberate. `fix` is not a functor; it is a word, and a stage that
**calls** a `fix`-built word is an ordinary stage — it reflects as one
atom, and the marker tracer whiskers after it like any other cut
(`after fac2`, printed, in the run above). No row in the table needs
amending to say so. What changed is not the class of liftable functors
but the vocabulary they act on, and it changed by *subtraction*: the
one atom with no scheme is gone. `Rec` likewise adds no row; it is a
label, and the rows checked by subsumption read label sets already.

The `fix` **idiom** was the exception, and it was (1)'s gate rather than
a missing row: while the knot is a live binder parameter the spine is
not closed over the environment, so there was nothing for a functor to
act on yet. *(Lifted 2026-09-12: elimination reifies the capture, and
the idiom elaborates. The table still gains no row — what changed is
again the vocabulary, this time by ADDITION: the closed structure's two
maps.)*

### The honest cost

Two prices, both paid in written types, both the sandbox rule reaching
one level further than it used to.

**Eight declarations across two example files** had to gain `=Rec>`
*(amended 2026-09-12: six. Two of the eight were the unification bug,
not the label — see the end of this section)*:
`data Stream(a) = (a Fn⟨• =Rec> Stream(a)⟩)` and, in
`examples/circuits.braid`, `data Circuit(a, b) = Fn⟨a =Rec> b
Circuit(a, b)⟩`, `data Arr(a, b) = Fn⟨a =Rec> b⟩`, and all five slots
of `theory Arrow(k(_,_))`.

**The label reaches into codata bodies' written types**, which is the
part that surprised. `theory Arrow`'s `arrP` needed `=Rec>` on its
*nested argument* as well as its own arrow —
`arrP : Fn⟨a =Rec> b⟩ =Rec> k(a, b)` — because composition **unifies**
rows rather than joining them. A closed `=Rec>` codata field propagates
the label to the written type of every function its body applies. This
is not new machinery; it is the no-subeffecting rule (`design-effects.md`,
stage 1 as shipped) meeting a label that more code carries than `IO`
ever did. The labelled spelling is the permissive one — a `=Rec>` arrow
still accepts non-recursive code, since an inferred row is open and
absorbs — and the bare spelling is the promise. That asymmetry is the
whole design, and the eight declarations are what it costs.

> **Amended 2026-09-12 — two of the eight were a BUG, not a cost.**
> Composition joins now, so a `=Rec>` codata field no longer propagates
> its label into the written type of the functions its body applies.
> `data Arr(a, b) = Fn⟨a ⇒ b⟩` and
> `arrP : Fn⟨a ⇒ b⟩ =Rec> k(a, b)` are what
> `examples/circuits.braid` says today, and it prints the same five
> numbers. The other six stand and always did: `Circuit`'s and
> `Stream`'s thunks really recurse, and `arrP`'s own arrow plus
> `thenP`, `firstP`, `observe` and `sample` are `=Rec>` because the
> `Circuit` model builds every circuit with `fix`. The asymmetry
> (labelled = permissive, bare = promise) is unchanged; what changed is
> that only an arrow whose OWN code recurses has to say so.

One latent bug surfaced and was fixed on the way: `substParams` rebuilt
a nested `Fn` with `arrPure`, discarding the declared manifest — it had
been silently wiping `=IO>` too, wherever a parameterized declaration
substituted into one.

### Correction to "What a functor can silently change"

That section's `a ⇒ a` counterpoint cites `def dvg = recurse` as typing
`ρ0 ⇒ ρ1`. Both halves are now false: `recurse` does not exist, and
divergence is no longer bare. The current reading is
`[(self ... -> self ... >> ev)] ... >> fix ... >> ev : ρ0 =Rec>
ρ1`, and the conclusion drawn there — that `a ⇒ a` is inhabited by
divergence, so the receipt is not the mark — **no longer holds for
unlabelled words**, modulo the prim audit above. What survives of it is
the cost half, unchanged and still unaddressed: the identity-at-a-cost
still types `a0 ⇒ a0`.

## Amendment (2026-09-12): the closed structure

*Beside the recursion amendment, and the thing that finishes it. Stage
5a¾. Everything below was run in Docker on the shipping build.*

**What changed.** Abstraction elimination used to take the **cartesian**
generators as given and emit them: a parameter block parked deepest, a
use of a parameter a `dup` on the block swapped up into place, the block
dropped once at the end. That is `P ⋉ –`, table row 2, and it covered
everything except the one case where a parameter is *not* consumed where
it stands — a quotation or a row branch that mentions it. Those were
refused (*"parameter captured in a quotation (a closure) — not
reflectable yet"*), and since `fix` hands the knot in as a binder
parameter, that was **every recursive def**.

Elimination now uses the cartesian **closed** — and hence distributive —
structure. Two maps, one taken as given and one derived:

- **`ev`** is the exponential's **counit**. It is the prim formerly
  spelled `apply`, renamed in this stage so the adjunction's two maps
  carry matching names (one spelling, no alias: everything that named it
  is in this repo and moved in the same commit). Not derivable —
  nothing else consumes an `Fn`, and naming a value never runs it:
  `(x f -> [x >> f])` fails with *Cannot unify stacks: a0 vs •*.
- **`curry : Fn⟨a ρ0 ⇒ ρ1⟩ ⇒ Fn⟨a ⇒ Fn⟨ρ0 ⇒ ρ1⟩⟩`** is λ, and it is a
  **prelude def**, not a prim:
  `def curry = (f -> [(x -> [x ... >> f ... >> ev])])`. Its own body is
  the one binder-into-quote that elimination takes as a **generator**
  rather than eliminating. Every other capture is rewritten into it.

Everything else is derived, in the prelude, with the derivation visible:

- `capture = (x f -> (f >> curry) x >> ev) : a Fn⟨a ρ0 ⇒ ρ1⟩ ⇒
  Fn⟨ρ0 ⇒ ρ1⟩` — partial application.
- `dist2 : a (ρ0 | ρ1) ⇒ (a ρ0 | a ρ1 | σ0)`, whose body captures the
  wire into one handler per track and then `case2`s. **Distributivity is
  a theorem, not an axiom**: in a cartesian closed category `P × –` is a
  left adjoint (that *is* `curry`), left adjoints preserve coproducts,
  and that body is the proof written out. `undist2` needs no closed
  structure at all — it is the canonical map any category with
  coproducts has, `(s -> s >> (_ alt1 | _ alt2) >> merge)`.

**The algorithm.** Under a block `P` of `k` wires: a quotation mentioning
`m` of them copies the block, compiles the body against a copy laid
deepest *inside* the quote (yielding `Fn⟨P ρ0 ⇒ ρ1⟩`), and then binds
the copies off the stack with `capture`, once each. The order is forced
and was checked against the body: each `capture` binds the wire directly
below the `Fn`, which must be the `Fn`'s own **deepest** input — so the
block inside the quote is laid in the **reverse** of the block on the
stack, the shallowest stack copy binding first. A row mentioning `m`
parameters copies the block, `dist2`s it into every track once per
parameter (shallowest first, so the block lands in its own order at the
bottom of each track), compiles each branch against it, and lets each
branch drop its own copy — which is what `compileAbs` already does at
the end of any body. Both keep the atom's **original type**, so nothing
downstream changes. Nesting is the same recursion; `fix` needs nothing
special.

```text
(x -> [x ... >> +])
  dup pass >> _ (_ [dup pass >> _ + >> drop pass] >> capture) >> drop pass

(n -> n >> zero >> (n >> drop >> 1 | n n >> *) >> merge)
  dup pass >> _ zero >> dup pass
    >> _ (dist2 >> (dup pass >> _ drop >> _ 1 >> drop pass
                   | dup pass >> dup pass >> _ swap pass >> _ * >> drop pass))
    >> _ merge >> drop pass
```

**Deviation from the scoped plan, and why.** The plan said to keep the
block through each branch, `undistN` it back out, and drop it once.
Dropping inside each branch is one word shorter *and better typed*:
`undist2`'s output carries a residual row variable (`alt2` is open in its
tracks and nothing closes it), so undisting would widen the row's type
where dropping per branch leaves it exactly as written. `undistN` ships
anyway — it is half of the `Distributive` theory, and the laws need it.

**What is now true of initiality, stated exactly.** `reflect` is total
on binder code but for two corners, and both are honest:

- A **residual** row `(p | q | ---)` that mentions a parameter is still
  refused: the passing tracks would need the block too, and an open
  row's width is not a type Braid can write.
- A **flat row of three or more tracks** that mentions a parameter is
  refused: distributing over a coproduct is derived from `case2`/`merge`,
  and `merge : (ρ0 | ρ0) ⇒ ρ0` is **binary**. There is no N-ary
  codiagonal to derive `distN` at a flat width, which is why `case3`/
  `case4` nest their sums and why `dist3`/`dist4` follow them —
  `dist3 = dist2 >> (pass | dist2)`. Polymorphism does not reach a
  closed row's width, and neither does this. Every row in the prelude
  and in `examples/` is binary, so the corner is a corner.

*(Both corners closed the same day — see "Rows get a proper tail"
below. The reading above is kept because it is why `#dist:K` had to be
a generator rather than one more derivation.)*

`sameCode` **decides nothing new**. It normalizes the term it is handed
and never runs abstraction elimination, so two spellings of a capturing
binder are still *"outside the structural fragment: a binder"* — and "I
cannot tell" is not "they differ". `dist ; undist = id` and
`capture ; ev = substitution` are stated and *run* at sample points in
`examples/distributive.braid`; **deciding** them is 5b.

**Hygiene, and its one new edge.** Code still carries no captured
values: a captured parameter reifies as a wire at the push, not as a
name, so invariant four survives with no closure exception. But
elimination now writes two *prelude* names into code that never
mentioned them — `capture` and `dist2` — and a module that shadowed
either would capture reflected code. So they are the two prelude names a
module may not redefine, refused by name with the reason.

**The functor receipt now says what ran.** `checkFunctorWord` tests
`eIO` alone, so a `Rec`-labelled functor word runs at elaboration
(fuel-bounded) and its `Rec` used to escape: a `fix`-built functor's
expansion read `Int =RecId> Int`, saying nothing about the unbounded
walk that produced it. The receipt now carries the functor word's **own
labels** beside the functor's name — `Int =Rec RecId> Int` — which is
the honest half of the choice the recursion amendment left open. `IO`
cannot reach it: `checkFunctorWord` still refuses that, because the io
grade *is* the phase distinction.

**What falls out.** `use F` over the `fix` idiom works — `use Traced`
over a `fix`ed factorial traces every stage and prints `24`, the demo
that was refused with *Unknown primitive: self* when 5a½ shipped. The
level-1 library reflects (`lift`, `box`, `equalsTo`, `both`, `whileFn`,
`case2`). "This functor transports recursion" is now *statable* —
`F(fix b) = fix (F b)` — but it is not stated: that is a law in
`theory Functor`, and it is 5b.

## Amendment 2026-09-12 — rows get a proper tail (`---`, `into`, `#dist:K`, `altN`)

*Written after the products-versus-coproducts pass. Every asymmetry
between the two in Braid traces to one fact — **products are the ambient
structure, coproducts are an object** — and that fact is a choice, not
an accident: the stack IS the product, so product structure is spelled
by juxtaposition and needs no words, while a sum is one wire and every
map on it has to be a word. This stage removed the asymmetries that were
gaps rather than consequences of that choice. Labels stay out: rows are
POSITIONAL.*

### The table

| | product (the stack) | coproduct (a sum wire) |
|---|---|---|
| where it lives | the ambient structure; juxtaposition | one wire, `(Δ₁ \| … \| Δₙ [\| σ])` |
| the tail | `...` — a stack variable `ρ` | `---` — a row variable `σ` |
| introduction | writing wires side by side | `alt1`…`altN` (`here`/`ok`/`again` ≡ `alt1`) |
| functorial action | a tensor stage `f g` | a code row `(f \| g)` |
| act on some, pass the rest | `f ...` / `>>>` | `(f \| ---)` |
| closed eliminator | `drop`, `at`, `foldExp` | `merge`, `case2`…`case4`, `otherwise` |
| **open** eliminator | `pass` (identity on an unknown rest) | **`into`** (handle one, shift the rest) |
| diagonal / codiagonal | `dup : a ⇒ a a` | `merge : (ρ \| ρ) ⇒ ρ` |
| terminal / initial | `• `, `forget : ρ ⇒ •` | the empty row — unwritable, and nothing needs it |
| symmetry | `swap` | `(alt2 \| alt1) >> merge` (the track swap; the prelude's `not`) |
| distributivity | — | `dist2` derived, `#dist:K` a generator |
| decided or run | `sameCode` decides the wiring fragment | rows are outside it; laws run at sample points |

**The dual pairs, read off the table.** `dup`/`merge` (diagonal and
codiagonal). `forget`/the-initial-map (terminal and initial; Braid has
the first as a word and does not need the second, because an empty row
is never built). `swap`/track-swap. `f g`/`(f | g)` (the two functorial
actions). `f ...`/`(f | ---)` (act on some, pass the rest). `pass`/`into`
(the two OPEN eliminators — this is the pair the stage added, and it is
the one that makes the column read straight).

What is *not* dual, and shouldn't be: `curry`/`ev` have no coproduct
mirror, because the exponential is right adjoint to the product alone.
That asymmetry is real category theory, not a Braid gap.

### `into` is `[h, id]`, and why that is the only choice

```
into : Fn⟨ρ0 ⇒ (σ0)⟩ (ρ0 | σ0) ⇒ (σ0)
```

A copairing needs one handler per alternative. Over a residual, the
alternatives inside `σ0` have no names, so the only handler you can
supply for them is the identity — and `[h, id]` is therefore not one
copairing among many, it is the whole of what can be written. Its
runtime content is a **tag shift**: tag 0 runs `h` on its bundle (whose
answer is already a value of the remaining sum), and tag `k > 0` becomes
`k − 1` with the bundle untouched.

It is not derivable. The obvious attempt, `(h | ---)`, gives
`((σ0) | σ0)` — a sum of a sum beside itself — and collapsing that
*positionally* is exactly the shift `into` performs; there is no word
that does it, and `merge` cannot, since the two sides have different
types. `splice : (ρ0 | (σ0)) ⇒ (ρ0 | σ0)` flattens the *other* nesting.

**`>=>` is not an instance of `into`.** `t1 >=> t2` desugars to
`t1 >> (t2 | alt2) >> merge` — the copairing `[q, alt2]`, with a
**written** second handler over a **closed** two-track row. `into`'s
second component is forced to be the identity. A closed two-track
copairing `[h, id]` is just `(h | pass) >> merge` and needs no prim
either; `into` earns its keep exactly when what remains is a residual,
or more than one track.

`into` and `otherwise` are the pair worth naming together. `otherwise =
(s a -> s >> (pass | a ... >> ev) >> merge)` is `[id, a]` then un-sum —
the ladder **closer**. `into` is `[h, id]` — the ladder **step**. The
idiom is one of each:

```braid
s
[h1 ; alt1] ... ; into
[h2 ; alt1] ... ; into
_ [d] ; otherwise
```

### Why `#dist:K` is a generator while `dist2` is derived

`dist2 : a (ρ0 | ρ1) ⇒ (a ρ0 | a ρ1 | σ0)` is a **theorem**: in a
cartesian closed category `P × –` is a left adjoint (that is `curry`),
left adjoints preserve coproducts, and the prelude body is that proof
written out — capture the wire into one handler per track, then `case2`.
The derivation goes through `merge`, and `merge` is **binary**. So the
derivation reaches exactly the closed two-track case, and `dist3 =
dist2 >> (pass | dist2)` reaches the NESTED ones, and nothing derives a
flat width or a residual.

```
#dist:K : a (ρ1 | … | ρK | σ) ⇒ (a ρ1 | … | a ρK | σ)
```

Two reasons this cannot be a definition. (1) **Width.** `K` is the arity
of a *written* row, and polymorphism does not reach it — the same wall
`caseN`, `distN` and the generated `#fold:` recursors all stand at, so
`#dist:K` is a synthesized family exactly like `#fold:`, one member per
width, its name unspellable (`#` opens a comment) so nothing can shadow
it. (2) **The residual.** `σ` is not distributed into *at all*; it
passes, block-free. That is not a shortcut, it is the only possibility:
to push `a` into a track you must write a handler for that track, and
the tracks in `σ` have no names. A word that "prepends `P` to every
track of an unknown row" is not a type Braid can write.

With it, abstraction elimination covers every row — closed binary
(emitting the derived `dist2`, because reflected code should show the
theorem), wider, and residual — and **`reflect` is total on binder
code**, full stop. The two corners above are closed.

### The alternative that is parked: extensive rows

The other way to type `P ⋉ σ` is as a **type former** — a row with a
pending prefix, distributed lazily. It is principal for a fixed-width
prefix and fails for a stack-variable one:

```
ρ ⋉ σ  ~  Int ⋉ τ
```

has `ρ := •, σ := Int ⋉ τ` and `ρ := Int, σ := τ`, and the two are
**incomparable** — neither is an instance of the other, so there is no
principal solution and the unifier would have to guess. That is the
whole argument; extensivity waits for a use that forces it.

### The copower, also parked

`n·C` — the `n`-fold coproduct of one object, a row *segment* rather
than a row — is the exact dual of `Cⁿ`, which Braid already has as
exponents (§13, `design-exponents.md`). Its **one-track** form is
writable today: `Fin(n) C` is a tag beside a payload, which is what a
copower collapses to when every alternative has the same shape. The row
form (`n` alternatives, each `C`, with `merge` at width `n`) needs
`mergeN` and the same width machinery exponents needed. Parked beside
stage 7, where the exponent/copower symmetry is the natural place to
finish it.

### `in1..inN` → `alt1..altN`

One spelling, **no alias** (2026-09-12, Daniel: "alt is good"). The
reasons are small and both real: `[h >> in1] into` read badly, and `in`
is the prefix `into` now lives beside. ~360 mechanical sites moved in
one commit — prelude, examples, tests, manual, design notes, the value
printer, and `injIndex`'s pattern; `here ≡ alt1` stays, as do
`ok`/`miss`/`again`/`done`. The Haskell identifiers (`injIndex`,
`injScheme`) keep their names: they are about injections, which is what
the family still is.

The word for a sum's tracks, in prose, is **alternative**.

## Amendment 2026-09-12 — the prim-reduction pass (50 → 46)

*Immediately after the row stage, because `fix`, `curry`/`ev` and `into`
had just made more of the kernel derivable and the design bet — "a tiny
prim set spans everything else in the language itself" — is only worth
anything if it is re-tested when the generators change.*

**The criterion.** A word keeps its place in `primEnv` only if it is a
**structure map** of the doctrine, or if it **touches the
implementation**:

| kept because it is structure | kept because it touches the implementation |
|---|---|
| cartesian: `_` `dup` `swap` `drop` `pass` `forget` | data: `+` `-` `*` `div` `mod` `cat` `toStr` `symStr` `asInt?` `eq?` `lt?` `true` `false` |
| coproduct: `alt1…altN` (via `injIndex`), `there`, `merge` | io: `print` `readLine` `readFile` `writeFile` |
| exponential: `ev` | reflection: `parse` `unparse` `reflect` `evalAs` `sameCode` `interpose` |
| recursion: `fix` | type-level: `weaken` `finInt` |
| open coproduct: `into` | |
| exponent tier over `Aⁿ`: `at` `foldExp` `foldExp2` `mapN` `mapN2` `zipN` `unzipN` `dupN` `indicesN` `checkedAt` | |

**What moved, each verified live at the scheme it had as a prim:**

- **`id` → `def id = _`.** `_` is the identity — the positional
  spelling, a wire this stage does not touch — and `id` is the word for
  the same morphism. Two prims for one map was the only outright
  duplicate in the table.
- **`gt?`, `gte?`, `lte?` → the prelude**, from the one primitive order:
  ```braid
  def gt?  = swap >> lt? >> (swap | swap)
  def gte? = lt? >> not >> (pass | pass)
  def lte? = gt? >> not >> (pass | pass)
  ```
  The trailing `(pass | pass)` is load-bearing. `not` is the track swap
  and is built from injections, which are **open** (`not :
  (ρ0 | ρ1) ⇒ (ρ1 | ρ0 | σ0)`), so without a closed 2-row the derived
  words would carry a residual the prims did not. There is no closed
  injection to avoid this with: openness is what makes a producer
  commit only to a prefix, and it is not negotiable.
- **`loop` → `def loop = (f ... -> [(self ... -> f ... >> ev >>
  (self ... >> ev | pass) >> merge)] ... >> fix ... >> ev)`** — the
  Elgot dagger, `f† = ∇ ∘ (f† + id) ∘ f`, over the knot 5a½ shipped.
  Note that this needs **no `into`**: the row is closed and two-track,
  so `[f†, id]` is just `(f† | pass) >> merge`. `into` is for the OPEN
  case, which is exactly the distinction the Elgot law beside it draws.

  **Two costs, both real.** (1) `Rec` is now *inherited* rather than
  declared, and composition unifies grades, so `loop`'s body type reads
  `Fn⟨ρ0 =Rec> (ρ0 | ρ1)⟩` where the prim said `⇒`. An inferred quote's
  grade row is open and absorbs the label, so every existing use still
  types; a **written** pure `Fn⟨Σ ⇒ (Σ|Θ)⟩` handed to `loop` is now
  refused. That is arguably the honest reading — the body does run
  inside an unbounded knot — but it is a loss of precision, recorded
  here rather than hidden.
  *(**Retracted 2026-09-12.** Cost (1) was not a cost and not honest:
  it was the grade system unifying where it should join. `loop` is
  `Fn⟨ρ0 ⇒ (ρ0 | ρ1)⟩ ρ0 =Rec> ρ1` again — the prim's type — and a
  written pure body runs through it. The body does not recurse; the
  KNOT does, and the knot is `loop`'s own arrow. See design-effects.md,
  "composition JOINS". Cost (2) stands.)*
  (2) A knot per loop instead of a builtin
  iteration: 100 000 iterations take 3.2 s against 1.9 s, with no
  growth in memory (the re-entry goes through `goAtoms`, which is where
  the fuel counter already lives).

**What was examined and kept, with the reason:**

- **`there : (σ0) ⇒ (ρ0 | σ0)` is not `alt2`.** `alt2 : Δ ⇒ (Δ1 | Δ | σ)`
  *injects a stack* at position 2; `there` *shifts an existing sum's
  tags*. `altN ≡ here >> there^(n−1)` — `there` is the successor of the
  unary numeral the flat family abbreviates, and every attempt to derive
  it goes through `splice`, which is defined *using* it. (`here` was
  never a prim: it lives in `injIndex` beside `ok`/`again`.)
- **`forget : ρ0 ⇒ •`** is the terminal morphism over a segment of
  *unknown width*. `drop` is its width-1 shadow; going the other way
  needs a fold over an erased width, which is the thing `forget` is.
- **`checkedAt`** tests an `Int` against the live segment's **actual**
  width. Widths are erased, so no Braid word can read one — the check is
  the implementation showing through, which is exactly the second
  criterion.
- **`dupN` / `zipN` / `unzipN` / `indicesN`** are the structure maps of
  the exponent object: `Aⁿ ⊗ Bⁿ ≅ (A⊗B)ⁿ` (`zipN`/`unzipN`), the
  diagonal at width n (`dupN`), and `Aⁿ ≅ (Fin n ⇒ A)` made concrete
  (`indicesN`). None is reachable from `mapN`/`foldExp`: `mapN` is
  one-wire-in-one-wire-out by construction, so it cannot double an
  element, and `foldExp` collapses to a scalar. They all need `n`, and
  `n` is erased.
- **`true` / `false` stay.** The stated objection — "a prelude `alt1`
  at `•` has an open residual and nothing closes it" — is *refutable*:
  `verdict = (forget | forget)` is a closed 2-row and closes it, and
  `def true = 1 >> drop >> alt1 >> verdict` type-checks at `• ⇒ Bool`
  and runs correctly (verified). The real obstruction is different and
  worse: nothing in Braid sources from `•` except a literal, so that
  "derivation" launders an `Int` into a unit. A prim that is honestly a
  point beats a def that lies about where it came from.

Count: **50 → 46**, with `into` added in the same session (51 at its
peak). The prelude gained five words, each with its `##` doc and its
derivation in the text.

## Honest gaps

- **Error provenance** remains the biggest gap in the language, and
  functors sharpen it: a type error in an expansion points at code the
  user didn't write. `unparse` in the message is the mitigation;
  source locations are the fix.
- **Double error reporting** is possible for binder bodies (inferred
  once during abstraction elimination, again after splicing).
- **Elaboration can diverge**; fuel is a bound, not a proof.
- The **stage-6 flagships lean on the row arc** (`=Shadow>` and
  friends assume rows); scope them down or sequence them after.
- **`eq?` on Code is syntactic**; two α-equivalent spellings of one
  rewrite differ until `sameCodeC` lands.
- The **image-tagging question above is open**, and the coeffect
  decision with it.
