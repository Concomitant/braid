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
and model renaming, the generated data folds. Every one is a
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
  model-parameterized defs `f(C)` are called *templates* in all
  docs, never functors; one MANUAL sentence disambiguates for Haskell
  readers (`Functor`/`fmap` ≠ this).
- **No `macro` keyword.** A functor's word is any def whose type
  unifies with `Code ⇒ Code` at pure grade. Existing combinators
  (`weave`, `transposeC`) qualify with no ceremony.
- **No new Term node.** `Use` already carries names; the elaborator's
  partition grows a third kind (models / resources / functors).
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
5. local rewrites `p ↦ q` with `scheme(q) ≥ scheme(p)` — the `model
   … : Base`
   declaration, **shipped 2026-09-13** (see the amendment below). **Unification blesses a call; subsumption
   blesses a rule.** A `replace : Fn⟨a ⇒ b⟩ Fn⟨a ⇒ b⟩ Code ⇒ Code`
   types, and the shared variables say only that p and q have a
   common model — symmetric, where "q may stand wherever p stands"
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
"marker tracer" (`examples/traced.braid`) is the worked model of
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
syntactic equality, and `sameCodeC` (**shipped 2026-09-13**) gives
semantic equality on the free-cartesian wiring fragment, where the word
problem is decidable. Law kinds:

1. **Functoriality** — free (unviolatable by construction) at level
   2a; audited only for raw whole-spine functors.
2. **Identity preservation.**
3. **Interaction laws** between a pair of functors — `s ; F ; G` vs
   `s ; G ; F` on witness programs: the graded-distributive-law
   question landed as a runnable law a model must pass.
4. **Idempotence** — `F(F(p)) = F(p)`: true of optimizers,
   normalizers, canonicalizers.
5. **Image membership** — for *idempotent* F only, "p is in the image
   of F" ⟺ `F(p) = p`: an assertion about a particular program (it
   lives beside the def), whose meaningfulness depends on law 4, so a
   theory offering it must declare idempotence. Verified 2026-08-31
   that the fixed-point test does NOT characterize interposing
   functors (weaving twice interposes twice) — their image can be
   remembered, not detected. See the open question below.

All five are shipped and worked in `examples/optimizer.braid`
(2026-09-13): 1–4 as three theories (`Functor`, `Optimizer`,
`Commuting`) whose models are audited at module start, 5 as program
assertions beside the programs. What `sameCodeC` decides, and what had
to fall back to syntactic `eq?`, is recorded in the 2026-09-13
amendment below.

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
`type`, `resource`, `theory`, `model` and `functor` all cross a file
boundary with nothing added to the checker. The alternative considered
and rejected was chaining checked modules as bases (the way the prelude
is threaded in): it works for defs, but a theory declared in one file
and instantiated in another would then need base theory/model tables
threaded through `checkModuleWith`, own-vs-inherited handling in the
model path, and a merge for every field of `Module`. Textual
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
  namespacing is model renaming at file scope, never a second
  implementation. Deliberately not in v1.
- *Importing through a functor* (`import "rules.braid" use Traced`) is
  a functor applied to a whole presentation, which is file-scope `use`.

One thing did have to be added, and it was for the REPL, not for
files: `ModuleBase`, carrying the model and functor tables a session
has accumulated. A file needs none of it (its imports are textually
present), but a session has no text to include into, so `:import` is
the only way a session gets a theory, a model or a functor — it
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
divergence now types `ρ0 =Recursive> ρ1`, so a bare `a ⇒ a` is no longer
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
for trusted models:

```
mode Circuit = CircuitPipe        -- a mode IS a model of theory
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
| mode `K` | `;` ↦ `thenP`, atoms ↦ `arrP`, from a model of `Arrow(k)` | the hom-object `K(a, b)` | the category the model presents, embedded as its hom-objects |

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
THEORY is a template — its body waits for a model; a def whose
`use` names an INSTANCE instantiates every template it calls, the body
expanded there, renamed by that model, re-inferred (no rank-1
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
  the operations; Braid's models are already models, so discharge
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
for: a name is a wire, `...` is a stack. The model head names a
**declared data type**, not a type expression, and `slotArrowAt`
substitutes the NAME into the slot's arrow before any slot is
forward-declared. So this is the ML-functor move and not higher kinds:
`Ty` gains nothing, `TyParam` gains `PCon String Int`, and inference
never meets a constructor variable. `k(a, b)` is recorded as
`TData "k" [a, b]` inside the slot signature only, and the rename runs
before the wire/stack substitution so it cannot reach into a type the
model supplied.

**Two consequences worth naming.**
- *Strength is what forced it.* `firstP : k(a, b) ⇒ k(Pair(a, c),
  Pair(b, c))` mentions `k` at three different pairs of wires. A `PWire`
  parameter can only name ONE hom-object, which is why the old theory
  was a monoid — a category with one object — rather than a category.
- *`Fn` cannot fill a constructor parameter.* It is built in and takes
  an arrow rather than wires. The refusal says so and names the one-line
  wrapper (`data Arr(a, b) = Fn⟨a ⇒ b⟩`), which is how
  `circuits.braid` gets its second, deliberately boring model.

**What stage 5c can rely on.** A model of `Arrow(k)` is nothing but
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
   with a resource scope *between* the model and the call
   (`use IntSum … use Log … total`), the inner scope routes the spine
   first and an inlined body would arrive after its own routing. So
   `use` now has FOUR ordered kinds — templates expand, models
   rename, resources route, functors rewrite — and expansion walks the
   whole term carrying a stack of enclosing models, innermost
   first. An expanded body is then elaborated by every scope it landed
   in, exactly as if it had been written there. Innermost-wins costs
   nothing: it is the head of the stack.

2. **The optional pre-check against the theory's signature was not
   taken, on a reason worth keeping.** The idea was a `Theory@slot`
   forward environment analogous to `declaredSlots`, so a broken
   template failed once rather than per instantiation. It cannot be
   general: a theory with a CONSTRUCTOR parameter (`theory Arrow(k)`)
   has no carrier before a model, so `thenP : k(a,b) k(b,c) ⇒
   k(a,c)` has no arrow to forward-declare — `k` is substituted at the
   model, which is the whole ML-functor move. A check that exists
   for parameter-free theories and silently does not for the
   interesting ones is worse than no check: it teaches a rule that is
   not true. Errors surface at each instantiation, which is where the
   expansion is, and expansions already render.

3. **Two refusals the plan did not name**, both consequences of
   expansion being inlining rather than linking: a template may not
   call itself (*template loopy calls itself: a template is expanded at
   the call, so it cannot recurse*), and a `use` header may name at
   most one theory (*a template waits for one model*). Recursion
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

   def collected = over Collector ; (f -> [f (seed) ... ; ev ; unwrap ...])
   ```

   *(spelled `use Collector` until 2026-09-13; the template header is
   `over` now — see "`use` applies, `over` declares" below, and the
   receipts on the types below are that amendment too.)*

   which comes out `Fn⟨ρ0 =Log> ρ1⟩ =Logs> Fn⟨ρ0 ⇒ Str ρ1⟩` under
   `use Logs` and `Fn⟨ρ0 =Counter> ρ1⟩ =Counts> Fn⟨ρ0 ⇒ Int ρ1⟩` under
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
the REPL keep them: `ecSlots :: SlotTable` is now model ↦ (theory,
slot names) — it gained the theory, which is what makes a template
resolvable — and `ecTmpls :: TemplateTable` is name ↦ (theory,
unelaborated body). `mode K = Inst` wants a third of exactly this
shape (K ↦ its model), and the K-word table 4b needs is the same
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
fix : Fn⟨Fn⟨ρ0 =Recursive> ρ1⟩ ρ0 ⇒ ρ1⟩ ⇒ Fn⟨ρ0 =Recursive> ρ1⟩
```

written `[(self args -> …)] ... >> fix ... >> ev` — quote the body,
tie the knot, `ev` it. The knot arrives **deepest**, so the recursive
call is an ordinary quoted call (`… >> self ... >> ev`); tying it is
pure, and the `Recursive` label sits on the arrow `fix` hands out and on the
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
`fix`-built and carry `Recursive` (`zip : List(a0) List(a1) =Recursive>
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
tr : Int =IO Recursive Traced> Int
```

**(2) Recursion is an operator with laws — statable now, not yet run.**
Two operators, and the literature names both. `fix` is the fixpoint
operator at the exponential: read `Fn⟨A ⇒ B⟩` as `B^A`, and the body
`Fn⟨Fn⟨A =Recursive> B⟩ A ⇒ B⟩` is `B^A × A → B`, i.e. `B^A → B^A` after
currying, of which `fix` takes the fixpoint. The *parameterized* form `C(P × X, X) →
C(P, X)` is what actually runs — the parameters enter through the
quote's closure — but `P` is invisible in the type, which is worth
saying out loud: Braid's `fix` is a Conway/parameterized fixpoint whose
parameter object is the quote's environment. `loop` is Elgot iteration,
and its type is that signature and nothing else:

```text
loop : Fn⟨ρ0 ⇒ (ρ0 | ρ1)⟩ ρ0 =Recursive> ρ1        C(X, X + Y) → C(X, Y)
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

— and both sides type `Int =Recursive> Int`, which is the law's statement in
the type as well as in the values. What is **not** true: nothing in the
repo runs these laws, and nothing decides them. `sameCode` refuses the
pair outright (*sameCode: outside the structural fragment: [facBody]*),
as it must: one unrolling is not a structural rewrite. *(2026-09-13:
the refusal survives the new normalizer — its wording changed, the
answer did not — and it now has a name. A fixpoint equation is an axiom
of an iteration theory, not an equation of the free bicartesian closed
category the normalizer works in; `[loop] [loop] ; sameCode` says*
outside the structural fragment: `loop` has no closed arity. *See "the
normal form for sums".)* Running them the
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

### Totality, and exactly what `Recursive` says

`Recursive` is a label like any other: minted by `fix` and `loop`, union
along composition, written wherever a type is written (`=Recursive>`, `=IO
Recursive>`, sorted on display), never annotated onto inferred code. It says
*may recurse without bound*. It is **provenance, not a proof** — the
same sentence the manifest amendment above makes about `IO` and about
functor receipts, said a fourth time.

The reading it buys is the one worth having: **fix-free pure code
terminates by construction**, so the `a ⇒ a` counterpoint's "free
theorems hold only up to termination and cost" closes on the
termination half for unlabelled words. Divergence used to inhabit every
type; it now inhabits every `=Recursive>` type and — modulo the audit two
paragraphs down — no bare one. Verified:

```text
[(self ... -> self ... >> ev)] ... >> fix ... >> ev : ρ0 =Recursive> ρ1
(x -> 1000 >> (n -> n) >> drop >> x)                      : a0 ⇒ a0
```

The cost half is untouched, and remains the standing argument for the
quantitative-grade arc; `fix` and `loop` being the only unbounded sites
is where that arc now starts.

**Modulo the prim audit.** "Fix-free ⟹ terminates" is *believed*, not
proved. Nobody has audited the whole primitive set for another
unbounded construct, and until someone does, the claim is a design
intent with strong evidence, not a theorem.

**What `Recursive` does not do**, stated beside what it does:

- It **bounds nothing.** Grades are idempotent, so `Recursive` ∪ `Recursive` is
  `Recursive`; a word that recurses once and a word that recurses forever
  have the same type. Counting is the cost arc.
- It **unions**, so it inherits the intersection gap `=Metered>` has:
  a `=Recursive>` word is one *some* of whose stages may recurse, never one
  *all* of whose stages do. "Wholly in the image" is still the open
  dual question (the coeffect section above).
- **Elaboration-time recursion escapes it entirely.** `checkFunctorWord`
  rejects a functor word that is not `Code ⇒ Code`, and rejects one
  that is io — the io grade *is* the phase distinction — but it tests
  `eIO` alone and never looks at the rest of the label set. A
  `Recursive`-labelled functor word is therefore accepted, runs while the
  module is being elaborated, and leaves **no `Recursive` on what it
  elaborated**: the recursion happened in the other phase, and the type
  says nothing about it. Verified end to end, and the receipt is the
  tell:

  ```text
  def shrink = (c -> (c >> unparse >> drop) 0 c ... >> skip)   -- Code =Recursive> Code
  functor Shrink = shrink
  def p = use Shrink ; dup ; * ; _ 1 ; +
  p : Int =Shrink> Int            -- no Recursive anywhere: the recursion ran at elaboration
  ```

  What catches a *diverging* one is not `Recursive` but the elaboration step
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
one atom with no scheme is gone. `Recursive` likewise adds no row; it is a
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

**Eight declarations across two example files** had to gain `=Recursive>`
*(amended 2026-09-12: six. Two of the eight were the unification bug,
not the label — see the end of this section)*:
`data Stream(a) = (a Fn⟨• =Recursive> Stream(a)⟩)` and, in
`examples/circuits.braid`, `data Circuit(a, b) = Fn⟨a =Recursive> b
Circuit(a, b)⟩`, `data Arr(a, b) = Fn⟨a =Recursive> b⟩`, and all five slots
of `theory Arrow(k(_,_))`.

**The label reaches into codata bodies' written types**, which is the
part that surprised. `theory Arrow`'s `arrP` needed `=Recursive>` on its
*nested argument* as well as its own arrow —
`arrP : Fn⟨a =Recursive> b⟩ =Recursive> k(a, b)` — because composition **unifies**
rows rather than joining them. A closed `=Recursive>` codata field propagates
the label to the written type of every function its body applies. This
is not new machinery; it is the no-subeffecting rule (`design-effects.md`,
stage 1 as shipped) meeting a label that more code carries than `IO`
ever did. The labelled spelling is the permissive one — a `=Recursive>` arrow
still accepts non-recursive code, since an inferred row is open and
absorbs — and the bare spelling is the promise. That asymmetry is the
whole design, and the eight declarations are what it costs.

> **Amended 2026-09-12 — two of the eight were a BUG, not a cost.**
> Composition joins now, so a `=Recursive>` codata field no longer propagates
> its label into the written type of the functions its body applies.
> `data Arr(a, b) = Fn⟨a ⇒ b⟩` and
> `arrP : Fn⟨a ⇒ b⟩ =Recursive> k(a, b)` are what
> `examples/circuits.braid` says today, and it prints the same five
> numbers. The other six stand and always did: `Circuit`'s and
> `Stream`'s thunks really recurse, and `arrP`'s own arrow plus
> `thenP`, `firstP`, `observe` and `sample` are `=Recursive>` because the
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
`[(self ... -> self ... >> ev)] ... >> fix ... >> ev : ρ0 =Recursive>
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
*(SUPERSEDED 2026-09-13: 5b part 2 routed `sameCode` through
`elimAbsTerm` and taught the normalizer quotations and rows. All three
of those sentences are now false, which was the point of the stage —
see "the normal form for sums".)*

**Hygiene, and its one new edge.** Code still carries no captured
values: a captured parameter reifies as a wire at the push, not as a
name, so invariant four survives with no closure exception. But
elimination now writes two *prelude* names into code that never
mentioned them — `capture` and `dist2` — and a module that shadowed
either would capture reflected code. So they are the two prelude names a
module may not redefine, refused by name with the reason.

**The functor receipt now says what ran.** `checkFunctorWord` tests
`eIO` alone, so a `Recursive`-labelled functor word runs at elaboration
(fuel-bounded) and its `Recursive` used to escape: a `fix`-built functor's
expansion read `Int =RecId> Int`, saying nothing about the unbounded
walk that produced it. The receipt now carries the functor word's **own
labels** beside the functor's name — `Int =Recursive RecId> Int` — which is
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
| decided or run | `sameCode` decides the wiring fragment | **decided too** (2026-09-13): a known injection is followed, an unknown one is split — see "the normal form for sums" |

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

**`>=>` is not a model of `into`.** `t1 >=> t2` desugars to
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
**incomparable** — neither is a model of the other, so there is no
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

  **Two costs, both real.** (1) `Recursive` is now *inherited* rather than
  declared, and composition unifies grades, so `loop`'s body type reads
  `Fn⟨ρ0 =Recursive> (ρ0 | ρ1)⟩` where the prim said `⇒`. An inferred quote's
  grade row is open and absorbs the label, so every existing use still
  types; a **written** pure `Fn⟨Σ ⇒ (Σ|Θ)⟩` handed to `loop` is now
  refused. That is arguably the honest reading — the body does run
  inside an unbounded knot — but it is a loss of precision, recorded
  here rather than hidden.
  *(**Retracted 2026-09-12.** Cost (1) was not a cost and not honest:
  it was the grade system unifying where it should join. `loop` is
  `Fn⟨ρ0 ⇒ (ρ0 | ρ1)⟩ ρ0 =Recursive> ρ1` again — the prim's type — and a
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

## Amendment (2026-09-12): the construct, named

*After the grade fix (composition joins, `5fc3677`) the arrow can be
stated in one sentence, and the record should carry it.*

**An arrow `Σ =L> Θ` is a morphism of grade `L` in a closed Freyd
category, graded by a join-semilattice with subeffecting, freely
generated by the vocabulary and presented concatenatively.** The parts:

1. *Freyd* (Power–Robinson): pure code `C` is cartesian and is the
   CENTRE of the premonoidal `K`; `J : C → K` is the inclusion; a
   stage runs left to right by decree.
2. *Graded, with the order* (Gifford–Lucassen / Katsumata): a grade
   function `K → B(P(Labels))` — composition unions — plus the
   filtration by wide subcategories `K≤L ⊆ K≤M` for `L ⊆ M`, with
   `K≤∅ = J(C)`. The order is subeffecting; a written type names a
   level; `subsumes` checks `code ≤ written`. Commutative and
   idempotent as a SOLVER decision (subset constraints have least
   solutions); cost (`× ℕ`) and sequential grades (Tate's productors)
   would arrive as product components, never by making provenance
   non-idempotent — "went through F" is a set-level fact.
3. *Carriers*: carrier-less labels are marked copies; carriered labels
   (resources; the World) are Power–Robinson state constructions
   `K(E ⊗ A, E ⊗ B)` with whiskering as the inclusion, glued by a
   Grothendieck construction over the semilattice (stage 7 makes this
   inference; today it is display); modes (5c) are internal categories
   in `C` with hom-objects `K(a,b)`, entered by a functor from the free
   category, receipted as an ordinary label.
4. *Closed* (Power–Thielecke): `Fn⟨Σ =L> Θ⟩` is the Freyd exponential,
   graded — `curry` pure, `ev` graded by what it evaluates.
5. *Distributive coproducts*: rows, `merge`, `into = [h, id_τ]`,
   distributivity a theorem except over an open family (`#dist:K`).
6. *A graded Conway fixpoint*: `fix : K≤ε(Fn⟨A ⇒ B⟩ ⊗ A, B) →
   K≤ε∪{Recursive}(A, B)`; `loop` its Elgot dagger, derived; `Recursive` the one
   grade-raising operator without a carrier.
7. *Free and concatenative*: functors out are determined on
   generators; `reflect` is total on binder code (one `pass`-placement
   corner aside).
8. *Types*: HM principal types over the presentation, subset
   constraints on grades (Talpin–Jouvelot), least-fixpoint solver,
   written types by subsumption with skolemized tails.

What order the type does NOT carry, and why (Daniel's question,
2026-09-12): execution order (`;` is the order; the decree fixes it),
functor application order (not compositional — declare the composite
and the receipt names it), and effect order (a sequential grade, a
separate product component when a label earns it). Two programs of
the same grade with different behaviour are two programs of the same
type, as `1 >> +` and `2 >> +` are.

Believed, not proved: totality of fix-free code; principal typing as
the cartesian lift of `reflect`; the fixpoint and iteration laws
(runnable at points, not decided).

## Amendment (2026-09-13): rules, laws, and the 2-cell

*Stage 5b, part 1. What shipped: the `rules` declaration, the
`rewrite` engine, `sameCodeC`, three law theories and
`examples/optimizer.braid`. **Amended 2026-09-13 (stage 5c½):** the
declaration is spelled `model Opt : Base = p = q, …` — a partial
model of the ambient presentation — and the keyword `rules` is gone.
Everything below is unchanged in substance; "rule set" reads "model
of `Base`" and "rule" reads "binding". See "`use` applies, `over`
declares" at the end of this file.*

**A rule set is a functor with a natural transformation attached.**
Take a rule set `R = {p₁ ⇒ q₁, …, pₙ ⇒ qₙ}`. Its action on code is a
functor out of the free category `Free(G)` on the generators `G`
(prims plus defined words): defined on generators — `pᵢ ↦ qᵢ`,
everything else to itself — and extended by congruence, which is
exactly what `rewrite` does as it descends through quotations, rows and
groups. Being *by generators* is what makes functoriality free: a
generator's image depends on that generator alone, so `R(p ; q) =
R(p) ; R(q)` holds by construction and `R(id) = id` trivially. The law
is still written and still runs (`theory Functor` in
`examples/optimizer.braid`), because "cannot fail by construction" is a
claim about the construction and a law is how a claim gets checked.

**The 2-cell is what the type check buys.** Let `principal : Free(G) →
Types` send a program to its principal scheme, and order `Types` by
subsumption (the model preorder: `σ ≤ τ` iff `τ ≥ σ`, "τ is at least
as general"). The rule check is exactly the requirement that

> `principal ∘ R ⇒ principal`

is a **lax natural transformation** into that preorder — a 2-cell,
whose component at a program `p` is the statement "the rewritten
program's scheme is at least as general as the original's". Because the
base is FREE, this is checkable on generators alone: the squares for
composites paste from the squares for generators, so `n` checks at
declaration cover every program the rewrite will ever meet. That is the
whole content of `rules`, and it is why the check is finite,
once, and complete rather than per-use and approximate.

Equivalently, in Melliès–Zeilberger's language, `principal` is a
**refinement system** (a functor into a category of types, fibred over
programs) and the rule check makes `R` a **morphism of refinement
systems** — it lifts along `principal`. That is the same statement with
the 2-category flattened, and it is the reading that explains the
asymmetry below.

**Direction matters, and it is not symmetric.** The 2-cell points one
way: generalize, never narrow. This is precisely why the naive typing
fails. A word

```
replace : Fn⟨a ⇒ b⟩ Fn⟨a ⇒ b⟩ Code ⇒ Code
```

types, and its shared `a`, `b` say only that `p` and `q` have a
*common model* — **unification**, which is symmetric. "q may stand
wherever p stands" is **subsumption**, which is not. With `two : a ⇒
Int Int`, `dupInt : Int ⇒ Int Int`, `dup : a ⇒ a a`, all three of
`dupInt ↦ dup`, `dup ↦ dupInt` and `two ↦ dup` pass unification, and
only the first is sound. Hence the slogan, which is the entire reason
`rules` is a keyword and not a type:

> **Unification blesses a call; subsumption blesses a rule.**

Grades come along at no cost, because `subsumes` compares them by ⊆ and
the grade semilattice has `∅` at the bottom: a pure `q` under an io `p`
passes (the rewrite *removes* an effect and the 2-cell still points the
right way), and an io `q` under a pure `p` is refused. That is
subeffecting in the type-and-effect sense (Talpin–Jouvelot), not
absorption — it became free when composition started joining
(5a⁹⁄₁₀).

**The railway operators are unaffected.** `>=>`, `>>=` and friends are
ordinary words: they are *in* `G`, not *over* it, so a rule set either
rewrites them by name or leaves them alone. Nothing about the 2-cell
touches how the sum monad composes, and no rule can change the shape of
a railway without being a rule *about* `>=>`, which would be checked
like any other.

**Receipts make the 2-cell auditable.** `use Opt` mints `Opt` on the
manifest of everything it rewrote, so the type of a word records which
rewrites were applied to build it, and an unlabelled written type
refuses optimized code (*Cannot unify effects: Opt vs pure*). This is
the difference between an optimizer you can audit and one you must
trust, and it is the reason the plan chose `use Rules` over a
`rewrite : List(Rule) Code ⇒ Code` word: a word leaves no evidence.
The engine still exists as that word (`rewrite`, over two symbol
lists), unchecked, the way `interposeRaw` is the unchecked half of
`interpose` — and `lift2`'s fallback is what keeps *that* honest.

**What `sameCodeC` decides, and what it does not.** `sameCodeC : Code
Code ⇒ Bool` is `sameCode` over `Code` values. It had to exist, because
a functor returns `Code` and a law about a functor is a claim about
`Code`; and it works on structure rather than text because `#dist:K`
and `#fold:…` do not round-trip through `unparse` (`#` lexes as a
comment). It decides strictly *more* than `sameCode`, for a reason we
did not anticipate: `Code` is post-abstraction-elimination, so the
binder `sameCode` refuses outright is already gone —
`([(x -> x x)] ; getCode) ([dup] ; getCode) ; sameCodeC` is `true`
where `[(x -> x x)] [dup] ; sameCode` is an error. It still stops at a
**quotation** and a **row**, which is the next stage's work.
*(SUPERSEDED the same day by part 2: `sameCode` runs elimination too,
so the gap closed and the two are one procedure; quotations and rows
are inside the fragment. The list below shrank to its last two items —
see "the normal form for sums".)* Laws that
had to be stated syntactically, with `eq?`, and labelled as such:

- **transport of recursion**, `F(fix b) = fix (F b)` — `fix` takes a
  quotation, so the comparison is spine-to-spine at a sample point;
  *(2026-09-13: decided when the body does not call itself, since `fix`
  has a closed arity and its argument's body is now compared in normal
  form; still syntactic when it does, because `self ... ; ev` is `ev`
  of a WIRE)*;
- any **image assertion about a higher-order program** — same reason;
- anything needing `+` to be commutative or `Int` arithmetic to be
  arithmetic, which is the older and permanent boundary of the free
  category (`2 _ ; *` and `dup ; +`).

**Natural transformations, the three readings** (recorded 2026-09-08,
now partly cashed). (1) *Model homomorphisms* — `transformation Len :
ListMonoid -> IntSum = len`, one generated law per slot, naturality
finite because the base is free. Designed, not shipped: the generator
is easy, the **verdict** is not (slots are recursive defs the
normalizer sees as opaque, and a generated law has no sample supply).
The sentence to keep: *naturality over a free category is finite — the
generators suffice.* (2) *Harmlessness of instrumentation*
(Dantas–Walker; the handler direction of Plotkin–Pretnar): for a
functor `F` with discharge `ε : F(Σ) ⇒ Σ`, naturality `F(p) ; ε = ε ; p`
says stripping the instrumentation changes no value. It holds for
`Metered` with `ε = drop the fuel`; `install : Σ ⇒ Fuel Σ` is **not**
natural, and that failed square IS the meter — the receipt on the arrow
is the obstruction to naturality of `install`. (3) *Parametricity* —
already the strongest guarantee available: a `∀a. List(a) ⇒ List(a)`
word is natural in `a` by its type (Wadler), checked by nothing because
it needs no check.

**The limit, written down: naturality lives in a FIBRE.** `traced(p) ;
ε = ε ; p` holds on values and fails on the log; an io `∀ρ. ρ ⇒ ρ`
stage is not central, so it is not a transformation `Id ⇒ Id` even
though its type says so — a pure one is, and is the identity.
Transformations are stated between functors into the *same* fibre;
crossing fibres needs a handler first (a grade-decrementing model
transformation). Non-local functors get no generator check — they are
not by generators — and stay sampled.

## Amendment (2026-09-13): the normal form for sums

*Written before the code, revised after it ran. The question this
stage had to answer is not "can the normalizer be made to enter a
row" — it can — but "what is the normal form it lands in, and what
does landing there prove". The answer below is a case tree over a
free distributive category, and the honest boundary is stated at the
end, because the fragment that has a normal form is smaller than the
language and saying so is the whole value of the word `decided`.*

### The fragment

A Braid program is in the **structural fragment** when every atom it
executes is one of:

- **cartesian wiring** — `id`/`_`, `dup`, `drop`, `swap`, `pass`,
  composition `>>`, juxtaposition (a tensor stage);
- a **literal** (`1`, `"x"`, `.sym`), read as a nullary constant, with
  distinct literals distinct constants;
- an **uninterpreted word** with a closed arity — any prim or def whose
  scheme fixes how many wires it eats and returns, including a def that
  is recursive (opaque by necessity) or that abstraction elimination
  refuses;
- a **quotation** `[p]`, together with `capture` and `ev`;
- the **coproduct's structure maps**: `alt1`…`altN`, a code row
  `(p₁ | … | pₙ [| ---])`, `merge`, `into`, `dist2`/`#dist:K`;
- any **def in the fragment**, which is inlined (so the normalizer sees
  through your own words) after abstraction elimination is run on its
  body. `undist2`, `case2`…`case4`, `otherwise`, `dist3`/`dist4`,
  `condFn`, `cond`, `when`, `unless` and the rest of the prelude's
  coproduct layer normalize by inlining; `dist2` and `capture` are
  interpreted directly because their own bodies would loop back through
  the words they define (`case2` eliminates to `dist2`, `capture` to
  `curry`).

That is the free **bicartesian closed** structure — products, the
exponential, coproducts, and the distributivity that follows from the
first two — over a signature of uninterpreted words. It is the setting
of Cockett's *Introduction to distributive categories* (READING): the
distributive law is coherent, `dist` is an isomorphism onto its image,
and a morphism of the free distributive category has a canonical form.
Carboni–Lack–Walters is the neighbouring statement — extensivity is what
makes the case split below a *partition* rather than a guess — and
Lafont's *Towards an algebraic theory of Boolean circuits* (also in
READING) is the presentation-with-canonical-forms style the symbolic
evaluator imitates: run the generators on distinct symbolic inputs and
read the result off.

### The normal form: a case tree over symbolic tuples

A symbolic value is

```
v ::= xᵢ                       an input wire
    | w(v₁ … v_k)ⱼ             the j-th output of an uninterpreted word
    | inⱼ(v₁ … v_m)            a KNOWN injection: tag plus bundle
    | ⟨v₁ … v_c ; p⟩           a quotation: captured arguments, then a body
```

The normal form of a program is a **case tree**: internal nodes are
labelled by a symbolic value of sum type whose injection is *not*
known, each node has one child per track of that sum, and each leaf
carries the pair (number of input wires consumed, tuple of symbolic
values returned). This is the sum-of-products shape the task asked
for: rows are pushed outward, `dist` pushes wires through them, and a
branch that is reached under a known injection is never built at all.

Two programs are the **same morphism** when their case trees agree:
the same splits, and equal tuples at every leaf. Equality of leaves is
structural, except on quotations, where `⟨c⃗ ; p⟩ = ⟨d⃗ ; q⟩` iff the
captures are equal and `p` and `q` are the same morphism — decided by
the same procedure, one level down. That is the only place the
definition is recursive, and it terminates because a quotation's body
is a strictly smaller term.

**Three rewrites do all the work**, and each is an equation of the free
bicartesian closed category, so the procedure is sound by construction:

1. **β for the coproduct.** `altK >> (p₁ | … | pₙ)` is `p_K` re-tagged
   at `K`; `altK >> merge` is the bundle; `altK >> dist2` pushes the
   wire into the bundle; `alt1 >> [h] into` is `h`, and `altK >> [h]
   into` for `K > 1` is `alt(K−1)`. No branching: an injection that is
   known is simply followed.
2. **β for the exponential.** `[p] >> ev = p`, and `x [p] >> capture`
   is the quotation `⟨x ; p⟩` — so `capture ; ev` IS substitution, by
   running the body on the captured arguments followed by the segment.
   This is the operational semantics, used as a rewrite.
3. **The case split.** When an eliminator (`merge`, a row, `into`,
   `dist2`) meets a sum whose injection is *not* known, the tree
   branches: one child per track, with the scrutinee **refined** to
   `inᵢ(b₁ … b_w)` for fresh bundle wires, and the refinement applied
   to *both* programs. Splitting a coproduct into its tracks is exactly
   extensivity, hence sound; applying the refinement to both sides is
   what lets a program that branches be compared with one that does
   not — which is how `dist2 >> undist2 = id` gets decided at an
   arbitrary sum, where one side has a case tree and the other is the
   identity.

The two programs are therefore normalized **jointly**, under a shared
refinement, rather than separately and then compared. A split requested
by either side is taken by both. That is the one departure from
"normalize, then compare", and it is what makes the trees line up.

**Where a split's width comes from.** A track's width is a *type*
question, so the normalizer asks the typechecker. An input wire's type
comes from the program's own inferred arrow; `w(…)ⱼ`'s comes from `w`'s
declared scheme; and a wire typed by a *declared* `data` name is read
through that declaration's `unName` scheme, because `unName` is the
identity at runtime and the normalizer has already inlined it away. A
row all of whose tracks are closed stacks gives the widths; a row whose
tail is a **row variable** gives none, and the normalizer refuses rather
than guesses.

Two consequences worth writing down, because both were found by running
the thing:

- **Both sides are seeded alike.** The two programs are re-inferred
  *independently* — the unification the call site did is long gone — so
  one can come out with a closed input stack and the other open
  (`alt1` alone is `ρ0 ⇒ (ρ0 | σ0)`; `toStr ; alt1` is `Str ⇒ (Str |
  σ0)`). Seeding each at its own width would then compare them at
  different arities and report `differ` for two equal programs. So both
  are seeded with the SAME number of wires, the larger of the two,
  which is whiskering by an identity and preserves equality in both
  directions.
- **A residual is compared semantically, not as a flag.** The `Bool` on
  `Alts` decides what the normalizer *does* with a tag past the written
  tracks (pass it), not what it *reports*. Over a closed two-track sum
  `(f | ---)` and `(f | pass)` are therefore one morphism, and
  `sameCode` says `same`; `(f | ---)` against `(f | g)` with `g ≠ id` is
  `differ`. That is the right answer, and it is a stronger claim than
  comparing the flag would be.

### Soundness

Every step is a directed use of an equation that holds in the free
bicartesian closed category over the signature: wiring is the cartesian
structure (`dup` natural, `drop` the counit, `swap` the symmetry),
inlining a def is unfolding a definition, β for `+` and for `⇒` are the
two triangle identities, and a case split is extensivity. Nothing in
the procedure uses a property of any *particular* word: `+` and `*` are
opaque, so the verdict `same` means *equal under every interpretation of
the words* — a theorem — while `differ` means only *not equal in the
free category*, which is not a counterexample at any concrete type.
That asymmetry is unchanged from 2026-09-12 and is the first thing
§12.9 says.

### Termination

Three measures, one per source of recursion.

1. **Inlining** terminates on the `seen` list: a def already being
   expanded is recursive and becomes an uninterpreted word, so the
   unfolded term is finite.
2. **The case tree** terminates because along any path each split
   consumes one *dynamic* elimination site, and a single run executes
   finitely many atoms (bounded by a per-run tick budget); depth is
   therefore bounded, and width is the number of tracks, which is
   finite because a split is refused unless the row is closed. A hard
   depth cap (16) and tick budget turn "finite" into "fast", and
   exceeding either is reported as *outside the structural fragment*,
   never as a verdict.
3. **Quotation comparison** terminates on the structural measure: the
   bodies compared are proper subterms of the terms that carried them.

### The honest boundary — what stays outside

- **Words with semantics.** `+`, `*`, `cat`, `lt?` are uninterpreted.
  `dup >> +` and `2 _ >> *` are still `differ`. Deciding those means
  normalizing modulo an equational theory (AC, ACU, a ring), not a free
  one, and that is a different procedure.
- **`fix`, and therefore `loop`.** `fix` has a closed arity, so
  `[b] >> fix` normalizes and *two `fix` bodies are compared in normal
  form* — that much is new. But `fix`'s defining property is a fixpoint
  equation, not an equation of the free category, so the **Elgot
  identity** `loop f = f >> [loop f] into` is **not** decided: it is an
  axiom of an iteration theory, and a normalizer for a free bicartesian
  closed category has no business proving it. It stays runnable at
  sample points in `examples/into.braid`, labelled.
- **`ev` of a wire.** `ev` is interpreted only on a *literal*
  quotation — one the normalizer built with `[…]` or `capture`. `ev` of
  a quotation that arrived as an input wire (`self ... >> ev` inside a
  `fix` body; a handler slot) is outside, because its segment width is
  an open stack variable and there is no arity to give it. This is the
  single reason `examples/optimizer.braid`'s transport-of-recursion law
  is still syntactic.
- **Residual rows under an unknown injection.** `(f | ---)` applied to
  a sum we cannot see into: the unnamed tracks have no widths, so there
  is no partition to split on.
- **`curry` standing alone** — which surfaces as the same message,
  since `curry`'s body ends in `ev` of its parameter — and any word
  whose input stack is an open variable when it is not the final atom
  of its stage. `there` is *not* outside: on an injection it knows it
  shifts the tag, and on one it does not it stays an uninterpreted
  word, which decides less but never wrongly.
- **A binder abstraction elimination refuses** — the two corners 5a¾
  pinned (a residual row, or a flat 3+-track row, mentioning a
  parameter). `sameCode` now runs `elimAbsTerm` first, so ordinary
  binders are decided; these two are reported with elimination's own
  message.

### What this changes elsewhere

`sameCode` and `sameCodeC` are now **one procedure**: `sameCode` runs
abstraction elimination before normalizing, which is the path `reflect`
already took, so the two words agree on every program. The line in the
products/coproducts table above is updated accordingly.

## Amendment (2026-09-13): modes, shipped

*SUPERSEDED the same day by "models transport by shape" below: the
`mode` keyword is gone and the slot NAMES `arrP`/`thenP` are no longer
read. Everything else here — the carrier, the display fold, exits and
entries, the word table — stands. Read `mode K = Inst` as `use Inst`
and `use K` as `use Inst` throughout.*

*Stage 5c. `mode K = Inst`, the K-word table, the exit rule, the
display fold, sealed modes. What follows is the record of where the
implementation departed from items 4b and 4c, and of the one question
those items left open.*

*(Amended 2026-09-13, stage 5c½: `rules Opt = …` below reads `model
Opt : Base = …`, and the K-word table gained a second, written entry —
`over K`. See the last amendment in this file.)*

**What shipped, in one paragraph.** `mode Circ = Circuits` is a
declaration line beside `functor` and `model`. It requires `Circuits`
to model a theory with a two-argument constructor parameter, reads the
carrier off the model head, and reads two slots off the theory by
NAME: `arrP : Fn⟨a ⇒ b⟩ ⇒ k(a, b)` and `thenP : k(a, b) k(b, c) ⇒
k(a, c)`. Every other slot is classified off its DECLARED arrow — a
carrier in and none out is an EXIT, none in and one out is an ENTRY.
`use Circ` renames the model's slots into scope (so the mode is
spelled with them), then rewrites the spine: a stage that is a K-word
or an entry slot is left alone, every other stage `s` becomes `[s] ;
arrP`, and the pieces are joined with `thenP`. A receipt `Circ` is
minted by the ordinary path. The display folds `• ⇒ K(a, b)` carrying
`K` to `a =K> b`, wanting exactly one carrier. `mode K` also declares
a word `K : Code ⇒ Code` and a functor entry of that name, so the
namespace is shared with `functor`/`model` and `[K]`/`lift2 [K]`
work.
No field on `Arrow`; no change to inference.

**Deviations from 4b.**

1. **`use K` does not go through `runFunctor`.** 4b said the mode's
   functor is applied "exactly as any functor scope does". It cannot
   be, and the reason is worth recording: the rule needs the K-word
   table, which is elaborator state, and a `Code ⇒ Code` word is a
   Braid value that cannot see it. So the scope's rewrite is a Haskell
   pass (`runMode`) beside `elabScope`'s routing — the same kind of
   thing routing already was — and the WORD `K` is generated
   separately for value use. The two agree on a K-word-free body up to
   one identity carrier: the word seeds with `[_] ; arrP` so that its
   per-stage action can be uniform (`stagewise`), where the scope
   emits the tight form. `leftId` is the law that says the seed is
   free, and a test pins both spellings' emitted code.
2. **Entry slots join the K-word table.** 4b's table was "defs
   declared under `use K`". That is not enough to write anything: the
   theory's own generators (`sample : • ⇒ k(Int, Int)`) are carriers
   too, and `arrP` cannot embed them. They are admitted on the
   strength of their DECLARED arrow, which is a written type, so
   invariant five is intact — this is a signature steering
   elaboration, which is the Lean move the amendment of 2026-08-31
   already blessed, not inference steering it.
3. **A module def that merely produces a carrier is NOT a K-word**,
   and this is the sharpest ergonomic edge in the stage. `def sum0 = 0
   ; sumFrom` has type `• ⇒ Circuit(Int, Int)` and is still `arrP`'d
   inside `use Circ`, because admitting it would mean reading an
   INFERRED type to decide a rewrite. The fix available to the user is
   to declare it as a theory slot (written type) or to write it under
   `use K`. Recorded here rather than softened. **CLOSED 2026-09-13
   (5c½):** `def sum0 = over Circ ; 0 ; sumFrom` is the written
   declaration — checked against the def's arrow, added to the K-word
   table, and still `• =Recursive> Circuit(Int, Int)` at the base, because
   `over` mints nothing. The edge was real and the answer was a
   keyword, not a change to inference.
4. **One mode per header.** `use K1 K2` is refused; the second would
   `arrP` the first's carriers. Nesting or a declared composite is the
   spelling.
5. **The receipt is now transparent to the normalizer.** `use@F` is
   `pass` with a label, and `sameCode` refused any program carrying
   one — *`use@F` has no closed arity* — so no law could be stated
   about code written under ANY `use` scope. The normalizer now erases
   a receipt exactly as it erases `pass`. This was found while trying
   to state the mode's category axioms and is a fix for functors and
   rule sets too.
6. **A string literal is not a slot name.** The elaborator's `@` guard
   was testing every `Prim`, and a Str literal rides as a `Prim` whose
   name starts with a quote — so `"a@b"` was refused as "the
   compiler's spelling of a slot". Fixed; the generated mode word
   needs it, and it was a latent bug for everyone else.

**Deviations from 4c.** None on the rule itself: exits are read off
declared arrows and refused by name inside the scope, and the K-word
table is exact because of it. Two clarifications the implementation
forced:

- The refusal is by SLOT name, and a slot is only a name inside a
  `use`. The model's underlying def (`probe`, for `observe`) is an
  ordinary word and stays callable anywhere. A mode seals its own
  vocabulary, not the module's — which is the same honesty the sealed
  corollary needs.
- **Sealed modes work and are one example** (`examples/circuits.braid`,
  `theory Vault`): with no exit declared, every stage becomes `arrP`
  and the only word touching the accumulated carrier is `thenP`, which
  returns one, so nothing written in the mode leaves it. The limit to
  state plainly: the CARRIER's generated unroller is an ordinary base
  word and Braid has no export lists, so a mode seals the category and
  not the type.

**The flagship question, answered: a K-word inside ANOTHER mode's
scope does NOT type, and should not.** 4c asked for this first. A word
of mode `K2` is `• ⇒ K2(a, b)`; inside `use K` it is a stage, and
`arrP` embeds `Fn⟨a ⇒ b⟩` — a program with one wire in and one out,
not a carrier-out-of-nothing. Inference says `Cannot unify stacks: •
vs a16`, so the elaborator says it instead, naming both modes. And the
refusal is right: the two modes present two different categories, and
a functor between them is a piece of data neither declaration carries.
The way to cross is to leave `K2` first — its exit — and re-enter,
which is exactly "entering is a marker, leaving is a model" applied
twice. A transport `K2 → K` would be the `transformation` declaration, still
unbuilt for the reason recorded above.

**The category axioms are NOT decided, and the reason is structural.**
Both of `circuits.braid`'s models were tried against `sameCode` (left
identity, right identity, associativity, `arr` functoriality, and the
`first`/`fst` square). All five are refused for both, with *outside
the structural fragment: `ev` of a value that is not a literal
quotation*. An Arrow's composition must APPLY a program that arrived
as a wire — `compC` through `fix`, `Funcs` through `unArr ; ev` — and
an `Fn` whose input stack is an open variable has no arity to give it.
This is not a gap peculiar to modes: it is the `transformation` verdict
again, equality modulo a model's defining equations, which is
structural induction over an initial algebra and not normalization in
a free category. The five laws stay finite tests of an infinite
object, run through `observe` at sample points, which is what a
theory asking for an `observe` slot was always admitting.

## Amendment (2026-09-13): `use` applies, `over` declares — and the base is a theory

*Shipped as stage 5c½. The vocabulary had drifted: `use` meant five
different things, one of which was not application at all, and `rules`
was a keyword for something the language already had a word for. Both
are one idea, stated once.*

**The one rule `use` obeys.** *What follows is written in the DOMAIN of
X, and X is applied to it.* That is the whole of it, and every kind of
name obeys it:

| `use X` | the block is written in | X sends it | direction |
|---|---|---|---|
| a model of theory T | T's vocabulary | to the model's words | **into** the base |
| a model of `Base` | the base | to the images it names | base to base |
| a resource E | the base | to `E ⊗ –` | **out of** the base |
| a functor F | the base | through F's `Code ⇒ Code` word | **out of** the base |
| a mode K | the base | to `K`, `;` ↦ `thenP` | **out of** the base |

Instances point into the base; modes, resources and functors point out
of it. That is the table, and it is complete.

The one row that broke the rule was `use Theory` for a template: it
applied *nothing*, it bound a domain. So it is a different word.

**`over X` declares membership.** "This def is a morphism of X." It
applies nothing, opens no scope, writes no wires, and **mints nothing**.
Two readings, and they are the same reading:

- `over T` for a theory T — the def is a **template**, a morphism of
  the theory, waiting for a model to interpret it.
- `over K` for a mode K — the def is a **hand-built word of K**, a
  morphism of the category the mode presents, entered without
  transport. The elaborator checks the claim against the def's arrow
  (`• ⇒ K(a, b)`, the shape the mode pass pads and hands to `thenP`)
  and adds it to the K-word table.

The second reading closes pragmatics item (A), the K-word wall: before
it, a morphism of the category that is not the transport of any base
program — a stateful circuit, the whole reason Arrows exist — was
stranded, because the only alternative was to read an *inferred* type to
decide what a word is, which is invariant five's sharpest edge. `over`
is the written declaration, and invariant five's carve-out is exactly
that: the directing type is written.

**`over` mints nothing, and that matters.** A receipt is PROVENANCE —
"this code went through F". A hand-built morphism did not go through
anything; it may be a morphism no base program denotes. Labelling it
`K` would claim membership in the functor's **image**, which is
strictly stronger than membership in the category, and the two are
exactly the gap the manifest is careful not to close (see "coeffects,
and tagging the non-idempotent image"). So `sum0 : • =Recursive>
Circuit(Int, Int)` prints unfolded, the composite `use Circ ; sum0 ;
dbl` prints `Int =Circ Recursive> Int`, and "only a `use` mints, and every
`use` mints" holds exactly. Membership in K is carried by the carrier
in the type and by the K-word table; nothing else needs to carry it.

**Every `use` mints — models included.** Until now `use Duals ; poly`
left no receipt, which was the one exception to the rule above. It
mints now: `onDuals : Dual =Duals> Dual` says *which model interpreted
this template*, which is provenance in exactly the sense a functor's
receipt is. The consequence is that a theory slot declared without the
label refuses a body written under another model — the same sharp
edge functors have always had, now uniform. The one exemption is an
model's own slot and law bodies: the `use I` that resolves their
slot names is resolution, not application, and a model does not apply
itself.

**`rules` is a partial model of the base.** `Base` is the reserved
theory whose generators are *every word in scope*, each with its own
scheme as the slot's declared type. `model Opt : Base = dupInt =
dup` is a partial model of it: the generators it names get images, and
every generator it does not name maps to itself. The check is
`checkInstance`'s subsumption, unchanged; `use Opt` is the renaming
`use Inst` already performed, unchanged; the receipt is the receipt
every scope leaves, unchanged. One keyword fewer, and nothing new.

Keep the distinction that is *semantic* rather than syntactic: an
model of `Base` whose images are provably equal to the generators
(`sameCode`) is an **optimizer**; one whose images merely satisfy the
laws is a **reinterpretation**, a dialect. Both are models of
`Base`, and the language does not need to tell them apart — the laws
do.

**The base, stated.** Everything above assumes a thing that had never
been written down: *the base is a theory*. `Base` is presented by its
prims and their axioms. Then:

- the **runtime** is `model Runtime : Base` — the canonical model,
  the one that actually computes;
- the **prelude**, and every program, is a **template over `Base`** —
  written in the base's vocabulary, waiting for a model, and almost
  always getting `Runtime`;
- **plain Braid is the identity mode** — `;` is `;`, `arrP` is the
  identity, the carrier is the object itself;
- an **optimizer** is another model of `Base`, agreeing with
  `Runtime` on meaning and disagreeing on cost;
- a **mode** is a model of `Arrow(k)` — a category presented by
  hom-objects, with `use K` the functor into it;
- **resources** are modes with carrier `Fn⟨E a ⇒ E b⟩` — the
  Power–Robinson state construction read as a hom-object. This one is
  conceptual until stage 7: routing is a separate pass today, and the
  claim here is that it need not be.

So the four kinds of label in the manifest table are four *models*,
and `use` is one verb. What differs is the carrier column, which is
where it was already said.

**A naming note, since it will come up.** A model IS a functor in
the textbook sense — a functor out of the theory's classifying
category, given by its action on generators. The keyword `functor`
names the *non-tabular* case: a program on syntax, a `Code ⇒ Code`
word, checked by re-inference at the splice rather than once at a
declaration. That is the escape hatch, not the front door, and the
docs now order themselves that way: theory, template, model,
receipts, and `Code` last, under "instrumentation and retrofit".

## Amendment (2026-09-13): models transport by shape

*Stage 5c½, agent B. `instance` became `model`, the `mode` keyword
dissolved, and the elaborator stopped reading slot NAMES.*

**One vocabulary.** `theory`, `model`, `over`, `use`, `resource`,
`functor`. `model` is spelled `model` — the categorical-logic word
for a functor out of a presentation, and "a failing model is not a
model" is the audit in four words. `mode` is gone entirely: it named a
model and a carrier, and both were already there.

**Transport is a property, not a declaration.** A model whose theory
has a hom-object `k(_, _)` presents a category, and `use M` transports
into it. Nothing says so; the theory's DECLARED slot arrows do. Three
shapes, with `k` the constructor parameter:

| shape | it is | it licenses |
|---|---|---|
| `k(a, b) k(b, c) ⇒ k(a, c)` | composition | `over M ; f g ; <compose>` |
| `Fn⟨a ⇒ b⟩ ⇒ k(a, b)` | embedding | `use M` on one-wire stages |
| `k(a, b) ⇒ k(P(a, c), P(b, c))` | strength, naming the pairing `P` | `use M` on any stage |

plus exits (carrier in, none out) and entries (`•` in, one carrier out)
as 5c already read them. Two slots at one shape are refused naming
both. Identity is `embed [pass]` and needs no slot.

**Why this is not a convention we invented.** It is the base's own
structure — a Freyd category; Hughes' `arr`/`>>>`/`first`; Atkey — made
*declarable*. A functor is a map to a target that has the structure the
source has, and the three shapes are that structure written down. The
theory in `circuits.braid` may still be called `Arrow` and its slots
`arrP`/`thenP`/`firstP`; the elaborator never looks.

**Invariant five holds.** A slot's arrow is WRITTEN. Reading it to
decide how to elaborate is a signature steering elaboration — Lean's
bidirectional move — not an inferred type steering it. The routing
below reads each stage's ARITY from its scheme in the prefix scope,
which is the same kind of read: a number off a written signature, not a
dispatch.

**The routing discipline, and where the strength enters.** A hom-object
names one wire on each side, so a transported spine is one carrier wire
whose object is the base stack packed with `P`. A stage of `k` wires in
and `j` out becomes `embed [unP^(k−1) ; stage ; P^(j−1)]`, whiskered by
the strength once per wire riding above it — resource routing's `_`
padding with `first` in place of `_`, the mirror image because the
padded wires ride ABOVE the acted-on ones here and BELOW them there.
`...` is exactly what the strength becomes. A one-wire stage emits what
5c emitted, byte for byte.

**Decided against: a stack-shaped embedding.** `Fn⟨... ⇒ ...⟩ ⇒
k(..., ...)` would make the packing unnecessary — and `TData` holds
STACKS, so it is representable today. It is out because every other
part of the language treats a hom-object's arguments as wires (the
display fold `a =M> b`, the `over` shape check, the strength's own
type), and because the pairing is Hughes' own answer. It is the obvious
next thing to try if a flagship wants a category over whole stacks, and
it would make `first` unnecessary rather than necessary — the two
designs are alternatives, not layers.

**`over M` says "written in M's vocabulary"; the SHAPE says what the
def is.** A def whose arrow is `• ⇒ K(a, b)` is a morphism of M and
joins the word table; one that is not is a base word that speaks M's
language (an observation, a runner, a composite that exits). This is a
softening of 5c's rule and worth the record: 5c refused to read an
inferred type to decide membership, and that is still true of every def
with NO header. What changed is that `over M` — a written header, one
name, the author asking the question — makes the arrow the answer. The
alternative was a third keyword for "M's words in scope, no claim", and
one spelling per thing said no.

**What this costs.** `use Circuits` used to be a plain renaming and is
now a transport, so every hand-written block over a carrier model moved
to `over`. That is the migration in `circuits.braid`, `lifting.braid`
and the imports fixture, and it reads better: `over` is where hand
work lives, `use` is where transport does.

## Amendment (2026-09-13): the Doctrine, declared

*Stage 5d, part one. The shape rule of the previous amendment lasted
half a day. It was right about the structure and wrong about who says
so.*

**What was wrong with detection.** "Models transport by shape" read
three arrow shapes off every slot of every theory and concluded, from
their presence, that the theory presented a category. That answers
*does this theory happen to look like a category*. The question is
*does it claim to be one* — and the language already has the word for
a claim, which is the word this project spent a whole stage
sharpening. Detection also had two smells that would not go away: the
"two slots at one shape" refusal (an ambiguity that only exists
because nothing was named), and the arrow LAWS, which had to be
rewritten in every theory that wanted them, because there was nothing
to inherit them from.

**The doctrine is a theory, in the prelude.**

```braid
theory Doctrine(k(_, _), p(_, _)) =
    compose : k(a, b) k(b, c) ⇒ k(a, c)
    embed   : Fn⟨a ⇒ b⟩ ⇒ k(a, b)
    first   : k(a, b) ⇒ k(p(a, c), p(b, c))
    observe : k(Int, Int) ⇒ Int
    sample  : • ⇒ k(Int, Int)
    law leftId, rightId, assoc, embedFunctor,
        firstFst, firstEmbed, firstCompose
```

and a theory joins it by declaring its operations at its signatures:
`theory Arrow(k(_, _)) over Doctrine = …`. The prelude had never
declared a theory before; it does now, because a claim needs something
to point at in every module, and `Doctrine` is ambient the way `Base`
is — with the difference that `Base` cannot be written down and this
one is written down in full.

**`over` in a theory head is `over` doing its one job.** Declares
membership, applies nothing, mints nothing, and the elaborator checks
the claim against the written signatures — the same sentence as `over
T` for a template and `over M` for a hand-built morphism. One word,
three positions, one meaning. `extends` was the alternative and it
would have been a fourth keyword for a thing the language already
says.

**Four decisions worth the record.**

1. *Conformance, not copying.* A theory declares the doctrine's
   operations rather than inheriting them silently. That is what keeps
   the LEVELS expressible — `Vault` takes `compose` and `embed` and
   not `first`, and is refused for a wide stage, naming the slot that
   would have carried it — and it keeps the slot list readable at the
   theory. Inheriting the slots would have forced every model to fill
   all five and made the sealed example unwritable.
2. *The grade is the extending theory's.* Only the stacks are matched.
   `Doctrine`'s slots are pure and `Arrow`'s are `=Recursive>` (circuits are
   built with `fix`); a grade says what a model may DO, and the
   doctrine does not bound it. Had the grade been inherited, every
   transporting model in the language would have become `Recursive`, and
   `Reified`'s arrows would have changed for no reason.
3. *The laws ARE inherited*, and a model is audited against every one
   it can STATE — every slot the law names is one its theory declared.
   `Arrow` takes all five, so all seven run, for `Circuits` and for
   `Funcs`; `Reflective` takes them too, so the same seven now run
   over a carrier that is a program paired with its `Code`; `Vault`
   declares no observation and runs none, which is the honest reading
   of *sealed* — nothing leaves it, the audit included.
4. *A constructor parameter names two things.* `p(_, _)` is a type in
   a signature and, capitalized, the words `P` and `unP` in a law; a
   model's argument substitutes both (generated defs `M@P = Pair`,
   renamed by the same walk `use M` already performs). Without it the
   doctrine could not state a law about `first` — every such law has
   to pack and unpack a pair to be observed at `k(Int, Int)` — and the
   laws about `first` would have stayed copied into every theory,
   which is the thing this amendment is against. A word that is
   already its own image generates nothing, so a pairing actually
   named `P` is left alone.

**What the elaborator reads now.** `thOver th == Just "Doctrine"`, then
which of `compose`/`embed`/`first` the theory declared. The hom-object
is the doctrine's `k` as the theory instantiated it, and it must be one
of the theory's own parameters, because choosing the carrier is the
MODEL's job. Exits and entries are classified off the remaining slots'
declared arrows exactly as 5c read them. `isCompositionShape`,
`isEmbeddingShape` and `strengthShape` are deleted; what replaces them
is one general one-way matcher against the doctrine's own declared
arrows, so the refusal can print both signatures.

**Migration.** `arrP`/`thenP`/`firstP` are gone from the codebase:
the doctrine's names are `compose`/`embed`/`first`, which
`examples/reified.braid` already used, and one spelling per thing
decided the rest. `examples/circuits.braid` lost five hand-written
laws and gained two it never had; `examples/reified.braid` gained
`observe`/`sample` and with them the whole audit.

## Amendment (2026-09-13): `ev` in the normalizer

*Stage 5d, part two. The normal form stopped at `ev` of a wire. It
stops one step later now, and the step is the whole of what an Arrow's
composition does.*

**The rule.** `ev` of a value that is not a literal quotation is a
NEUTRAL APPLICATION when the value's arrow is CLOSED: the typechecker
wrote how many wires the function eats and leaves, so the normalizer
takes that many and emits `ev(f, x…)` as an uninterpreted term — which
is standard NbE's neutral case, arrived at from the other direction.
Only an OPEN arrow (a `fix` body's self wire, a handler slot, a bare
`Fn` inference never pinned) is left outside, and the refusal now says
which: *`ev` of a value whose arrow is not closed (there is no arity to
give it)*.

**Four things had to come with it**, and each was a separate bug the
new rule exposed:

1. **η for the exponential.** `embed [pass] ; f = f` weighs a
   QUOTATION against a wire. Without η every identity law of every
   category whose carrier wraps an `Fn` came out `false`. A quotation
   against a neutral of closed arrow type is now compared by applying
   both to fresh wires.
2. **Two quotations with different captures.** The old comparison
   required captures pairwise equal and otherwise answered `false` —
   which is a syntactic answer to a semantic question, and it is
   exactly the shape associativity takes (`compose (compose f g) h`
   captures a composite where `compose f (compose g h)` captures `f`).
   Each body is now run on ITS OWN captures plus a shared fresh
   segment, which is what equality of functions means. A refusal there
   falls back to the old syntactic `false`, so no verdict that stood is
   withdrawn.
3. **The wire types the two sides disagree about.** They are inferred
   independently, so the same wire came back `Arr(a0, a1)` on one side
   and `Arr(a5, a6)` on the other, and the clash marker threw the type
   away — which meant no arity, no split, no verdict, in every
   comparison of two programs not spelled identically. Types are now
   MERGED structurally: a type variable is "not said" and the other
   side's answer stands; a real disagreement is still a clash.
4. **Types survive into a quotation, and a single-alternative nominal
   type has one track.** A captured wire is the same wire, so its type
   is still true inside; and `data Pair(a, b) = a b` unrolls to a
   payload stack, which is one track, so `unPair` of a wire is a
   partition into one branch rather than a refusal.

**What flipped, measured.** For `Funcs` — the pure-function Arrow of
`examples/circuits.braid` — six of the doctrine's seven laws now
DECIDE by `sameCode`: `leftId`, `rightId`, `assoc`, `embedFunctor`,
`firstEmbed`, `firstCompose`. So do the sealed category `Sealed`'s
axioms. `capture ; ev` on a wire-borne closed `Fn` decides.

**What did not, and why — sharply.**

- `firstFst`, the naturality square, for `Funcs`: it is stated at three
  pairings, and the pairing's instantiation is LOST when a generic
  quotation body (`compose`'s) is weighed on its own, so the wire the
  law would `unPair` comes back a bare variable. Fixing it means
  propagating the expected type into the comparison — inference for the
  whole equation rather than per body.
- Every axiom of `Circuits`, and the `over`/`use` coherence at a
  stateful pair (still pinned by observation, 30 = 30): `compC`
  applies the self wire of a `fix`, whose arrow is `Fn⟨Σ =Recursive> Θ⟩`
  with Σ open. Codata is where this stops, and that is the honest
  place for it to stop.
- The self-calling transport law in `examples/optimizer.braid`: the
  same open self wire. Still compared spine to spine, and it says so.
- A composition over a BARE `Fn` wire (no hom-object) — the arrow
  inference leaves open, so it has no arity. Worth the note because it
  is the mirror of the good news: a DECLARED hom-object is what pins
  the width, so the doctrine's carrier is exactly what makes its own
  laws decidable.
- `loop`, and the Elgot identity: untouched, and out of scope
  permanently — a fixpoint equation is an axiom of an iteration
  theory, not an equation of the free category.

No example's output changed: the laws that flipped were never printed,
they were stated by `observe` at sample points, and they still are. The
flips are pinned in `test/Tests.hs` and described where they are true,
in `examples/circuits.braid`'s closing comment.

## Amendment (2026-09-13): `transformation`, shipped

*Stage 5d, part three. Designed on 2026-09-13 and shipped the same
day, once `ev` gave the verdict something to stand on.*

**The declaration.** `transformation Len : ListMonoid ⇒ IntSum = len` — two
models of ONE theory and a base word between their carriers. The
elaborator generates one square per slot,

```text
A@s ; K(Θ)  =  K(Σ) ; B@s
```

with `K` the component on each wire that is the theory's parameter and
the identity on the rest, and that is complete because the base is the
FREE category on the theory's generators: the squares for composites
paste from the squares for generators. The old record said the
generator was straightforward and the VERDICT was missing. The verdict
is what this amendment is.

**The verdict, in two ways and a refusal.**

1. **Proved** by the normalizer (`sameProgram` at check time, which is
   `sameCode`'s engine). This is now worth doing, which it was not two
   commits ago: a hom-object pins its own `Fn⟨a ⇒ b⟩` to one wire per
   side, so `ev` of it has an arity and a whole internal functor's
   squares go through. All five of `Forget`'s do, in
   `examples/transformations.braid`.
2. **Sampled**, at the theory's own evidence, when the normalizer will
   not: `sample : • ⇒ a` supplies the inputs, an exit observes a result
   that is a carrier (a carrier cannot be compared), `eq?` decides, and
   the check runs at module start beside the model laws. All three of
   `Len`'s are this case: `len` is a fold and a fold applies its
   handler, whose arrow is open.
3. **Refused**, naming the slot and the missing evidence, when neither
   reaches. That is the honest third answer, and it is what the design
   record asked for a stage ago.

**Decisions worth the record.**

- *Evidence is a generator.* `sample` is a slot, so a transformation
  must preserve it. The example's list has seven elements because
  `IntSum`'s
  sample is 7. The alternative — exempting evidence slots — would have
  been a second class of slot, and there is no such thing in a theory.
- *`⇒`, not `->`.* The arrow of every written type in Braid; `->` is
  only its ASCII synonym there, and it is already the binder's arrow.
- *The component is a word.* `Len` is forward-declared at the type the
  two model heads wrote, exactly as a theory slot is, so a def may name
  it wherever the declaration sits.
- *The compiler may write the compiler's spelling.* The squares are
  ordinary generated defs that name `A@op` and `B@op` directly, and
  `ecGen` lets them — a def the compiler wrote may reach a slot the way
  the compiler spells it, while source still may not. That is cheaper
  and more honest than wrapping each side in a scope that would
  transport what it touched.
- *One parameter.* A transformation is a component AT the theory's
  parameter, so a theory with two is refused, naming the count.
  `Doctrine` itself
  has two (the hom-object and the pairing); the theories that extend it
  have one, which is the case that matters.
- *`use Len` is not shipped.* Transporting a template's result from one
  model to another wants a second elaboration of the template, and
  nothing has asked for it. The word is enough for everything the
  examples do.

**What the two examples pin, side by side.** `Len` proves nothing and
samples everything; `Forget` proves everything and samples nothing.
Same declaration, two verdicts, and the difference is the carrier — a
declared hom-object is what makes a category's own laws decidable.

## Amendment (2026-09-14): recursion is a marker

The 2026-09-09 amendment above ("recursion at a typed boundary") took
the name out of the body and put the knot in a word with a type. It
bought three things — closed spines, total functors, a label that says
"may recurse" — and it charged for them in the one currency the design
is supposed to refuse: an **exception to the principle**. Stage 5c½
stated the principle as *every label names a functor that a written
`use` applied, the four io prims being the one pre-applied case*.
`Rec` — as `Recursive` was then spelled — was a second pre-applied
case, minted by the prim `fix`, and nothing had been written to apply
it. It also charged a tax on every
user who wanted a recursive definition: `[body] ... >> fix ... >> ev`
is three stages of plumbing around one idea.

**The marker pays the first debt and cancels the second.** `use
Recursive` is a written scope in a def's header. It puts the def's own
name back in scope in its own body, and — being a scope — it mints its
receipt exactly as `use Traced` does. There is no pre-applied label
left but io.

```braid
def fac =
    use Recursive
    (n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> fac) >> *)) >> merge)
# fac : Int =Recursive> Int
```

### It is a rewrite, not a special form

Elaboration replaces the body with the closed form the language already
had:

```text
def f = use Recursive ; B
  ↦  use@Recursive >> [ (#self ... -> B[f := #self ... >> ev]) ] ... >> #fix ... >> ev
```

Three properties make this cheap rather than clever.

1. **It is syntactic.** No types are consulted, so inference stays the
   CHECKER of what elaboration emits rather than an input to it — the
   same discipline the resource router has kept since stage 4. A binder
   parameter named like the def shadows it, because the rewrite stops
   at a binder that rebinds the name; a self-call inside a quotation is
   a capture, which abstraction elimination already handles.
2. **It runs INNERMOST among the header's scopes.** `use Traced
   Recursive` traces the closed spine, not a name that is not in scope
   yet. Written as separate lines the order is the writer's, and the
   useful order is the one the single-line form picks.
3. **The knot is unwritable.** `#fix` — the machinery that was the prim
   `fix` — is spelled with a character that opens a comment, so no
   program and no reflected atom can name it. That is the same device
   as `#dist:K`, `#fold:` and `use@F`, and it is what let `fix` leave
   the primitive set (48 → 47) without the language losing a knot.

### Closed spines are a property of ELABORATED defs

This is the sentence the 2026-09-09 amendment should have written, and
could not, because before the marker the two readings coincided. A
**source** body may now name the def it is in. An **elaborated** body
may not: every def that reaches inference is still a closed spine over
its prefix scope, so every stage's scheme is computable without knowing
the def's own type, `reflect` is total on it, and a functor out of it
is total. Nothing downstream of elaboration changed at all — which is
the argument that the marker is not a new feature but a spelling.

Verified, not assumed: `use Traced` over a `use Recursive` factorial
traces every stage and prints `24`; `reflect`/`evalAs` round-trips a
marked def and runs it; an unlabelled `evalAs` witness still refuses
it, naming `Recursive`.

### `fix` is derived, and says so on its own arrow

```braid
def fix = use Recursive ; (b -> [(b >> fix >> id) ... >> b ... >> ev])
fix : Fn⟨Fn⟨ρ0 =Recursive> ρ1⟩ ρ0 ⇒ ρ1⟩ =Recursive> Fn⟨ρ0 =Recursive> ρ1⟩
```

Eta-expanded, because Braid is call-by-value: the self-application sits
under a quote and is tied only when the knot is run. The `id` is load
bearing — a grouped atom in non-final position is instantiated closed,
and closing would erase the knot's own arity.

**One honest regression.** The prim's own arrow was pure: tying a knot
ran nothing. The derived word's arrow carries `Recursive`, because it
runs the knot's `ev` and because the scope it is written under mints
unconditionally. Everything *inside* the arrow is unchanged — the body
is asked for no grade, the self and the result carry the label — so the
only programs this can reject are ones that wrote a *pure* arrow for
`fix` itself, which nothing in the tree did. `loop`, `while` and
`until` keep their schemes exactly. The scheme-subsumption test that
pins "today's word is at least as general as yesterday's prim" gained a
`fixD` slot written `=Recursive>` to record the difference rather than
hide it.

`fix` is still the right word for **open** recursion — a body someone
else wrote, a memoizing or logging `self`, a body built at runtime.
That is the whole of what it is for now, and the tutorial says so.

### What the normalizer had to be told

A def written under the marker ends in `ev` of the knot, and the knot's
arrow is `Fn⟨Σf =Recursive> Θf⟩` with `Σf` an open stack variable —
`sameCodeC`'s standing refusal. Inlining such a def could therefore
only trade a verdict for a refusal, so the normalizer **holds knots
opaque**: a def whose body mentions `#fix` decides as an uninterpreted
word of closed arity, which is exactly what the prim `fix` was. That
keeps `F(fix b) = fix (F b)` decided (`examples/optimizer.braid` §8)
and changes no other verdict.

### Mutual recursion: the shape, not the build

Not shipped. Recorded so the next attempt starts further along:

- **Syntax.** Adjacency is the tempting block rule — a run of
  consecutive defs each headed `use Recursive` may name each other —
  and it is the wrong one, because the block boundary would be
  invisible and a blank line would change meaning. The honest spelling
  names the partners: `use Recursive f g` in each header, or one
  `recursive f g = …` block. Either way the header still says it.
- **Elaboration.** The block's bodies become one knot at a STACK rather
  than at an arrow: `#fixv : Fn⟨Δ =Recursive> Δ⟩ ⇒ Δ` with `Δ` the
  stack of the block's `Fn`s. The body takes the k knots as its input
  stack and returns the k quotes; a call to `fᵢ` inside any body
  becomes the i-th bound wire, applied with `... >> ev`. Each def is
  then a projection out of the tuple.
- **Runtime.** `#fixv` is the same lazy early-binding cycle `#fix`
  already builds, at k names instead of one.
- **The awkward part** is the projection: k defs must come out of one
  knot, which either needs a numbered family (`#proj:i` — house style
  says no) or a per-def re-tie that recomputes the tuple. That is the
  open question, and it is why this is recorded rather than built.

## Amendment (2026-09-14): Float, and the first flagship

*Stage 6a. One base type, and the first example written to find out
what the declaration layer costs a person who is trying to compute
something rather than demonstrate something.*

### What `Float` is, and what it is not

`Float` is an IEEE double and a base type **beside** `Int`. It is not a
numeric tower, not a class, not a coercion, and not a second reading of
any word that already exists. `+` is Int addition and will stay Int
addition. The two types meet only where a program says they meet, at
`toFloat : Int ⇒ Float` and `floor : Float ⇒ Int`, and a stage that
mixes them is a type error whose message names both vocabularies and
both crossings — because in a language with no tower, "add a coercion
here" is never the fix; *write the other word, or write the crossing*
is.

Seven decisions worth the record.

1. **The spelling scheme is alphabetic, and the lexer forced it.**
   `f+ f- f* f/ f<` was the first choice and it does not lex: `-` is
   not an identifier character — it heads `->`, `---` and every
   negative literal — so `f-` is two atoms, `f` and `-`. A scheme that
   breaks on subtraction is not a scheme, so the family is `fadd fsub
   fmul fdiv flt?`, with `fexp fsin fcos fsqrt` and `fneg`/`fabs`
   beside them. One scheme, every word, no exceptions.

2. **There is no `feq?`.** `eq?` is already polymorphic and already
   reaches a `Float`, and one spelling per thing forbids a second. What
   it means at `Float` is IEEE `==`: bit equality up to the one
   identification IEEE makes (`0.0` and `-0.0`) and the one it refuses
   (`NaN` equals nothing, itself included). `(0.1 0.2 ; fadd) 0.3 ;
   eq?` is **false**, and a language that quietly made it true would be
   lying about the two doubles. A tolerance test is four words and
   belongs where the tolerance is known; `examples/autodiff.braid`
   writes one.

3. **The literal is digits, a point, digits.** `1e-3` is refused where
   it is written, with the fix in the message. The reason is the same
   `-` as in (1): an exponent form needs a lexer case of its own for a
   notation nothing ever prints back. A leading digit is required, so
   `.5` is still the symbol it always was.

4. **The display convention is pinned: shortest round-trip decimal, no
   exponent, always a point.** `showFFloat Nothing` over Haskell's own
   shortest-identifying digits. What that buys is a property, not a
   preference: **every finite Float prints as a Float literal that
   re-reads as itself**, so a printed result is a Braid term, and a
   worked example's output can be pasted back into the file that
   produced it. The three non-finite doubles print `NaN`, `Infinity`,
   `-Infinity`; they are values and not literals, and `valueToCode`
   refuses to splice one, which is the honest edge of the property.

5. **Eleven implementation prims, 47 → 58, and the criterion did not
   move.** A word keeps its place in the kernel if it is a structure map
   of the doctrine *or if it touches the implementation*; a double is a
   machine number and nothing in the language can build one, so the
   Float arithmetic is in the kernel for precisely the reason the Int
   arithmetic and the four io edges are. The count is a large jump and
   it is the honest one: these span no structure, they *are* the
   machine. What did **not** enter: `fneg` is `0.0` minus and `fabs` is
   one `flt?` and a two-track row, so both are prelude defs with their
   derivations visible, and the Float mirrors of `gt?`/`gte?`/`lte?`
   are not written at all until something wants one.

6. **`fdiv` keeps `div`'s refusal.** Dividing by zero has no answer
   worth inventing, at either type, and one spelling per thing extends
   to one behaviour per question. Everything else that can leave the
   finite doubles — `fexp` overflowing, `fsqrt` of a negative — yields
   the IEEE value, because those are answers.

7. **`Atom` did not gain an alternative.** A Float literal reflects as
   a WORD atom rather than as a fourth literal track. `Atom`'s
   alternative list *is* `foldAtom`'s arity, and every reflective
   program in the tree — `examples/transpose.braid`,
   `examples/reified.braid`, the tracer and the meter — is written
   against seven cases; an eighth would rewrite all of them for a
   literal that already round-trips by name (`unparse` prints `2.5`,
   `parse` reads it back as a literal, and the normalizer treats it as
   the same nullary constant either way, which is what makes `[2.5 ...]`
   and `[2.6 ...]` decidably different). The asymmetry is recorded here
   rather than hidden: it is the one place where a Float literal is not
   quite an Int literal.


### The first flagship: `examples/autodiff.braid`

**The thesis.** Differentiation is a functor into pairs of a value and
a linear map — `D(f)(x) = (f x, f'(x)·—)` — and it is a functor
*because* the chain rule says composition goes to composition
(Elliott, *The simple essence of automatic differentiation*; READING).
A model of a theory in Braid IS a functor out of the free category on
that theory's generators. Put those two sentences together and the
chain rule has nothing left to do: write the arithmetic as a `theory`,
write differentiation as a `model` of it, and each slot says what the
derivative of **one** operation is. Composition is the language's.

The file contains **no `Code`, no `functor`, no `getCode` and no chain
rule**, and that absence is the result. It is the argument for the top
of §12's ladder over the bottom of it, made by a program that anyone
would have expected to need syntax.

**Forward and reverse are one linear map, twice.** `Fwd` carries the
tangent — the map applied to a seeded direction. `Rev` carries the
map's **transpose** as a continuation `Float ⇒ Grad`: given the adjoint
of this node, return the gradient of the inputs. `transformation Transpose :
Fwd ⇒ Rev` is the sentence that says they are the same map, and it is
a declaration rather than a comment. Two consequences fall out that are
usually engineering:

- **Fan-out needs no special case.** Continuations are linear, so a
  value used twice contributes twice: call its continuation twice and
  add. There is no tape, no node id, no visit count. `k2` is four
  words and is the whole of it.
- **One reverse sweep gives every partial**, where forward mode needs
  one run per input. The file prints both, at the same function, to
  make the difference visible rather than asserted.

**What the transformations establish, measured.**
`transformation Value : Fwd ⇒ Floats = value` — forgetting the tangent
— is the claim *AD computes
the right value*, and **all eight squares are PROVED** by the
normalizer (add, mul, neg, lit, exp, sin, sample, observe), not
sampled. A `Dual` is two Float wires under a roll, `unDual` partitions
into one track, and the whole square normalizes. That is the strongest
verdict the machinery has and it is the one that matters here: the
correctness claim about a differentiator is that it does not change the
value.

**THE EXIT PROBLEM, and how it was resolved.** A theory's exit is a
SLOT, so it has one type for every model: `observe : a ⇒ Float`. `Rev`
has two things to hand back — the value and the gradient — and the
theory cannot ask for the second, because `Floats` and `Fwd` have
none. A per-model exit would be a slot whose type varies with the
model, which is not what a slot is; the alternatives (a second theory
parameter, a sum-typed exit that three models fill differently) both
buy the gradient by making the theory about reverse mode. So the exit
is the VALUE, matching `Fwd`, and the gradient is read by an ordinary
base word outside the theory: `backward : Rev ⇒ Grad`, which runs the
accumulated continuation at adjoint `1.0`. *Entering is a marker,
leaving is a model* already said the shape of this; what the flagship
adds is that a carrier may have more to say on the way out than one
slot can carry, and the answer is a word and not a bigger slot.

**The gap `transformation` has, stated exactly.** `transformation Transpose : Fwd
⇒ Rev = transpose` **cannot be declared as the machinery stands**, and
the reason is the machinery and not the maths. When a theory's
parameter is a WIRE rather than a hom-object, `sampledLaw`'s `observer`
returns the empty stage — the theory's exit is NOT applied — on the
reasoning that "a wire parameter is an ordinary type, since `eq?`
reaches it". `eq?` does reach it; but a `Rev` holds a CLOSURE, and
`eq?` on a quotation is syntactic. So the sampled square weighs two
extensionally equal continuations that were built by different code,
answers `false`, and the module is refused with *the square for slot
'add' does not commute at the theory's samples*. `sameCode` answers
`false` one step earlier for the same reason.

Measured, not guessed, by instrumenting `checkTransformation`:

| slot | verdict |
|---|---|
| `sample`, `observe` | proved by the normalizer |
| `lit` | proved — *if* `rlit` is written `(c -> c (0.0 ; scaleK) ; Rev)`, the zero linear map, rather than `[(d -> gzero)]`; otherwise not provable, and **not statable** either, because `lit`'s input is a `Float` and no `sample` supplies one |
| `add`, `mul`, `neg`, `exp`, `sin` | sampled, and FALSE |

Note where the gap lives: it is exactly the **wire-parameter** case. A
theory declared `over Doctrine`, whose parameter is a hom-object, takes
the other branch of `observer` and goes through the exit already. So
the machinery was right for the case it was written against
(`examples/transformations.braid`'s `Forget`) and wrong for the first theory
that put a function inside an ordinary carrier. `Smooth(a)` is an
algebraic theory over one carrier — a ring — and not a category with a
hom-object, which is why it is not declared `over Doctrine`: Elliott's
functor is between categories, and the model of an algebraic theory is
the same statement one level down, on the free category the theory's
generators present.

The fix is one line — apply the theory's exit for a wire parameter too,
i.e. delete the `PCon` special case in `observer` — and it is
deliberately NOT made in this stage, because a stage that finds a gap
and patches it in the same breath has not tested anything. The file
states the six squares by hand instead, through `rvalue` and
`backward`, and prints the failing `eq?` beside them so the gap is
shown rather than described.

*(Made in stage 6a½, 2026-09-14. The `PCon` case is deleted, the exit
is applied whatever the parameter's kind, and `transformation Transpose :
Fwd ⇒ Rev = transpose` is a declaration in the file: `lit`, `sample`
and `observe` **proved**, `add`, `mul`, `neg`, `exp` and `sin`
**sampled** through the exit. `lit` proves only because `rlit` now
builds the zero linear map as `(0.0 ; scaleK)` — the table above
predicted exactly that, and it is a real constraint: `lit`'s input is
a `Float`, no `sample` reaches it, so a square like that must prove or
the module is refused. The hand-stated squares and the printed `eq?`
came out of §7 with the gap they demonstrated; what replaced them is
three sentences and a declaration. Two things the fix did NOT buy: a
theory with no exit still compares carriers directly — there is
nothing else — though a failure now names the fix, and the sampled
squares establish their claim at the exit, which here is the value.
The verdicts are stored on the module and printed by `:transformations`,
because the gap was found by instrumenting the compiler with
`Debug.Trace`, and a verdict that takes a recompile to read is a
verdict nobody checks.)*

A second, smaller finding rides along: `sameCode` here answers **false**
rather than refusing. Everywhere else in the tree a verdict the
normalizer cannot reach is a refusal, and `false` means *different
morphism*. For two quotations that close over different captures it
means *spelled differently* — the 2026-09-13 amendment's fallback
("a refusal there falls back to the old syntactic `false`") reached
further than expected once carriers began holding closures.
*(Closed 2026-09-14, stage 6a¾: `fallbackFalse` is deleted and the
refusal propagates — see the amendment at the end of this file. The
finding was right about the wart and wrong about this case: these
squares are not refused at all, they are decided **false**, because the
two sides differ up to the arithmetic of the uninterpreted `fadd` and
`fmul`. `false` about the free category is not `false` about the model,
so they still go to the samples, and `:transformations` now says which
of the two answers sent them there.)*

**The `Gradient` resource.** `Rev` SUMS: every node returns a gradient
and `gadd` merges them coming back. The last section threads ONE
accumulator through the whole reverse sweep instead and lets the leaves
add into it — the same functor with the adjoint threaded rather than
summed, a fourth model `RevThread : Smooth(RevG)`, and a program typed
`Float ρ0 =RevThread Gradient> ρ0`: two receipts on one arrow, which
model read the template and which resource the scope threaded. It is
installed by rolling a `gzero` and discharged by unrolling, exactly as
`metered.braid` installs and discharges `Fuel`; there is no handler
keyword and none was wanted. What it cost to write is one sentence
worth recording: **`Fn⟨Gradient Float ⇒ Gradient⟩` has to be written
out in the `data` declaration**, because the `=Gradient>` fold is
display and does not run backwards.

**What is not built, and why it is not a small step.** Second
derivatives need `Fwd` to be a model of `Smooth(Dual(a))` for ANY model
of `Smooth(a)` — a model **parameterized by a model**. A `model` head
names a declared data type, so `model Fwd(M) : Smooth(Dual(M))` is not
writable; templates are parameterized by a model and models are not.
That is the honest shape of the missing feature and it is a real one.
Wang–Rompf's per-node accumulator (shift/reset; READING) wants a
reified graph — a map from node ids to partial sums — which is a data
structure nobody has built here. And `Grad` is two slots because a
gradient indexed by its inputs is `Fin(n)` work joined to this, which
is a different piece of work.

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
- **`eq?` on Code is syntactic** — that has not changed, but
  `sameCodeC` is the semantic alternative wherever the fragment
  reaches, and since 2026-09-13 that includes quotations, rows, and
  `ev` of a wire whose ARROW IS CLOSED. What is left outside is
  narrower and sharper again: `ev` of a wire whose arrow is OPEN. A
  knot body that calls itself, a fold that applies its handler, a handler
  slot — each applies an `Fn` whose input stack is an open variable, so
  there is no arity to give it. Those laws are still stated with `eq?`
  and labelled syntactic.
- **A sampled `transformation` square over a wire parameter compares
  CARRIERS with `eq?`** (2026-09-14), and a carrier may hold a closure,
  where `eq?` is syntactic. The theory's exit is applied only when the
  parameter is a constructor. Found by `examples/autodiff.braid`'s
  `Fwd ⇒ Rev`, whose squares commute and are reported as not
  commuting; the fix is one line and is not made yet. In the same
  place, `sameCode` answers **false** rather than refusing when two
  quotations differ only in their captures — `false` should mean
  *different morphism*, and here it means *spelled differently*.
  **CLOSED 2026-09-14 (stage 6a½)**: the `PCon` case is gone, so the
  exit is applied whatever the parameter's kind, and
  `transformation Transpose : Fwd ⇒ Rev` is declared in the flagship. What a
  theory with no exit does is unchanged — it compares the carriers —
  but a failure now names the fix (*declare an exit `observe` in the
  theory*), and a square the normalizer PROVED is no longer sampled
  besides. The `sameCode` half is **closed 2026-09-14 (stage 6a¾)**:
  `fallbackFalse` is gone, so a refusal stays a refusal. It turned out
  not to be what sends these squares to the samples — `sameCode`
  *decides* them false, up to arithmetic — and both answers go to the
  evidence, with the verdict recording which. What the machine checks
  about `Transpose` is therefore still what the exit can see — the
  value — and the gradient half stays a printed check in §5 of the
  file.
- **A model parameterized by a model** is not writable (2026-09-14): a
  `model` head names a declared data type, so nesting forward mode
  inside itself for second derivatives — `model Fwd(M) :
  Smooth(Dual(M))` — cannot be said. Templates are parameterized by a
  model; models are not.
- **`transformation` is shipped** (2026-09-13), and what is still missing is
  narrower: a square over a model whose slots are folds is decided at
  SAMPLES, not proved, because equality modulo a model's defining
  equations is structural induction over an initial algebra — a
  different procedure from normalizing in a free category. A theory
  with no `sample` slot and a square the normalizer cannot prove is
  refused rather than assumed. `use Len` — reading a template through
  one model and landing in another — is not shipped.
- The **image-tagging question above is open**, and the coeffect
  decision with it.
- **A category's axioms are decided when its composition applies a
  wire whose arrow is closed** (2026-09-13) — `Funcs` and `Sealed`
  prove theirs — and are not when it applies a knot's self wire,
  which is every codata model, `Circuits` included. Those run through
  `observe`. `firstFst` is undecided even for `Funcs`; see the
  amendment above for why.
- **A written `Fn⟨a =K> b⟩` is not the folded form.** The display fold
  does not run backwards — for modes or for resources — so the carrier
  is written out. For a mode it could not run backwards anyway: type
  lines are parsed before theories and models, so a slot cannot
  mention a mode declared from a model of its own theory.
- **Carrying a word across categories** is `transformation` now: a component
  between two models of one theory, with its squares decided. What it
  does not do is carry a TEMPLATE across — `use Len` would read a
  template through one model and land it in another, and that is a
  second elaboration nobody has asked for yet.

## Amendment (2026-09-14): `morphism` → `transformation`

*A rename, one spelling, no new machinery.*

Two models of one theory are two functors out of the presented
category; a map between them with one component per object and a
commuting square per generator is a **natural transformation** between
those functors, and the generated squares are its naturality squares.
So the declaration is `transformation Len : ListMonoid ⇒ IntSum = len`,
the REPL command is `:transformations`, and `examples/morphisms.braid`
is `examples/transformations.braid`.

`morphism` was correct only in the reading "a morphism in the category
of models", which is underspecified — every arrow in every category is
a morphism, and the word said nothing about which one this is.
"Natural" is implied and therefore not written: there is no other kind
of transformation here, and the checker enforces naturality. For an
algebraic theory the same thing is a **homomorphism of models**; for a
theory over the `Doctrine` it is also an **internal functor**. One
declaration, three readings, one spelling.

The old keyword is refused with the new one: *`morphism` is spelled
`transformation` since 2026-09-14 … write `transformation Len :
ListMonoid ⇒ IntSum = len`*, the way `instance` and `mode` are refused.

## Amendment (2026-09-14): a refusal stays a refusal

*Stage 6a¾, part two. `fallbackFalse` is deleted.*

`eqSym`'s quotation case wrapped its extensional comparison in
`fallbackFalse`, a two-line function that turned `Left msg` into
`Right False`. It was written so that no verdict standing before the
extensional route arrived would be withdrawn by it, and the reasoning
was local and wrong: in that one corner `false` meant *could not
decide*, while everywhere else in the tree `false` means *provably
different*. A verdict that means two things is a verdict nothing
downstream can trust — and the transformation checker is downstream.

The fix is a deletion. `sameCode` and `sameCodeC` now error over
quotations whose captures are not pairwise equal, and over the two eta
comparisons beside them, the way they already error everywhere else,
and each refusal names its case. **No example's printed output changed**
— nothing was relying on the fallback, including the `sameCode` laws in
`optimizer`, `distributive`, `circuits`, `reified` and `into`.

**What the transformation checker does with the two answers.** The
interesting half. `false` is *different as programs of the FREE
category*, which is a real statement about the free category and not a
statement about the model: a model's words satisfy the theory's laws,
and the normalizer has none of them. `Transpose`'s five sampled squares
are exactly that — the two sides are equal only up to associativity and
distributivity of `fadd` and `fmul`, which are uninterpreted. So the
rule is not "false refuses":

- **proved** — `sameCode` says true, for every input and every
  interpretation.
- **sampled**, whichever of *false* or *refused* the normalizer said,
  because only the theory's evidence knows the model. The verdict
  carries the reason next to the point count:
  `sampled (2 points; differ in the free category)` against
  `sampled (2 points; ev of an open wire)`. The refusal's own message
  names its case (MANUAL §12.9); the verdict keeps the naming half.
- **refused** when there is no evidence to fall back to, and the
  refusal now says *which*: `is FALSE — \`sameCode\` decides the two
  sides are different programs of the free category` where it used to
  say only *does not decide*. `test/Tests.hs` pins a planted false
  transformation on pure wiring (`_ drop` against `drop _`, no
  arithmetic anywhere) to hold that message down.

The prediction in the 6a½ record — that the `sameCode` half of the
closure finding was "a `false` where a refusal belongs, and it is what
sends these squares to the samples" — was half right. The wart was real
and is gone; the squares were never refused, they were decided false,
and the reason they need the samples is arithmetic rather than
machinery. Measuring it was the point of carrying the reason on the
verdict.

## Amendment (2026-09-14): three things the first flagship asked for

*Stage 6b. `examples/autodiff.braid` was written against the language as
it stood; its report named three places where the file was shaped by the
notation rather than by the mathematics. All three are now closed, and
the first two are SYNTAX in the strict sense the house style means:
they rewrite to existing words before anything downstream can see them.*

**1. Destructuring binders.** Six slot bodies opened with the same
ritual — `unDual _ ; _ _ unDual ; (a da b db -> …)` — because a `data`
carrier's fields had no way into a binder head. Now they do:
`(Dual(a, da) Dual(b, db) -> …)`, over any **single-alternative** `data`
type, mixed freely with plain parameters and with the open `...` form,
and one field may itself be a pattern.

The rewrite is token-level and happens before the parse tree exists,
producing *character for character* the source a hand wrote yesterday —
the `un` stage for the j-th slot padded by one `_` per wire already
un-constructed to its left and one per slot still whole to its right.
So there is no destructuring binder anywhere downstream: no Term, no
inference case, no runtime case, and `reflect` is free rather than
extended (the test that pins this reflects both spellings and compares
the unparsed code). Two refusals name their fix: a multi-alternative
carrier (*use a row*) and an arity that is not the constructor's.

**2. Lines that wrap.** A newline is a strict `>>`, so a stage that did
not fit on one line could not be written at all, and a line beginning
with `;` was `Expected a tensor stage, got: TokSeq` — which is why the
flagship pulled `newton` and half a dozen square checks out into named
one-line defs. Three spellings now say *not yet*: a line ending with
`;`/`>>`, a line beginning with one (both redundant with the newline,
which is exactly why they read well down a page), and a trailing `\`,
which drops the newline outright so the tensor stage itself wraps.

`\` is the one continuation form, and the reasoning is the interesting
part: **indentation cannot be made to mean this**. Every multi-line def
body in the language is indented deeper than its `def` line and relies
on newline = `>>`; a rule that read deeper indentation as continuation
would silently change the meaning of every one of them. `\` is
stage-final where `|`, `...` and `---` are not, and it is unwritable in
a program today, so no file can change meaning. The line-based layer
above the parser learns the same rule, so an inline `def` may wrap the
way one that leaves a bracket open already could.

**3. The exit problem.** The real one. A theory's exit is a slot, so it
has ONE type for every model; `Rev` had two things to hand back and the
theory could only ask for one, so the gradient was read by a base word
*outside* the theory and the gradient half of `Transpose` was not
machine-checked at all. The answer is not a slot whose type varies with
the model — that is not what a slot is. It is that **an exit whose
result varies by model is a theory parameter**:

    theory Smooth(a, g) = … ; gradient : a ⇒ g
    model Floats : Smooth(Float, Float)
    model Fwd    : Smooth(Dual, Float)
    model Rev    : Smooth(Rev, Grad)

That half needed no new machinery: multi-parameter theories, per-model
instantiation and slot substitution were all already there, and a wire
parameter used only in an exit's output types simply works.

The consequence is where the work was. A component of `transformation
T : M ⇒ N` was one word on *the* parameter, and `gradient : a ⇒ g` has
its two ends at different parameters — one component cannot draw that
square. So a natural transformation between models of an n-parameter
theory is **n components, in the theory's order**:

    transformation Transpose : Fwd ⇒ Rev = transpose, gx

with each component checked at the arrow the two model heads wrote for
*its* parameter, and the generated squares putting the right component
at each position of the slot's stacks. A parameter whose type is the
same in both models writes `id` — an ordinary word, no case in the
checker. Sampling follows the parameters too: evidence for a wire comes
from an entry of *that* parameter, and a result is observed by an exit
of *that* parameter — `observe : a ⇒ Float` is not an exit for a `g`,
and a `Grad` result is compared with `eq?` directly, which is sound
because a `Grad` is two Floats and not a closure.

What it buys, in one line of `:transformations`:

    gradient  sampled (1 point; differ in the free category)

`tangent ; gx` against `transpose ; backward` — the statement that
forward mode's tangent and reverse mode's accumulated continuation are
the same linear map read two ways. That was §9's first entry under
*what is NOT built*; it is a square now.

## Amendment (2026-09-14): the frame is a model

`examples/frame.braid` is the second flagship, and it settles a
question the first one only posed: **what is the right shape for a data
frame in a language with one arrow?**

The answer is that a frame library is not a library. It is a **model of
the Doctrine**, and the user's code is a program on ONE ROW.

    data Trade = (sym: Str, px: Float, qty: Int)
    def notional = use Frame ; dup ; px qty ; _ toFloat ; fmul
    #   notional : Trade =Frame Recursive> Float

`List` appears nowhere in a row program. The hom-object is a **function
between columns**, `Col(a, b) = Fn⟨List(a) ⇒ List(b)⟩` (with
`=Recursive>` inside — see *Pragmatics* below); `embed` is
`map`, `compose` is composition, and `first` is **unzip / map / zip**.
The strength is, literally, *the other columns ride past* — which is
what makes the two-wire stage `px qty` legal inside the scope, and it
is the only reason a hom-object with one wire per side can carry a
row of three scalars at all.

**The laws come free, and they are the right laws.** A frame library
usually promises "map is a functor" in its documentation. Here the
promise is the Doctrine's seven arrow laws, and they are run by the
audit before the file prints a line. `Frame` declares all five doctrine
slots — the three structural ones plus `observe` and `sample` — so all
seven run; a model whose `compose` is wrong stops the file with `law
'leftId' fails for model Frame`. Nothing was added to the checker.

### The index reading

Conceptually a frame is **a map from an index to a row**: `Fn⟨I ⇒
row⟩`, together with its key set. v1 represents it as `List(row)` with
an **implicit positional index** `0 … n−1`, which is `Fin(n) ⇒ row`
stored tabulated and flat — exactly what a `List` is here.

The reading is worth keeping even though it is implicit, because it is
what says *why the model is a functor*: `map` preserves the index
pointwise, so a transported row program cannot move a row, cannot drop
one, and cannot see its neighbours. Everything that does any of those —
`keep`, `groupBy`, `sortBy`, `join`, the aggregations — is written
**once**, at frame level, outside every scope. **A functor cannot drop
rows**, and that sentence *is* the division of labour in the file. It
is not a style rule; it is what the model is.

Making the index explicit — a key set in the carrier, so `join` is a
map union rather than a nested scan and two frames may share an index
without being the same length — wants `Col(i, a, b)`, a
three-parameter hom-object. The Doctrine declares `k(_, _)`. Parked.

### Why column names are words, not types

`data Trade = (sym: Str, px: Float, qty: Int)` generates `sym`, `px`
and `qty` as **projection words** (MANUAL §5). They are ordinary
definitions: they compose, they quote, they reflect, they go to `map`.
Nothing in the type system knows a column is called `px` — two
declarations with the same layout are the same type, and the header
travels as **runtime data**, a `List(Str)` handed to the printer.

The alternative — column names in the type, a record type with a row of
labels — was considered and rejected, and for once the reason is not
implementation cost:

- Braid's products are the **stack**, and the stack is positional. A
  labelled product would be a second product with a second theory of
  subtyping, width and permutation, and every structural rule in the
  language would grow a labelled case.
- A field name that is a word is one that the rest of the language
  already knows how to do everything with. `[px] rows ; column` needs
  no projection syntax, no lens, no `.`; `px qty` is an ordinary tensor
  stage; a projection `reflect`s because it *is* wiring (`unTrade` and
  then the stage that keeps one wire).
- Names as words collide like words, which is the honest behaviour:
  **objects are added, never merged**. Two types cannot share a field
  name. That is a cost, and it is the same cost `import` pays, for the
  same reason.

What is given up is the thing a typed data frame is usually sold on:
the checker will not tell you that you selected a column the frame does
not have. Here the field word simply does not exist, which is the same
error one level down — an unknown word rather than an unknown column.
For a CSV read at runtime (part 3's `table`) the declaration is
generated from the header, so the two are the same check.

### The sums-under-transport gap

The one thing the Doctrine cannot carry is a **filter written as a row
program**. `row ⇒ (row | •)` is a stage whose output is a SUM, and
transporting it needs a slot the Doctrine does not declare: Hughes'
`ArrowChoice`, whose generator is `left : k(a, b) ⇒ k((a | c), (b |
c))` — the coproduct's strength, dual to the one `first` already
carries. Without it, `use Frame ; qty ; _ 100 ; gte?` has nowhere to go:
`first` whiskers a product and there is no `left` to whisker a sum.

`keep` sidesteps it, and the sidestep is exact rather than a
workaround: the **deciding** is a column (`Trade ⇒ Bool` — a functor may
compute that), and the **dropping** is frame-level (a functor may not do
that at all). So the mask splits the filter along precisely the line
the index reading already drew. That the workaround lands on the same
line as the theory is the evidence that the line is real.

Adding `choice : k(a, b) ⇒ k((a | c), (b | c))` to the Doctrine is the
obvious next move, and it is a real one: it would make `into`-shaped row
code transportable, and every model would owe a binding. It is not
free — `Circuits`, `Funcs`, `Reified` and `Sealed` would all have to
answer for it, and a sealed category that declares no choice would then
refuse a whole class of stage rather than a whole class of shape.
Parked with the reason written down.

### The column store, and the transformation waiting for it

`Frame` stores the frame as **rows** and computes on **columns**. The
other representation — the frame as a stack of columns, one wire per
column, `Str^n Float^n Int^n` — is the one a real analytical engine
uses, and in this language it would be a **second model of the same
theory**. Then

    transformation Columnar : RowStore ⇒ ColStore

is an ordinary declaration, its squares generated and decided by the
machinery `examples/transformations.braid` already has, and "the column
store computes the same answers" stops being a comment.

It waits on one thing, and it is the thing already parked under *not
admitted: a stack-shaped embedding* (MANUAL §8): a hom-object whose
arguments are whole **stacks** rather than wires. A column store's
object is n columns; packing it with the pairing would defeat the
representation, which is the entire point of having it. So this is the
flagship that would justify the stack-shaped carrier, and it is now
written down as such rather than as a maybe.

### Pragmatics, recorded

- `Col`'s inner arrow is `=Recursive>`, because `first` is written with
  `zip` and `unzip` and the prelude's `zip` ties a knot. The walk is
  structural and terminates; the label is conservative, not wrong. A
  `zip` folded Church-style — the trick the prelude's own `fold`
  comment describes — would drop it, and is worth doing the next time
  the prelude is opened.
- `unzip` and `nth` were simply missing from the list library and are
  now in the prelude; `split : Str Str ⇒ List(Str)` and `asFloat? : Str
  ⇒ (Float | Str)` are new implementation prims (58 → 60). There is no
  `lines`: a newline is a separator like any other, and one spelling per
  thing.
- `count` is `len`. A frame *is* its rows, so the list word already is
  the aggregation, and a second spelling would have been a second name
  for one morphism. `column` is the one place the file does add a
  second name — `[f] rows ; column` is `map` — and it earns it by being
  written in the model's words (`embed` then run), so that the two
  denoting the same function is `embed`'s defining equation rather than
  a coincidence.

## Amendment (2026-09-15): `table` — a CSV header is a presentation

`examples/frame.braid` shipped on 2026-09-14 with a hand-written loader:
a `data Trade` declaration whose fields repeated the CSV's header, six
helper defs, and a comment promising that part 3 would emit exactly that
text from the header. It does, and the declaration is one line:

```braid
table Trades = "examples/data/trades.csv"
```

**Why a new keyword and not `import`.** `import` already means one
thing — the inclusion of one module's declarations into another — and it
is a morphism of presentations: objects added, never merged. A table
*also* includes declarations, so half of `table` is an import. The other
half is not: it **generates a loader over DATA**, a program that reads
the file again at runtime, which no import does, and it reads the file
itself in order to write that program. Overloading `import` with "and
also, if the file is a CSV, invent a type and a reader for it" would
make one keyword mean two things and make the meaning depend on the
extension. Daniel's line: *`import` already means inclusion of
declarations; a table also generates a loader over data.* Two acts, two
words.

**What is Haskell and what is Braid.** The Haskell is exactly three
things, all at check time: resolve the path and **read the whole file**;
**sniff** the column types; **write Braid text**. That text is then
spliced in under the `table` line and checked like any other source.
Everything that *runs* is Braid — the generated `loadTrades` is
ordinary derived code, the same text the hand-written loader was, and
its helpers are ordinary defs. There is no elaboration-time IO anywhere
else, and the boundary is the one `import` already stands at: the
loader, before anything is checked. Invariant two — elaboration sees
only parsed declarations — is untouched.

**The sniffing rule, and why whole-file reading makes it honest.** A
column is `Int` if every cell in it is an Int literal; else `Float` if
every cell is a Float or an Int literal; else `Str`. That is a
three-point lattice and the answer is the join over the column. The
reason to state it as *every cell* rather than *the first row* or *a
sample* is that the file is right there: the loader reads all of it, so
the type it writes is a fact about the data rather than a guess that a
later row can falsify. A sniffer that peeked would have to be defended;
one that reads everything has nothing to defend. The same reading is why
a **blank cell is refused**, naming line and column: a blank is not a
value of `Int`, of `Float` or of `Str`, and the three honest answers —
guess, widen to `Str`, or refuse — are a lie, a silent type change, and
the truth.

**The schema form is one form.**

```braid
table Sector(ticker: Str, sector: Str, weight: Float) = "sectors.csv"
```

It writes the names *and* the types, positionally. There is no separate
rename form and no separate ascription form, because renaming a column
and giving it a type are the same act — naming it — and two forms would
be two spellings of one thing. It is also the fix every refusal names: a
header that is not a word after sanitizing, a header that collides with
a word in scope, two columns of one name. Under a schema every cell must
read at the type written, checked at the same pass; the arity must match
the header, because the form is positional.

The **sanitizing rule** for the bare form, stated once: each space, tab
and `-` in a header cell becomes `_`, and the first letter is
lowercased. What is left must be a word — a letter, then letters, digits
or `_`. `Ticker Name` becomes `ticker_Name`; `1st` becomes nothing
usable and is refused.

**The hidden half.** A table generates two public words, `loadTrades`
and `headerTrades`, and six helpers named `Trades@…` — seven when a
column is `Float`, since the reader that takes `40` as well as `40.0`
is only written when something needs it — the compiler's
spelling, refused in source by the same walk that keeps `I@slot` out of
it. So a table's insides are reachable only through its two words, and
the refusal names them.

**At stage 8 the check-time half becomes a word.** The Haskell here is a
`Str ⇒ Str` function that happens to do IO first: path to file contents
to Braid text. That is a declaration word of type `Str =Dict IO> Code`
in the sense stage 8 is building toward — a macro that may read the
world, run by the loader at the boundary, its output ordinary source.
When declaration words exist, `table` should stop being a keyword and
become one: the parsing, the sniff and the text generation are all
writable in the language, and the only thing the Haskell has that Braid
does not is the file read, which is what `=Dict IO>` is for. Recorded
as the intended demolition rather than as a maybe.

## Amendment (2026-09-15): probability is a model

`examples/prob.braid` is the third flagship, and the one that says what
the `theory`/`model` layer is *for*: it buys a distinction the language
cannot otherwise draw, and it buys it structurally.

### The Markov reading

A **Markov category** (Fritz, *A synthetic approach to Markov kernels…*,
2020; READING) is a symmetric monoidal category in which every object
carries a commutative comonoid — every wire can be **copied** and
**discarded** — subject to two axioms with opposite force:

- **discard is natural.** `f ; discard = discard` for every `f`. This is
  causality (semicartesian): a kernel has total mass 1, so throwing its
  output away is the same as never having run it.
- **copy is NOT natural.** `f ; copy ≠ copy ; (f ⊗ f)` in general. This
  is the whole of probability. Copying a sample gives two *equal*
  values; running the sampler twice gives two *independent* ones.

Braid's base is cartesian, where copy *is* natural — and that is not an
assumption here, it is a machine verdict: `examples/laws.braid` has
`sameCode` **prove** `dup ; f f = f ; dup` for an arbitrary word, which
is exactly the statement that the base category has no randomness in it.
So a model of the `Doctrine` whose hom-object is a stochastic map is a
Markov category, `use Enum` is the functor from the deterministic world
into it, and the two programs

```braid
def twoEqualE = use Enum ; half ; flip ; dup        # ONE flip, copied
def twoIndepE = use Enum ; twoBiases ; bothFlipE    # TWO flips
```

disagree because the model disagrees. Nothing in the file declares that
they should; `dup` is transported by the functor, `bothFlipE` is the
strength applied twice, and the disagreement *is* what the model is.
That is the point of drawing it structurally rather than by a convention
about what `flip` means: a reader who does not believe the thesis can
run the file, and a model with a wrong `compose` makes the doctrine's
laws fail before anything prints.

### The shape a generator has to take, and why

A hom-object is `k(a, b)`: **one object on each side**. There is no
`k(•, Bool)`, because `•` is not a wire and a constructor parameter is
applied to types. So a *distribution* — a morphism `I → B` in the
Markov category — has no direct spelling, and the honest move is to
write the **kernel** it is a family of:

```braid
flip      : • ⇒ k(Float, Bool)          # an ENTRY: a carrier out of nothing
uniform   : • ⇒ k(Int, Int)
condition : • ⇒ k(Pair(Bool, a), a)
```

The bias then arrives on the wire the kernel consumes, and it is
produced by an **ordinary base stage inside the transported scope** —
`half = (n -> 0.5)`, one wire in and one wire out, so the functor embeds
it like any other stage. Nothing special-cases a parameter, and the
alternative spellings are worse in ways worth recording: `flip : Float ⇒
k(•, Bool)` does not typecheck (no `k(•, _)`), and a slot taking the
Float *beside* a carrier would stop being an entry and so stop composing
under `use`. The stand-in for the monoidal unit is `Int`, ignored: every
program in the file starts with a stage that drops the incoming Int and
produces what it actually wanted, and `report` runs kernels at 0.

`report : k(Int, b) ⇒ d(b)` is the **exit**, and it is the 6b rule one
kind up: an exit whose *result* varies by model is a theory parameter,
and here the result is itself parameterized (`Weighted(b)`, `Draws(b)`,
`Reach(b)`), so the parameter is a **constructor** parameter `d(_)`.
That needed a one-line fix: `componentArrows` wrote two type arguments
for every constructor parameter, on the standing assumption that one is
always a hom-object, and refused any transformation over such a theory
with `Weighted(a0, a1) ⇒ Reach(a0, a1)`. The arity is written in the
declaration; it is read now.

### Three models, and the one that is not shipped

- **`Enum`** — `Kern(a, b) = Fn⟨a ⇒ Weighted(b)⟩`, the Kleisli category
  of the finite distribution monad. `embed` is the point mass,
  `compose` is bind with the weights multiplied, `first` is the
  strength. Exact: every weight in the file is a double, and the dyadic
  ones are exact doubles.
- **`Sampler`** — `Samp(a, b) = Fn⟨Rng a ⇒ Rng b⟩`, a seed threaded as
  a `resource` exactly as `metered.braid` threads Fuel. The generator is
  a 48-bit LCG written in Braid, so the model is **deterministic** and
  every count printed is the program's output rather than a report about
  a run of it. `report` draws 200 samples, threading one seed through
  all of them, and the frame library tallies them.
- **`Nondet`** — `Poss(a, b) = Fn⟨a ⇒ Reach(b)⟩`, the support and
  nothing else: the possibilistic Markov category, where a weight is a
  bit and `compose` is `flatMap`. It earns its place by showing that
  the copy/two-flips distinction survives with the numbers removed —
  `{HH, TT}` against `{HH, HT, TH, TT}`.

**`Density` is not shipped, and not because it is tedious.** A scoring
semantics weighs an outcome it is *given*, so its `flip` would be
`k(Pair(Float, Bool), Bool)` and not `k(Float, Bool)`. A slot has ONE
type for every model, so a density model is a model of a **different
theory** — and saying that is worth more than a third carrier that
repeats `Sampler`'s resource threading with `Weight` in place of `Rng`.

### What the transformations establish, and what they refuse

**Expectation is not a functor of this category, and the reason is
mathematics.** E[g(X)] ≠ g(E[X]) — the file prints E[X] = 1 and
E[X²] = 5/3 for X uniform on {0,1,2} — so expectation does not preserve
composition and `transformation Expect : Enum ⇒ anything` is not a thing
to declare. What expectation *is* a homomorphism of is the **convex
structure**, so the file declares a second, one-carrier theory for it:

```braid
theory Convex(m) = mix : m m ⇒ m ; sample : • ⇒ m ; other : • ⇒ m ; observe : m ⇒ Float
transformation Expect : Mixtures ⇒ Means = meanW
```

`mix` is the fair midpoint ½x + ½y and the laws are the barycentric
ones (idempotence, commutativity, mediality). All four squares are
decided at the theory's evidence. Putting `Expect` where it *is* a
homomorphism, and printing the counterexample where it is not, is the
whole of what this file has to say about expectation.

**`Sampler ⇒ Enum` has no component at all.** A sample is not a function
of the distribution, and the type system says so before the mathematics
does: a component must be generic in the hom-object's arguments, so it
can never apply the sampler. Writing the obvious wrong one — the point
mass at a draw from a fixed seed — typechecks and is refused at the
samples, on `compose`, because a fresh seed per factor is not the same
kernel as one seed threaded through the composite.

**`Support : Enum ⇒ Nondet` is a homomorphism and is still refused**,
and this is the pragmatics item. Forgetting the weights really is the
support functor from the distribution monad to the nonempty powerset;
every square but one is fine; the `first` square is not. Its result is
`k(p(a, c), p(b, c))` — the hom-object at a **pairing** — and the
doctrine's exit is `observe : k(Int, Int) ⇒ Int`, which does not fit it.
A second exit at the pairing cannot help: the square *that* exit would
itself need is fed by the theory's first entry, `sample : • ⇒ k(Int,
Int)`, whose object is `Int` and not a pair, so it does not even
typecheck. With no exit that fits, the two carriers are compared with
`eq?` — and they are closures, where `eq?` is syntactic.

The general statement, which is the standing limit and now sits in
MANUAL §14: **a transformation's component is generic in the
hom-object's arguments, so it can never RUN the carrier; a square
between two function-carrier models is therefore decidable only when the
normalizer proves it, which needs the component to pass the witness
through untouched.** `examples/transformations.braid`'s `Forget : Names
⇒ Funcs` drops a `Str` field and proves all five. A component that
*transforms* the witness — which is what forgetting a weight is — is out
of reach, at the pairing especially. Closing it wants either an exit
family indexed by the slot's result shape, or a second kind of evidence
slot (`sampleAt : • ⇒ k(p(Int, Int), p(Int, Int))`) that the square
generator picks by fit rather than by declaration order.

### What is NOT built

**Continuous distributions.** Everything is finitely supported: `Enum`
enumerates, `Nondet` lists. A Gaussian has no list, and the carrier
would be a density against a base measure — which is the `Density`
model above, a model of a different theory.

**Inference beyond enumeration and forward sampling.** `condition` is
rejection at weight 0 or 1 and `renorm` is Bayes' rule on the frame.
There is no importance sampling, no MCMC, no variable elimination. Those
are algorithms; this file is about what the category is.

**Disintegration as an arrow.** Cho & Jacobs' Bayesian inversion takes a
kernel `k(a, b)` and a prior and returns `k(b, a)`. In `Enum` the
operation is writable — enumerate the joint, group by the `b`
coordinate, renormalize inside each group — but the *arrow* is not: a
kernel must answer for **every** `b`, so the inverse needs a table keyed
by an arbitrary outcome type, and that needs an ordering or a hash,
which the language does not have (`eq?` is structural, `lt?` is Int).
The Monty Hall and sensor sections are disintegration at one point, done
with `condition` and `renorm` — the operation, without the arrow.

**No choice slot, again.** A row program that branches into two
different *kernels* cannot be written inside a `use` scope: transporting
a sum needs `ArrowChoice`'s `left` and the Doctrine has `first`. The
file sidesteps it the way `frame.braid`'s `keep` does — the deciding is
deterministic and rides the wire, the generator is composed
unconditionally — which is why `coinSndE` flips even when the coin will
be ignored, and why the Monty Hall tally has to SUM the two branches
that agree. This is the second flagship in a row to hit it; it is the
strongest case yet for a `left` slot in the Doctrine.

### Pragmatics, recorded

- **A program over the theory cannot be written once.** `over Prob`
  makes a template, but a template's body elaborates to a `use@` marker
  and `use Enum` is a *transport* scope, not a template instantiation —
  so `def tmpl = over Prob ; half ; flip ; dup` followed by `use Enum ;
  tmpl` is refused (`use@Enum takes no wire`). Every transported program
  and every hand-built category word is therefore written once **per
  model**: `bothFlipE`, `bothFlipS`, `bothFlipN` are three copies of one
  text. `examples/autodiff.braid` writes `poly` once because `Smooth` is
  not over the Doctrine. This is the largest single cost in the file and
  the clearest thing to fix next.
- **`over M` must be its own line.** `def f = over Enum ;` followed by a
  newline loses the scope for every line after the first — the words
  resolve as base primitives and the refusal is `Unknown primitive:
  embed`, which names the symptom and not the cause. `def f =` /
  `    over Enum` / … is the form that works.
- **Width bookkeeping is visible.** After `dup` the scope is running two
  wires, so the next stage must take two; after a k-word it is running
  one, whose object is a `Pair`, so the next stage must take one and
  `unPair` it. Two spellings of one decoder (`Bool Bool ⇒ Str` and
  `Pair(Bool, Bool) ⇒ Str`) is what that costs, and the file pays it by
  decoding outside the scope instead.
- **The frame library as a client, which is what it was built for.**
  `import "frame.braid"` brought `groupBy`, `sumF`, `keep`, `printFrame`
  and `Pair` in, and the import rule did its job: the demo did not run,
  the declarations did. Three frictions: (1) `Pair` had to come from
  there rather than be declared locally, which is right but only
  discoverable by hitting the clash; (2) `says` — three atoms —
  clashed, and the refusal named both files at once, which is the rule
  working exactly as designed and still the standing cost of having no
  namespacing: a library's every private helper is in your scope; (3) a tally is
  `groupBy` over two columns built by two `map`s over the same list,
  which is four traversals for one grouping — `groupBy` wants a
  key-function form beside the key-column one.
- **A refusal that misreports its cause.** The `first`-square message
  said *the theory declares no exit* about a theory declaring two. Fixed
  the same day, tested, and worth noting as a class: a message that
  names a **missing** thing must say missing-*for-what*, or it sends the
  reader to add what is already there.

## Amendment (2026-09-15): a model parameterized by a model

`examples/autodiff.braid` ended, from the day it was written, with a
paragraph saying what it could not do: differentiate twice. Nesting
forward mode inside itself needs `Fwd` to be a model of `Smooth(Dual(a))`
for **any** model of `Smooth(a)` — a model parameterized by a model —
and a `model` head named a declared type, not a model variable. It does
now:

```braid
data Dual(a) = a a

model Fwd(R : Smooth(a, g)) : Smooth(Dual(a), a) =
    add = Dual(x, dx) Dual(y, dy) -> (x y ; add) (dx dy ; add) ; Dual
    mul = Dual(x, dx) Dual(y, dy) -> (x y ; mul) ((x dy ; mul) (dx y ; mul) ; add) ; Dual
    lit = (c -> (c ; lit) (0.0 ; lit) ; Dual)
    …

def polyDD = use Fwd(Fwd(Floats)) ; poly
#   polyDD : Dual(Dual(Float)) =Fwd(Fwd(Floats))> Dual(Dual(Float))
```

**What it is.** Not one model: a **family**, a functor Mod(Smooth) →
Mod(Smooth). It is ML's higher-order functor, Kiselyov's interpreter
transformer, and the ring construction R ↦ R[ε]/ε², and the three are
the same thing said in three vocabularies. A model of a theory is a
functor out of the free category on the theory's generators; a family is
a map between such functors' *sources of definition*, one level up.

**The spelling is an application, and it is the name.** `use
Fwd(Floats)` applies the family and mints a model called `Fwd(Floats)`.
The alternative considered was a scope stack — `use Floats Fwd`, "a
parameterized model takes the nearest enclosing model of its parameter
theory" — and it was rejected on one decisive ground and two supporting
ones. Decisive: a `transformation` names a model, and `transformation
Value : Fwd(Floats) ⇒ Floats` has to be *writable*; only the applied
form is a name. Supporting: the receipt has to print the model that read
the template, and `=Fwd(Floats)>` is exactly the text you would write to
reproduce it; and iteration is unwritable in the stack form, where `use
Floats Fwd Fwd` would have to mean association the reader cannot see.
One spelling per thing, and this is the one.

**The receipt is the whole application, as one label.** `use
Fwd(Floats)` mints `Fwd(Floats)`, not `Fwd` and `Floats`. A receipt says
*which model read this code*; one model did; `Floats` never saw the
template. Grades are sets of labels and this contributes a singleton,
which is also why nesting reads `=Fwd(Fwd(Floats))>` and not two marks.

**The carrier is substitution, never a type-level function.** The
parameter clause binds a name to each of the argument's own theory
arguments — `R : Smooth(a, g)` — and the head writes its own in terms of
them. `Floats : Smooth(Float, Float)` gives `a := Float`, so the head
`Smooth(Dual(a), a)` reads `Smooth(Dual(Float), Float)`; `Fwd(Floats) :
Smooth(Dual(Float), Float)` gives `a := Dual(Float)` and the head reads
`Smooth(Dual(Dual(Float)), Dual(Float))`. Nothing is applied at the type
level; a name is replaced. `Dual(a)` is an ordinary parameterized `data`
declaration, and that is the whole type story.

**A family's slot bodies are templates over the parameter's theory.**
Inside a body every theory name is R's — the name of the slot being
defined included, because the slot is not in scope in its own body. That
is what makes `add = … add …` unambiguous with no self-reference rule to
learn, and it is why the bodies read as the arithmetic they are.
Mechanically it is the renaming that already existed: an ordinary
model's slot defs are wrapped in `use <itself>`, and a family member's
are wrapped in `use <its argument>`. Its **laws** are still wrapped in
`use <itself>`, because they are the theory's and are about this member.

**Laws are checked at each instantiation.** Checking them for the family
would need equality modulo the parameter theory's laws — "R's `add` is
associative, therefore `Fwd(R)`'s is" — and there is no such judgement
here. So every member runs the theory's laws on its own evidence, and a
false family is refused at its **first** instantiation, naming the
member, which names the family and the argument at once. The refusal
says why it is happening there.

### The two problems the example posed, and what they decided

**The zero tangent.** `Fwd`'s `lit` needs "the zero of R's carrier". The
two candidates were a new `zero : • ⇒ a` slot on `Smooth` (filled
trivially by `Floats` and `Rev`) and `0.0 ; lit`. `0.0 ; lit` wins, and
not on economy: the theory **already names its zero** and `law addUnit`
already pins it — `(sample (0.0 ; lit) ; add ; observe)` is `sample`. A
`zero` slot would be a second spelling of a thing the theory has, and at
`Fwd(Fwd(Floats))` the two spellings would have to be proved to agree
anyway. As written, `0.0 ; lit` at `Fwd(Floats)` *is* `Dual(0.0, 0.0)`,
which is the zero of the first-order duals, by construction.

**The `g` parameter.** `Fwd(R)`'s gradient type is R's **carrier**, not
R's `g`: the head is `Smooth(Dual(a), a)` and the `gradient` slot is the
projection `Dual(v, t) -> t`. At `Fwd(Floats)` that is `Float`, which is
what the hand-written model had, so nothing changed. At
`Fwd(Fwd(Floats))` it is `Dual(Float)` — a first derivative carrying its
own tangent, which is the second derivative. Nothing had to be asked of
R, which is the honest answer and a better one than expected: a tangent
lives in the carrier, so the exit for it is a projection and never a
computation.

**A third problem the example found on its own: `cos`.** `Fwd`'s `sin`
needs R's cosine. While `Fwd` was hand-written over `Float` it reached
the base word `fcos`; a family has no base words — the only vocabulary
it has is the theory's. So `Smooth` grew `cos : a ⇒ a`. The general
statement is worth keeping: **a theory closed under `Fwd` must be closed
under differentiation**, in the sense that every generator's derivative
is writable in the theory's own words. `exp` ↦ `exp`, `sin` ↦ `cos`,
`cos` ↦ `sin`·`neg`, and the ring operations are their own. That is a
real constraint on theories a family can be built over, and it was
invisible until the family was.

### The head, and the one construct it is a step toward

A model head is now a **sequence of clauses**, each after the name
optional:

```text
model NAME [ ( R : Theory(binders) ) ] : THEORY [ ( args ) ]
```

The record carries a third field, `inObjMap`, empty today: the **object
map** clause to come — `model FwdAD : Base(Float ↦ Dual)`, a functor
given on generators with a substitution on types. It rides beside the
theory's arguments rather than replacing them, so adding it moves
nothing that exists.

The general form the clauses collapse into: **a model is a presentation
interpreted in a category, given by an object map and an image for each
generator.** Today's three kinds are the three ways that reads:

| kind | object map | generator images |
|---|---|---|
| `model Opt : Base = dupInt = dup, …` | the **identity** | a table, partial — every generator it does not name maps to itself |
| a Doctrine model (`model Circuits : Arrow(Circuit)`) | the identity on base types, with `embed` total (every base program has an image) | the theory's slots, and `;` goes to `compose` |
| a parameterized model (`model Fwd(R : Smooth(a, g))`) | a type-level **substitution**, `a ↦ Dual(a)` | written over the **parameter's** words, not the base's |

A written object map is the first row's map made explicit, and when it
arrives all three are one declaration read three ways.

### What did not fall out

**`over Prob` is still not instantiable by `use Enum`.** The pragmatics
note above stands, and it is not this mechanism's to fix. Checked
directly: a template over a Doctrine theory *does* expand under `use M`
— its slot names resolve to `M@…` correctly — and is then **transported
a second time**, because `use M` on a Doctrine model both instantiates
the template and embeds every base stage. The expansion's own `embed`
and `compose` get embedded, and the refusal is a stack failure about
`Plain(•, b)`. Separating "instantiate" from "transport" is a second
knob on one header word, and the one-spelling rule says it needs a
better answer than a flag. It is still the largest single cost in
`prob.braid`.

**Kleisli, the other motivating example, does not type** — and the two
refusals name the same missing thing twice: a type constructor that can
be applied to a **variable** and applied **partially**.

- `data Kl(m(_), a, b) = Fn⟨a ⇒ m(b)⟩` → *Malformed type parameter
  list*. A `data` declaration's parameters are wires, stacks, widths and
  rows; a **constructor** parameter is a theory's alone. For the body to
  hold `m(b)` a type would need a *variable in head position*, and `Ty`
  has `TData String [SType]` — a name. That is type-level application,
  which is exactly what the substitution discipline above exists to
  avoid.
- `model Kleisli(M : Monad(m)) : Arrow(Kl(m))` → *theory `Arrow`
  declares 'k' as a type constructor of arity 2, so its argument must be
  a bare constructor name, not `Kl(m)`*. An `InstArg` at a constructor
  parameter is a name; there is no partial application to write.

A family whose carrier is `C(a)` for a **wire** parameter — the
dual-number construction — needs neither, which is why it is the one
that shipped. `Kleisli` is a decision about whether Braid gets a type
level with application in it, and this amendment deliberately does not
make it.

**One parameter only.** Two would give one slot name two meanings inside
a body, since a body is written in the parameter's vocabulary. The head
refuses a second and says that; qualified slot names (`R@add`) are the
obvious answer and are not worth their cost until something wants them.

## Amendment (2026-09-16): `in` and `with`

`over` and `use` are gone. The declaration layer has **two header
words**, and a def's grammar is

```text
def NAME [in T] [with M …] = body
```

`in` at most once, `with` a list, `in` before `with`, both **header
clauses** — left of the `=`, never in a body — and the body is a pure
spine.

### The four glyphs, one meaning each

The rename was forced by a rule that had been true of the glyphs and not
yet of the words:

| glyph | means | and nothing else |
|---|---|---|
| `;` | **COMPOSES** | not "separates", not "then declare" |
| `,` | **LISTS** the items of a declaration | bindings, components, arguments |
| `:` | **TYPES** a slot (`add : a a ⇒ a`) | not "is a member of" |
| `=` | **DEFINES** the body | never equality — equality in Braid is always a program |

Under that rule three heads were misspelled. `model Floats : Smooth(…)`
used `:` for membership; so did `transformation Value : A ⇒ B`; and a
`;` between two model bindings looked like a separator. All three now
read the same way:

```braid
theory Arrow(k(_, _)) in Doctrine = …
model Floats in Smooth(Float, Float) = …
model Fwd(Smooth(a, _)) in Smooth(Dual(a), a) = …
transformation Value in Fwd(Floats) ⇒ Floats = value, zeroTangent
def poly in Smooth = …
def polyD with Fwd(Floats) = poly
```

`table Trades = "…"` is unchanged: a table names a file, and that is a
definition.

### Membership against application

`in` says **what this def is** — a morphism of the category `T`
presents, written in `T`'s vocabulary. It applies nothing, writes no
wire and mints no label. `with` says **what is applied to the body** —
a model, a resource, a functor, a `Recursive` knot — and every `with`
mints its receipt exactly as `use` did.

That is the distinction `over`/`use` already drew; what the rename buys
is that the words now *say* it, and that one word never means two
things. `over` was a preposition doing a verb's job ("this def is over
Circuits" reads like "this def ranges over circuits"); `use` said
nothing about what was being used for what.

### Why header-only: a scope is not a stage

`use R ; body` took the rest of the enclosing scope as its body, which
made it look like a stage and put it in the same placement family as
`x y ->` and `...` (MANUAL §4). It is not one. A scope is a property of
the **definition**, not a step in the pipeline: it decides how every
stage is elaborated, and a thing that decides how the spine is read
cannot be a point in the spine. Two consequences fell out for free:

- `def f = 1 ; over Monoid ; op` had to be refused by a special rule
  ("`over` may only be a def's own header — the first thing in its
  body"). With the clause left of the `=` there is no such position to
  refuse, and the grammar says it.
- The block-body trap is gone. `def f = over Enum ;` followed by a
  newline silently lost the scope for every line after the first
  (design-macros.md, 2026-09-15). A header clause has no body to lose.

The one place `with` still stands on a line of its own is the **REPL**,
where a session has no `def` to hang it on and the rest of the session
*is* the body — which is what ML's `open` does.

A **quotation** is the other place a body is written, and it takes the
same clause introduced by the same `=`: `[with Fuel = dup ; *]`.
`traced.braid` and `metered.braid` turn on being able to reify a
program *as a scope elaborated it*, receipt and routing included, and
that program is not a whole def. A quotation declares nothing, so there
is no `in` there.

### Instantiate against transport, decided by `in`

The 2026-09-15 amendment ended with a finding it could not fix: a
template over a Doctrine theory *did* expand under `with M` and was then
**transported a second time**, because `with M` on a Doctrine model both
instantiated the template and embedded every base stage. The expansion's
own `embed` and `compose` got embedded and the refusal was a stack
failure about `Plain(•, b)`. That note said a flag would be the wrong
answer and the one-spelling rule wanted a better one.

`in` is the better one, and it is not a second knob — it is the clause
that was already there:

| the def | `with M` does | because |
|---|---|---|
| `def f in T with M = …`, T = M's theory | **instantiates**: slots resolve to M's words, the spine stays BASE composition | the body is already a morphism of `B[T]`, and a morphism of `B[T]` composes like the base |
| `def f with M = …`, no `in` | **transports**: stage ↦ `embed`, `;` ↦ `compose` | the body is a base program and M is the functor carrying it in |

Never both. So `prob.braid`'s three hand-copied `second`/`bothFlip`
words are writable once:

```braid
def second in Prob = (c -> (([swapP] ; embed) (c ; first) ; compose) ; _ ([swapP] ; embed) ; compose)
def secondE in Prob with Enum = second
```

and the mixed case `in K with K` — K's own words inline, base stages
transported around them — is allowed and means what it looks like.

**The pin.** The two readings are different programs with different
types, and both are legal:

```text
def a with Enum = half ; flip ; dup   # a0 =Enum Recursive> Pair(Bool, Bool)
def b in Enum   = flip ; dup          # • =Recursive> Kern(Float, Bool) Kern(Float, Bool)
```

`a` is the Markov copy — one flip, copied, HH and TT at ½. `b` is two
kernel *values* side by side, which is not a kernel at all. Nothing but
`in` tells them apart, which is the argument that it belongs in the
grammar rather than in a flag.

### `in Recursive` is refused, and what it would have been

```text
`Recursive` is applied, not lived in: write `with Recursive`; the
open-recursion body is `fix` by hand (MANUAL §8)
```

The walk-through, because the refusal is a design decision and not an
omission. `with Recursive` on a def `f` is exactly **`in B[f]` plus the
knot model**: `B[f]` is the base presentation extended by one generator
— `f` itself — so it is a one-slot theory *per def*, whose slot's type
is not written anywhere but inferred from the body's use of it. A def
written over that theory is an **open-recursion** body: it names `f`
and does not say what `f` is. `with Recursive` then applies the knot
model, the unique one that sends that generator to the fixed point of
the body — which is what `tieKnot` builds and what `fix` computes.

So `in Recursive` would be the open half alone: a body over a theory
with no name, waiting for a model nobody can write down. The honest
spelling of that today is `fix` by hand, which the prelude already has
and `examples/recursion.braid` already shows. If the one-slot theory
ever becomes writable — an inferred-slot theory, `theory Self(a) = self
: ?` — `in Recursive` becomes the thing to say, and the refusal names
it in advance.

### A family head without a name

`model Fwd(R : Smooth(a, g))` named its parameter `R`, and nothing ever
used the name. A family's bodies are written in **the theory's**
vocabulary, not in the parameter's — `add` inside `add`'s body is the
argument model's `add` because the slot being defined is not in scope in
its own body — and there is exactly one parameter, so there is nothing
to disambiguate. The head is now

```braid
model Fwd(Smooth(a, _)) in Smooth(Dual(a), a) = …
```

— the theory the argument must model, and a name for each of that
model's own arguments so the head can write its own, with `_` for a
binder the head does not use. `Fwd`'s `g` was such a binder from the day
it was written.

### The comma, and why it is unambiguous

`;` composes, so it never separates two bindings. A declaration's items
are separated by a **comma on one line** and by a **newline in a block**
— models, transformations and theories alike, one rule:

```braid
model Ints in Ring(Int) = add = +, mul = *
```

The body of a binding runs to the next **top-level** comma, and brackets
are balanced, so `mul = (x y -> x ; f ; y ; g)` is one binding whose
body composes twice and contains a comma-free parenthesis; a comma
inside `Dual(x, dx)` is inside a bracket and is not a separator. The
test the checker actually makes is a second **top-level `=`**: a
binding's image is a program and a program has no `=` in it, so a second
one at depth zero is two bindings run together. The message says so:

```text
`;` composes; separate bindings with `,` or a newline
```

Every model now has the inline form, not just a model of `Base` — `def`
has both forms and a model is a definition too.

### The receipt is `with@F`

It was `use@F`. A receipt is minted by a `with` clause and by nothing
else, and it is visible in reflected code (`traced.braid` prints
`with@Ticked >> dup >> "tick" pass …`), so leaving it spelled after a
retired word would have left exactly one mention of `use` in the
language — one the reader could not look up and could not write. One
spelling per thing. That example's printed line changed; nothing else
did.

### What it cost

Forty-one `in` sites across twelve example files, seven theory heads,
every `with` clause, the prelude's nine `Recursive` defs, ~230 test
mentions and ~290 doc mentions. The whole of it is spelling except the
four items above (instantiate-vs-transport, the quotation clause, the
comma refusal, the inline model body), and four printed lines changed —
three that quoted the retired syntax in a banner, and the receipt.

## Amendment (2026-09-16): reflected types

**TypeRep, in two halves.** Both halves are REFLECTION of things the
checker already knows, exposed as DATA in the language. Neither adds a
type-level anything: no type families, no type classes, no runtime type
passing. The whole design is one sentence — *the checker holds four
tables; let a program read them* — and everything below is a
consequence of taking that literally.

### Why not type families

The obvious shape for "compute a type from a type" is a type-level
function in the type system: `Cols(P(x, y)) = P(Cols x, Cols y)`. It is
the obvious shape and it is wrong here. A type family is
**non-injective**: from `Cols a ~ Cols b` you cannot conclude `a ~ b`,
so unification can no longer solve for a variable under one, and
principal types go with it. Haskell pays for this with a constraint
solver, deferred equalities and `TypeError` as a genre. Braid's whole
bet is that inference is a one-pass mechanical thing with no solver
behind it.

So the rule, stated once:

> A type-level function is an **ordinary Braid word on `TypeRep`
> values**, run at **elaboration**, producing a declaration or a
> program. It never enters unification.

That is strictly more expressive at the places it is wanted (the
function may branch, recurse, print, fail with a message) and strictly
less dangerous everywhere else (unification never sees it). What it
costs is that the function's result must be *pinned somewhere* — a
generated declaration, or code spliced by a `functor` — rather than
floating as an unsolved equality. That cost is the feature.

### B1 — reflected declarations (shipped)

```text
typeOfWord : Str      ⇒ (TypeRep | Str)
declOf     : Str      ⇒ (Decl | Str)
showType   : TypeRep  ⇒ Str
```

Three prims, all pure, all total with the checker's own message on the
miss track. `data TypeRep` mirrors `Ty`/`SType`/`EffRow`/`Arrow` in
seven alternatives (base, variable, declared type at argument stacks,
`Fn` around an arrow, sum, a stack's open end, arrow); `type StackRep =
List(TypeRep)`; `data Decl` is a `data`, a `type` or a `theory`.

Four decisions inside that shape, each with its reason.

1. **A stack is a list, and its open end is an item of the list.** The
   alternative was `Box(List(TypeRep) Sym)` — items beside a tail. It
   would have been purer and it would have cost a `Box` unroll at every
   read. A tail is last in a stack and nowhere else, which is a
   statable invariant, so the list won.
2. **Equality is `eq?` after `normalizeArrow`, and the words normalize
   before they answer.** Otherwise `eq?` compares variable *names*, and
   two identical schemes that were generalized in a different order
   compare false. This is the one rule a reader must carry: a rep you
   *built* compares; a rep you *assembled* does not.
3. **A scheme's rep is its arrow's.** Quantifiers become the named
   variables `a0`/`ρ0`/`σ0`/`ε0` the REPL already prints, so a rep needs
   no binder list, and the display the REPL shows and the display
   `showType` shows are the same function (`showArrowA`, alias folding
   included).
4. **The width tier has no rep.** A bundle exponent (`Intⁿ`) and
   `Fin(n)` ride the miss track. An `Exp` is a second sort — it is not a
   type — and a rep that flattened it would make two different types
   equal, which is the one thing a rep must never do. `:t` still prints
   them; `typeOfWord` says why it will not.

**What it cost the implementation.** One record, `RCtx` — environment,
`data` declarations, aliases, theories — threaded where `Env` alone
used to travel (`evalTerm`, `runBuiltin`, `ElabCtx`). That is the whole
of it: a reflection prim reads the prefix scope, and the prefix scope
is one thing, so it is one argument rather than four.

### The first deriving customer

`table Trades = "trades.csv"` already writes Braid text from a
declaration; that was the precedent. `cellsFor : Decl ⇒ Code` is the
same move made **in the language**: the prelude word that turns a
`data` with named fields into the `Code` of its row printer. Its
customer is `examples/frame.braid`, where `tradeCells` used to be a
hand-written line and is now derived, printing byte for byte what it
printed before.

**And it hit a gap, which is stage 8's.** Deriving at *elaboration* is
already possible — a `functor` is an ordinary pure `Code ⇒ Code` word
and may return anything, including code that ignores its input entirely
— but **every `with` mints a receipt**, so a derived `tradeCells` would
be `Trades =Cells> List(Str)` and no longer fit `embed`'s
`Fn⟨a ⇒ b⟩`. The receipt is right (a functor that leaves no receipt
cannot be audited) and the refusal is right (a label is part of the
type). What is missing is a **declaration form whose body is computed**
— a way to declare a def *from Code* without applying a scope to it.
Until it exists a derivation either pays a runtime `evalAs` against a
witness (what `frame.braid` does) or wears a label.

A smaller consequence, worth recording because it will recur: the
derived word must stay **pure**, so `cellsFor` is written as a fold over
the field names carrying the remaining types rather than as `zip` — the
prelude's `zip` ties a knot, and an `=Recursive>` printer does not fit
`Fn⟨a ⇒ b⟩` either. *Grades propagate into derived code*, and a
deriving word therefore has a grade budget.

### What is NOT admitted, on its own merits

**`∀a. a ⇒ TypeRep`.** Runtime type passing. It would kill the free
theorems — `∀a. a ⇒ a` stops being the identity the moment something
inside it can ask what `a` is — and it would make erasure a lie. It is
also **unwritable**: nothing above takes a *wire* and answers a type.
The inputs are a **name** (`typeOfWord`, `declOf`) and **code**
(`typeOfCode`, B2), both of them static. There is no atom to build such
a word out of, so the refusal needs no rule; it is a property of the
generator set.

**Rewriting triggered by the manifest of the def being elaborated.**
Impossible by construction, and worth saying because it is the first
thing anyone tries: elaboration *precedes* inference. When a `functor`
runs, the def it is rewriting has no type yet — the types available are
the **prefix scope's**, fixed before this definition. A functor can ask
what `dup` is and what `Trades` is; it cannot ask what the word it is
building is, because that is not a fact yet.

### The retired objections

Two objections parked this in 2026-09-09 and both have since been paid
off by other work, which is why the amendment is dated now rather than
then.

- *"`typeOfCode` could see `.recurse` and loop."* There is no
  `.recurse` atom. Since 5a½ `with Recursive` rewrites to a closed
  spine over `#fix`, so every def — recursive ones included — is a
  **closed spine** with a principal scheme per stage read off the prefix
  scope. Inferring a Code value's type is inferring an ordinary
  program's type.
- *"Reading a type at elaboration is reading a type that is still being
  computed."* Only if the type being read is the current def's, and it
  cannot be (above). Every other type in scope was settled by the time
  the current declaration was reached; that is what "prefix scope"
  means, and it is the same property that lets a `functor` be *run*
  while the module is still being checked.

### B2 — `typeOfCode`, and the bootstrap (shipped)

The second half is `typeOfCode : Code ⇒ (TypeRep | Str)` — the
principal scheme of a **Code value**, inferred in the prefix scope —
with `envOf : • ⇒ List(Box(Str TypeRep))` beside it and `:tc <prog>` in
the REPL. Its customers are in `examples/typerep.braid`.

**Diagram cuts.** `cuts : Code ⇒ List(Code)` splits a spine into its
connected components: atoms are nodes, wires are edges, and each atom's
arity is read off `typeOfCode` of the one-atom spine that calls it. The
walk keeps one component id per live wire and *merges* when an atom eats
two; a merge is one relabelling, which is why the whole state is one
record. `1 2 3 4 ; + _ _ ; _ *` comes back as `1 2 ; + ; _` and `3 4 ;
_ _ ; *` — two halves with no wire between them, and nothing in the
*text* said so; it is read off the wires. This is **analysis**, not
runtime parallelism. What it licenses is a reading: a component whose
grade is ∅ is **central** (interchange holds), so it may be reordered
against anything and run wherever; a component carrying a label may
not, because the label is the claim that its order is observable.

**A type-level function as a word.** `colsOf : TypeRep ⇒ TypeRep` is
the column store's object map, `P(x, y) ↦ P(Cols x, Cols y)` with
`t ↦ List(t)` at the base — the exact shape that would be a type family
elsewhere. It is an ordinary `with Recursive` word over `unTypeRep`, it
prints through `showType`, and unification never hears of it. What it
*cannot* do is turn its answer back into a `data` declaration — the
same missing door B1 hit, from the other side.

**The differential check.** `typeOfWord w` against `typeOfCode [w]`,
over every word in scope, pinned as a test over the prelude: **182
words have a rep, and all 182 agree — up to the effect tail.** That
qualification is the finding rather than a fudge. A prim's scheme is
written with a **closed** pure row (`arrPure`); an inferred scheme's row
is **open** (a fresh ε later constraints may fill). Those are different
claims — "pure, full stop" is stronger than "pure so far" — and every
user-facing renderer hides effect tails, so the display hides exactly
this. In the language the example reports both numbers; the pinned test
closes every tail on both sides and demands exact equality, which is the
comparison the display already makes. The one name that cannot be
compared at all is `#fix`, and for a good reason: since 2026-09-14 no
source can *name* it (`#` opens a comment), so there is nothing to
parse.

That differential check is the first rung of a longer ladder, and the
ladder is the reason any of this is worth building:

1. `typeOfWord w` = `typeOfCode [w]`, over the whole prelude, pinned as
   a test. *(the rung this stage ships)*
2. A Braid **checker** for a fragment of Braid, written on `TypeRep`,
   checked by the host checker.
3. The two run against each other over the corpus — the differential
   test at scale.
4. Self-application: the Braid checker checks itself, and the host's
   answer is the oracle.
5. Optionally, a switch: the host checker becomes one implementation of
   a specification written in the language it checks.

Nothing about steps 2–5 is promised here. What is claimed is that step
1 is the honest first rung and that the rep was designed to carry the
rest of the climb: it is structural, it is total on everything but the
width tier, it normalizes, and equality on it is `eq?`.

### What hurt, recorded

Two things, both worth remembering because neither is about types.

*A binder shadows a word, silently and correctly.* `cuts`'s inner
walk bound the eaten wires to a parameter named `cons`, and every later
`cons` in that body was the list rather than the constructor. The
refusal, when it came, was an arity mismatch three lines away. Nothing
is wrong with the rule — a parameter shadows a word exactly as it
shadows any other name, and that is what makes binders safe — but a
shadow of a *prelude constructor* is the one that reads as a typo
rather than as a binding.

*A grouped compound closes its open output.* `(f e ; ev)` in non-final
position is instantiated closed, and `ev`'s result stack is open, so
the group produced **no** wires and the stage silently shifted. The fix
is to put `f e ; ev` at the head of its own stage and bind the result —
which is what every prelude word that calls a quoted predicate already
does. Worth a line in §14 the next time that section is touched.

---

## Amendment (2026-09-16): hom-objects over stacks

*Decided and shipped in stage 7a. What follows is the reason a slot, a
parameter and a whole elaborator pass went away together, and what one
model kept.*

### Three warts, one cause

Reading `examples/circuits.braid`, `examples/frame.braid`,
`examples/reified.braid`, `examples/prob.braid` and
`examples/transformations.braid` side by side, three things were ugly
in exactly the same way:

1. **`data Pair(a, b) = a b`, declared in five files.** A product type
   in a language whose products are the stack. Nothing used it as data;
   it existed to be packed with.
2. **The Doctrine's second parameter, `p(_, _)`.** A constructor
   parameter whose only job was to let the doctrine *name* the pairing
   a model chose, so that `first : k(a, b) ⇒ k(p(a, c), p(b, c))` could
   be stated and three laws written about it. It also had to carry its
   own capitalized constructor words `P` and `unP` into a law's scope —
   a second mechanism, for one parameter.
3. **The routing pass.** A stage of `k` wires in and `j` out was
   elaborated to `embed [unP … ; stage ; P …]` and then whiskered by
   `first` once per wire riding above, with the widths read off each
   stage's own arrow in the prefix scope. Sixty-nine lines of
   `runTransport`, an arity read that no other pass needed, and four
   refusals about widths.

The cause is one sentence. **The stack is Braid's only product and it is
flat**; a `data` declaration is THE way a product goes on a wire, and
`Box(ρ)` is the anonymous case. The hom-object `k(a, b)` was the one
place in the language where products *nested*, because it named one
WIRE per side — so a three-wire stack had to become `Pair(a, Pair(b,
c))` and `first` had to unpack a level at a time.

Stage 5c½ parked the alternative as "a carrier over whole stacks is
representable (`TData` holds stacks) and would delete both the packing
and `first`", filed as *alternatives, not layers*. Flat products pick
that alternative.

### The decision

`theory Doctrine(k(..., ...))`, with two structure slots:

```braid
compose : k(a, b) k(b, c) ⇒ k(a, c)
embed   : Fn⟨a ⇒ b⟩ ⇒ k(a, b)
```

`a`, `b` and `c` are **stacks**. A theory's constructor parameter is now
kinded one argument at a time — `_` a wire, `...` a stack — so
`k(..., ...)` is the hom-object and `d(_)` is still the parameterized
exit `examples/prob.braid` wants. A `data` declaration may name several
stack parameters, `data Circuit(a..., b...)`, and the "a stack variable
sits in tail position" law moves from the parameter list to the body,
which is where it was always really enforced.

Transport is then: every stage becomes `embed [stage]`, whatever it
covers, and every `;` becomes `compose`. The base already makes each
stage cover the stack it is handed — that is what `_` and `...` are for
— so the base's own widths ride through the functor untouched. Nothing
reads an arity; nothing packs; nothing whiskers.

### Does the strength survive anywhere, and why

**Not in the Doctrine.** The question that decided it was whether
`embed [f ...]` is available to every model, `Circuits` included — a
circuit being a stateful box rather than a function. It is, and for a
reason that is not about the model at all: the whiskering happens in the
BASE, inside the quotation, *before* `embed` is applied. `embed` is
handed a program on a wider stack and has nothing to commute with. Every
model's `embed` is a function of a `Fn⟨ρ ⇒ σ⟩`, and `ρ` and `σ` are
whatever the stage was written at. So `first` is not needed by
`Circuits`, `Funcs`, `Frame`, `Reified`, `Sealed`, `Notes` or `Names` —
all seven lost it and none of them noticed.

**In `Prob`, yes — and it declares its own.** A base stage whiskers in
the base; a **generator** does not. `flip : • ⇒ k(Float, Bool)` is an
*entry*: a carrier at a fixed width, built by the model, not the image
of any base program. Nothing in the base can widen a carrier, and a
Markov category is exactly a theory whose generators are carriers —
`flip ⊗ flip` is the statement the whole file turns on. So `Prob`
declares the widening as an ordinary slot of its own:

```braid
under : k(a, b) =Recursive> k(c a, c b)
```

One wire `c` rides **under** the kernel's domain. There is no pairing in
that signature and nothing to unpack: over stacks the strength is
whiskering and whiskering is concatenation. `c` is a wire rather than a
stack because `c a` is spellable and `a c` is a splice. `under` is not a
doctrine slot, so it is available under `in Prob` and ignored by
transport — which is exactly how it was used before, through `second`
and `bothFlip`, except that `second` has no second spelling any more:
acting on the wire above one riding below IS `under`.

The honest general statement: **the Doctrine has no strength; a theory
whose generators are carriers declares one, and over stacks it needs no
pairing to say it.**

### What got deleted

- the slot `first`, the parameter `p(_, _)`, and the laws `firstFst`,
  `firstEmbed`, `firstCompose` (replaced by one, `embedWide`, which says
  `embed [f] ; embed [g] = embed [f ; g]` at a stage that is one wire in
  and two out and at one that whiskers)
- `instanceConWords` and the `P`/`unP` constructor-word mechanism
- `runTransport`'s arity read, packing, whiskering loop and width
  bookkeeping: 130 lines to 61
- four refusals — *takes no wire*, *leaves no wire*, *takes k wires but
  the scope is running w wide*, and *is not one wire in and one wire out
  … transports through `first`*. A stage that does not cover its stack
  now gets the base's own refusal, which is what it is; and a stage that
  takes no wire is simply legal, because `k(•, Int)` is a hom-object
  between stacks and `•` is a stack
- `data Pair` from five example files
- the level table's third row

### The `Frame` carrier, and a note worth keeping

`Col(ρ, σ)` is `Fn⟨List(Box(ρ)) =Recursive> List(Box(σ))⟩`: **one list of
boxed rows**, not a stack of lists. The distinction is the whole reason
the type is written that way — a stack of lists is the column store, and
it is *non-injective*: three columns of ten and ten columns of three are
the same stack of `Int` lists, so the width is not recoverable and the
type would be a lie. A `TypeRep` word could derive the column-store
representation from the row type later, which is where that belongs;
the carrier says the honest thing now.

### What it cost, recorded

Two prices, both paid in public.

*Two transformation squares stopped being proved.* `Forget : Names ⇒
Funcs` used to prove all five of its squares, because a hom-object that
pinned its `Fn⟨a ⇒ b⟩` to one wire per side gave the normalizer a closed
arity for the `ev` inside `compose`. Over stacks the witness is
`Fn⟨ρ ⇒ σ⟩` with `ρ` open, and `ev` of an open wire has no closed
arity — so `compose` and `observe` go to the theory's samples, which is
the same wall `Len` has always stood at. `embed` and `sample` still
prove. What would buy the other two back is a normalizer that reads a
stack's width from the type at the splice; that is a stage of its own,
and it is not this one.

*A logger cannot render a stack.* `examples/lifting.braid`'s `Notes`
logs its input with `toStr`, and `toStr` is a word about ONE WIRE.
Braid has no renderer for a whole stack — `dup` copies a wire, `pack`
wants a homogeneous bundle — so a logger over stacks logs the `Box`, and
a box renders as the one-alternative sum it is. The file's log line went
from `100 212` to `alt1(100) alt1(212)`, and the file says why. A `Show`
for stacks is the thing that would fix it; nothing in stage 7a ships one.

---

## Amendment (2026-09-16): widths in the rep

*Shipped with stage 7a's second half. The reflected-types amendment
above recorded that a bundle exponent and `Fin(n)` "ride the miss track,
with the reason". The reason is still right; the conclusion was not.*

### What was wrong with missing

A width is a **second sort** — an exponent is not a type — and a rep
that flattened `Aⁿ` into `A` would make two different types equal. That
argument says a width must not be *reflected as a type*. It does not say
it must not be reflected at all, and the difference matters: with `pack`,
`zipN`, `mapN`, `checkedAt`, `indicesN`, `at`, `weaken` and `unzipN` all
missing, `typeOfWord` was not total on the prelude, the differential
check (`typeOfWord w` = `typeOfCode [w]`) skipped them, and rung 2 of the
bootstrap — a Braid checker written on `TypeRep` — could not have typed
the very words that make bundles work.

### The design

Two alternatives join `TypeRep`, and neither is a wire-shaped lie:

```text
7  rep   List(TypeRep) WidthRep    a closed SEGMENT repeated a width
8  fin   WidthRep                  Fin(n), an index into such a bundle
```

`Aⁿ` is a **stack segment**, not a wire, so tag 7 stands in a `StackRep`
beside the open end (tag 5) and `wire?` says false for it — which keeps
`stackWidth` honest, since a repeated segment is no more a *known* number
of wires than an open tail is. `Fin(n)` genuinely is a wire, so tag 8 is
one.

The width itself is its own type:

```text
data WidthRep = (Int | Sym Int)     lit k | var n at offset k
```

The offset is not decoration: `weaken : Fin(n) ⇒ Fin(n+1)` is in the
prelude, so a rep without it would have to lie about `weaken` or drop it.
The checker's own `Exp` is exactly an offset plus an optional variable,
and the rep says that and nothing more.

### The rule

**Never flatten a variable width into a type.** A *concrete* width may
reflect expanded, because the checker expands it first — `sexp`
canonicalizes `Int³` into three real wires and there is no `SExp` left to
reflect, so a rep that shows three wires is not lossy, it is accurate. A
*variable* width comes back with its variable and its offset, or `a0ⁿ⁰`
and `a0ᵐ⁰` would be the same type, which is the one thing a rep must
never allow. Normalization needed nothing new: `normalizeArrow` has
renumbered width variables to `n0`, `n1`, … since they existed.

### What it bought

`showType` round-trips every prelude word: `typeOfWord "pack"` renders
`a0ⁿ⁰ ⇒ List(a0)`, byte for byte what `:t pack` prints, because the
display was always the REPL's own. The differential check over the
prelude went from **182 words to 210** — the exponent and index words
joined it, and they agree.

What is still not reflected is a `model`, a `transformation`, a
`functor` and a resource's routing: each needs a rep of its own, and
none of them is a function of the declaration alone.

---

## Amendment (2026-09-17): resources are models; routing by inference

"The manifest, stated once" wrote down four rows, one table, every
difference in the carrier column, and said a resource's functor is
`E ⊗ –` — Power & Robinson's state construction. The checker did not
agree: `resource` was `data` under another keyword, `with R` minted no
label, and the routing pass and the transport pass did the same job
twice in two vocabularies. Stage 7b makes the table true.

**A resource is a model of the Doctrine.** `resource R = Ty` generates
three declarations beside `R`/`unR` — the carrier
`data R@k(a..., b...) = Fn⟨R a ⇒ R b⟩`, the theory `R@t in Doctrine`
declaring `compose` and `embed` only, and `model R in R@t(R@k)` — in
the compiler's `@` namespace, visible through `:doc R`. The theory
declares two slots and not four because `observe` would have to *run* a
resource program, which needs a seed, and seeds are install-site only;
a generated `observe` would be `mempty`-conjuring by another name. The
happy consequence is that no inherited law runs, since every Doctrine
law names `observe` or `sample`.

**`with R` is transport, in FUSED form.** The fibre `K_R(Σ, Θ) =
C(R ⊗ Σ, R ⊗ Θ)` is representable — the hom-object is an object of the
base — so fibre composition *is* base composition of representatives
and `embed [s] ; compose` has a normal form, `_^k s ...`. That is
character for character what the routing pass already emitted. Running
the unfused transport would build and immediately destroy an `R@k`
wrapper at every stage, changing every reflected program. So the
routing pass is not deleted; it is **restated** as the fused evaluator
of the resource model, and what goes is the idea that routing is a
separate kind of scope. Everything the scope does that transport does
not — the claim assertion, the one-resource-op stage, the whole-scope
word, the two refusals — is the part that is about the carrier
**segment** rather than about the functor, and the segment is an
ordered object the grade cannot hold.

**The receipt is `with@R`, and it does NOT get a stage.** Every `with`
mints; a functor's receipt is prepended as a stage of its own, and a
resource scope's cannot be, because the scope already emits exactly one
stage — the claim `unR ; R` — and `examples/metered.braid` counts
stages by burning fuel. The receipt is composed into the claim's own
atom: `with@R ; unR ; R`, one stage, one unit, the label on it.

**Routing is INFERRED.** A def is routed for a resource when the scheme
of an atom in its body, alone in its stage, carries that resource as
its deepest wire on both sides; callers are routed transitively until
the wire meets an install site or a handler. `with R` stays as the
explicit, idempotent override.

**Invariant five, amended by one sentence.** *Routing may read the
schemes of callees in the prefix scope — fixed before the current def
is touched, as good as written, the same licence `typeOfCode` and the
5c½ strength routing use; it never reads the manifest of the def being
elaborated.* Elaboration still runs between parse and inference, and
what it reads is a finished table rather than the answer to the
question it is part of.

**One label mechanism.** Every label names a functor and the functor's
carrier is looked up from the label's own declaration: `Log`'s is
`Log ⊗ –`, `Notes`' is `Logged(ρ, σ)`, `Metered`'s is nothing, and
`IO`'s is `World ⊗ –` for an abstract linear `World` there is exactly
one of. The display fold reads the carrier off the **stack**, not off
the set — a carriered label's display position is its carrier's
position, because the carrier segment is ordered and the grade is not —
and `arrowBetween` subtracts the folded names from the sorted set
before appending them in carrier order, which also fixed a label and
its own carrier printing the name twice (`=R R>`).

Full note: `design-7b.md`.

---

## Amendment (2026-09-17): the object map, and one model head

Stage 7c. A model has always been *a presentation interpreted in a
category, given by an object map and an image for each generator* — and
until now Braid wrote only the images. The object map was there in
every kind of model, unwritten: the identity for a model of `Base`, the
theory's parameters instantiated at the arguments for a plain model,
the identity on base types for a Doctrine model, a substitution driven
by the parameter for a family. `inObjMap` had been a field of the
head's record since 2026-09-15, empty, with a comment saying the clause
could arrive without reshaping the head. It has arrived, and it did
not.

```braid
model Mod in Base(Int ↦ Mod7 via reduce) = + = addM, * = mulM, - = subM
```

**The map is a SUBSTITUTION.** `A := B`, applied structurally — under
`List`, under a data type's arguments, through an `Fn` arrow, along a
stack. Not a type-level function, and that is the whole argument for
this shape: substitution commutes with unification, so a transported
program has a principal type for exactly the reason the original did,
and there is nothing to solve. The same argument that made a family's
carrier a substitution (2026-09-15) makes this one one. The source is
therefore **nominal** and of arity zero: `List(a) ↦ …` at an unknown
`a` is a function, and is refused.

**The glyph is `↦`, and it is not `⇒`.** `⇒` is the arrow of every
written TYPE in Braid — a slot's signature, an `Fn`'s insides, a
transformation's hom-set. An object map is not a type; it is a function
on objects, and `↦` is the mathematician's spelling for exactly that.
The lexer already admitted it as an ordinary identity character and
nothing else in the language claims it, so one spelling per thing cost
nothing here.

**`via c` is the image of the LITERAL FAMILY.** This is the piece that
makes an object map a different construct from a bigger table rather
than a convenience. The literals of a base type are generators —
infinitely many of them, and not one of them is a word — so no table
can name them and the head must. Under `with Mod`, `3` is `3 ; reduce`.
The consequence is visible in `examples/modular.braid` §7: under a
floor-halving map, `p(x) = x² + 3x + 2` at 4 computes 16 + 4 + 1 and
not 30, because `3` is `⌊3/2⌋` and `2` is `⌊2/2⌋`. That is what a
functor on a presentation does, and a reader who expected a change of
representation learns the difference in one line.

For a **nominal** `A` there are no literals at all, and the honest
answer is not to make `via` optional. `c` is then the map on *values*,
which is what conjugation coerces with, and it is still what makes the
head a map rather than a claim about types with nothing behind it on
values. The constructor of a nominal `A` is a generator like any other:
it takes an image, or a conjugation, or a refusal.

**ANY WORD may appear in the table**, because `Base`'s generators are
every word in scope; each image is blessed once by the same `subsumes`,
at the generator's own arrow **with the substitution applied**. Images
here are PROGRAMS rather than single words, and the reason is the old
one read the other way: a model of `Base` with the identity map also
declares a `Code ⇒ Code` word and Code carries names, so its bindings
must be names. An object-mapped model declares **no such word** — its
action on a literal is not a rename and its action on a def is an
unfolding, and a rewrite table holds neither — so the constraint lifts
and the images are ordinary programs, inlined at each use and
re-inferred where they land.

**THE REFUSAL IS TYPE-DIRECTED**, and this is the part that makes the
construct usable at all. A word whose scheme does not mention `A`
passes through untouched: the functor is the identity off `A`, so
wiring goes to wiring with nothing to declare, and `print`, `eq?`,
`map` and every other polymorphic word are simply not the model's
business. A word that *does* mention `A` and has no image and no body
is refused BY NAME, where the scope is written, with the three fixes.
Two consequences fall out rather than being arranged: `with M` twice is
the identity the second time (after one pass no type mentions `A`), and
`with M` then `with N` for `N : B ↦ C` composes.

**TRANSITIVE UNFOLDING is the machinery beyond a table check**, and it
is why this is a stage rather than an afternoon. A def called under the
scope is not a generator with an image; it is a def, so the functor
enters it — `F(def) = F(body)` — and so on through everything it calls.
Each is minted once per def per model as a generated word `M@def`: a
CACHE, one word with one type however many times it is called, not an
inlining. `fix` transports as structure, because the walk enters
quotations and a functor of the doctrine preserves the fixpoint, so a
def written under `with Recursive` comes along with no case of its own.
The closure terminates because a def is not in scope in its own body
(5a½), which makes the call graph a DAG — the same invariant that pays
for `sameCode` and for inferred routing pays here.

**Retraction and conjugation.** `via c, r` declares `r : B ⇒ A` with
`c ; r = id_A`, and every generator the table does not name is then
DERIVED: one `r` per `A` input wire, one `c` per `A` output wire, read
off the generator's own arrow. A retraction makes the **empty table
total**, so `model Milli in Base(Meters ↦ Mm via toMm, toM) =` with no
bindings at all is a complete model and says something. What it does
not say: `r ; c` is only an idempotent unless `c` is an iso, so a
conjugated word sees `B` only through `c`'s image. The example prints a
program written over metres running over millimetres, and nothing in
between was written twice.

**Two laws, and the dialect line.** A declaration like this states laws
`Base` has no samples to run: the retraction, and `image = F(body)` for
an image given to a word that has a body. `sameCode` decides both where
it reaches — a proof in the free category, for every input — and where
it does not, the binding stands and the model is recorded as a
**DIALECT** in `:doc M`. This is not a new policy: it is the line
`examples/optimizer.braid` §2 has drawn since 2026-09-13 between an
optimizer (images provably equal to their generators) and a
reinterpretation. Refusing instead would rule out every image whose
truth is arithmetic, which is all of them — `reduce(x + y) = reduce x ⊕
reduce y` is true and `sameCode` treats `+` and `mod` as uninterpreted.
The verdict is recorded rather than assumed, which is the whole
difference between a claim you can audit and one you must trust.

**AN OBJECT MAP IS NOT A HOMOMORPHISM**, and the example says so twice
in one file. `model Mod in Base(Int ↦ Mod7 via reduce)` makes reduction
a functor on the *ambient presentation*: it types, it runs, and it says
nothing about rings. That `reduce` is a **ring** homomorphism is a
further and stronger claim, and `transformation Reduce in Ints ⇒ Mods`
is where it is made and audited square by square. The contrast is
floor-halving: a perfectly good object map — every generator it names
has an image at the substituted type — whose transformation is REFUSED
at the `add` square, because ⌊(7+7)/2⌋ = 7 and ⌊7/2⌋ + ⌊7/2⌋ = 6. Two
declarations, two questions, and the language keeps them apart.

### One model head

The second half of the stage is a statement rather than a feature, and
the parser was made to match it:

```text
model NAME [ ( PARAM ) ] in THEORY [ ( ARGS ) ] [ ( A ↦ B via c [, r] ) ] = BINDINGS
```

One required clause and three optional ones, read by one function
(`parseModelHead`) into one record (`Instance`). A model of `Base` is
now an `Instance` like every other — its theory is the ambient
presentation, its arguments are none — which retired the separate
tuple `BaseInstance` had been since stage 5b.

The two parenthesized clauses after the theory are told apart by
**CONTENT, not position**: a group containing `↦` is the object map.
There is nothing to disambiguate, because a type expression never
contains `↦`, and a reader never has to remember an order. That is the
same move the head made for the parameter clause in 2026-09-15 — the
clause is recognized by what it says, and every clause is optional.

The five kinds of model are then five **settings** of one declaration,
and `CONSTRUCTS.md` says so in a table: identity map + partial table
(`Base`), theory parameters at the arguments (plain), identity on base
types with `embed` total (Doctrine), substitution driven by the
parameter (family), substitution written down (object-mapped). A
`resource` is a sixth *reading* of the Doctrine row, not a sixth row.

**What is refused, and why.** An object map on a model of a theory:
such a model already maps objects, by instantiating its theory's
parameters at its own arguments, and a second map at a mapped type
would be a functor into a category whose objects nobody has named. It
may well mean something — a model of `Ring(Mod7)` *is* the image of a
model of `Ring(Int)` under an object map, and saying so in the head
rather than by writing two models is exactly the kind of compression
this stage is about — but nothing has asked for it, and a clause that
is accepted before anyone knows what it means is worse than one that is
refused by name. Recorded, refused, and the question stays open. A
model parameter on a model of `Base` is refused for a flatter reason:
`Base` has no theory for an argument to model.

### What stays open

One thing, and it is stage 8's: **`functor` is not folded into
`model`**. A `functor F = word` is a rewriting of the ambient
presentation in exactly the sense a model of `Base` is — the difference
is that its table is *computed*, by a `Code ⇒ Code` word, rather than
written. Folded in it would read

```braid
model Traced in Base = <a Code ⇒ Code image>
```

with a program where the table goes, and `:doc` saying which of the two
a given model is. The reason not to do it here is that a computed image
cannot be blessed by `subsumes` at a declaration — there is nothing to
bless until the word runs — so the fold would put two different
checking stories under one keyword, and deciding how that reads is a
stage's worth of work rather than a paragraph's. Everything else this
amendment names is shipped.

---

## Amendment (2026-09-17): the declaration layer — keywords are words

*Stage 8. Direction 3 was decided on 2026-08-29 and written down in one
bullet; this is what it cost to build, and the two places the bullet was
not specific enough.*

Stage 0's surface decision reads, verbatim:

> **Declaration layer, direction 3**: fixed name-first surface notation
> (`def name = body` and kin) over an eventually-open table of
> declaration words carrying a `=Dict>` manifest — the metalanguage is
> the language, one resource richer. Forth-style parsing words are ruled
> out permanently: they break uniform reading and the
> hygiene-by-representation story; post-parse Code functors only. The
> keyword-initial surface is kept *deliberately* — it marks "an act on
> the dictionary" vs a morphism, the phase distinction made visible.

It is built, and the surface did not change by one character. Every
existing example prints what it printed, save one that counts the words
in scope and now counts ten more.

### `Dict` holds the declarations, not the module

The bullet says "one resource richer" and does not say what the resource
carries. Two answers were available and the first is wrong.

The **`Module` record** was the obvious one: it is what a declaration
ends up in. It holds an `Env`, a `Scheme` and a `Term`, none of which
has a Braid rep — so handing one to a program would mean reflecting the
checker's own types, which is bootstrap rung 2 and not a declaration
layer. Worse, it would make `Dict` a thing a program could *read*,
and reading is not what a declaration word does.

So `Dict` holds **the declarations so far**: the defs with their
headers and source, the type lines, the theory/model/functor/
transformation blocks, the imports, the tables and the program lines the
declarations did not take. `Dict` is the **write** handle. The **read**
side already existed and is the reflection words — `declOf`,
`typeOfWord`, `envOf` read the four tables the checker holds, at the
point the word runs. Write and read are two constructs because they are
two directions, and neither wanted the other's rep.

**Discharge is structural, which is `World`'s argument made a second
time.** A handler is `seed ; … ; unwrap`, and both ends come from the
`data` machinery a `resource` line drives. `Dict` is declared by
nothing, so there is no `Dict` and no `unDict`, and the name may not be
taken by any keyword. The loader discharges it, because the loader is
the host.

### The grade decides what a declaration line is, not the first token

The bullet says the keyword marks the phase. It does — at the surface.
At the **other** place a declaration can now be written, a top-level
line of a program, there is no keyword to read, and the first attempt
read the line's tokens for a declaration word's name instead. That
fails at exactly the case the feature is for:

```braid
def declare = (n -> (n ; bodyFor) (n ; nameFor) ; defW)
[(acc n -> n ; declare ; acc)] 0 (1 2 3 ; pack) ; fold ; drop
```

The second line names `defW` nowhere. It is a declaration line because
`declare` is `=Dict>` and the grade propagates, and **the grade is the
only thing that knows**. That is what a manifest is for; the keyword is
the same mark written where an arrow cannot be read.

Three rules follow, each refused by name: such a line must be `• =Dict>
•` (it is lifted out of main and run above it, so it must leave main's
stack as it found it); it may not touch the world (it runs before main,
so its output would arrive before main's — and check-time file reading
is the loader's, which is what `importW` and `tableW` are); and it
lands **below** the module's written defs, because the dictionary a
compile-time word sees is the dictionary so far. The ordering rule,
again, unchanged.

### Nine of the ten are the keyword's only

`defW` is the one a program may call. The other nine declare things the
module's own defs are checked *against* — a theory, a model, a type —
and those are checked above the program that would declare them. Making
them callable means checking the module in more than one pass, and a
second pass is a stage's worth of work rather than a paragraph's. It is
refused by name, with that sentence.

`typeW : TypeRep Str =Dict> •` is the interesting one of the nine. The
2026-09-16 amendment recorded, twice, that a type-level function on
`TypeRep` "cannot turn its answer back into a `data` declaration — the
same missing door B1 hit, from the other side." The door now has a
word on it. It is bolted, and the bolt is a pass structure rather than
a missing construct.

### What the table bought, and what it cost

The scanner's ten keyword branches became ten **rows**: a keyword, a
word, how its line is collected, the shape of its body argument, and
whether it reads the world. A row is data. Adding a keyword adds no code
to the scanner, which is what "eventually-open" was asking for.

The argument shapes are **three and closed** — `Code`, `Str`,
`TypeRep`, all post-parse. That is not a limitation waiting to be
lifted: a fourth shape is a reader macro under another name, and the
bullet rules those out permanently. A keyword's word receives what the
parser already built, which is why a Braid file can be read without
being run.

The cost was one number. `examples/typerep.braid`'s differential check
counts the words in scope — 260 before, 270 now — because ten of them
are new. They have reps and they agree, which is the check doing its
job.
