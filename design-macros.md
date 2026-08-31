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
2. **Elaboration never performs IO.** A functor's arrow must be `⇒`,
   not `⇒!` — the io grade doing double duty as the phase distinction
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
   refactor-stable). The arrow's manifest (`=K>`, `⇒!`) is inference's
   *record* of what the elaborated code needs, propagating by
   unification. Rewriting is never triggered by inferred types.

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
  (`a ⇒ Fn⟨ρ ⇒ a ρ⟩`) and `apply` is its inverse. Ambient structure,
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
  interpretation all live here.
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
  effects (`=Fuel>`, `⇒!`); a functor that moves to a non-representable
  category shows up as different types (`Circuit(Int,Int)`); the cause
  is the `use` line, one line up. Only representable structure can be a
  label, because only it leaves a wire there is anything to fold.

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
