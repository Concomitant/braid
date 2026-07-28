# Control flow: open issues & the logic report

Working notes from the July 2026 control-flow sprint. Design is
ongoing; nothing here is settled unless marked shipped.

## Part 1 — Open issues

### 1. The frame question (the `_` tax) — TABLED, decides everything else

Every wire on the stack must be covered by some component of a tensor
stage. A point (`1`, `"neg"`, `[quote]` — anything `• ⇒ A`) therefore
cannot ride a `>>` onto a non-empty stack; it needs a frame: `_ [c] [a]
>> elif`, `1 ... >> +`. Same rule, same tax, two spellings (`_` = pass
what's below; `...` = pass the remainder).

The categorical sidebar established the sharp line: for a *consuming*
morphism the frame boundary is a real choice (what's consumed vs
passed), so explicitness buys footprint honesty. For a **point** the
frame is forced and information-free (whiskering `ρ ≅ ρ⊗• → ρ⊗A` hides
nothing — there is no input to mis-account). So "zero-input pushes
auto-frame" is a principled, non-slippery rule — the line is "no
inputs," not taste. Costs: `x >> 1` stops being caught as a mistake;
points stop being syntactically visible as points; and if Braid ever
grows real effects (premonoidal), *when* a push happens becomes
observable and the silent frame is no longer canonical.

**Decision on record**: constants stay exact for now (user, 2026-07-27).
Revisit trigger: if the `_` in vertical quoted ladders keeps chafing, or
if a second construct (beyond guards) starts paying the same tax.

### 2. The deferral boundary — elif cannot be a value without a quote

"Run this on one track only" *is* deferral. Deferral has exactly three
implementations: a quote `[g]`, a row arm `(a | g)`, parse-time capture.
The tensor is not one of them (juxtaposition holds nothing back), and
`forget >> [g]` fails differently (it *destroys* the in-flight sum —
verified). So for any elif-like word:

- **value** ⇒ the next stage is quoted: `t1 >> [t2] >> elif` — honest,
  first-class, pays `[]`;
- **no quote** ⇒ the word is parse-special (a connective).

We drafted the connective twice (guard-block parser; then/elif/otherwise
program-level words) and deleted both: no special guards. The words are
now ordinary prelude defs (see §4). This boundary is a theorem of the
design, not a TODO — record it, stop re-deriving it.

### 3. `case(…)` status — CONTESTED

Shipped: `case(b1,…,bn)` parse sugar ≡ nested `(b1 | (b2 | …) >> merge)
>> merge`; the coproduct eliminator with bare (unquoted) branches,
heterogeneous domains, one result type. The honest defense: it is to
anonymous sums what `list(…)` is to nil/cons and what generated
`foldName` is to a data type. The objection (user): it's a parser
special-case, "spits on the conventions." The value-level alternative
`eitherV = (s ha hb -> s >> (ha ... >> apply | hb ... >> apply) >>
merge)` typechecks and runs but **does not nest** (verified failure),
so it can't replace `case` at depth. Options: keep and bless; keep for
sums-of-depth-≥3 only (style rule); remove and accept merge-ladders.
Unresolved.

### 4. The idiom inventory — which control flow to reach for (all verified)

| idiom | shape | needs | best for |
|---|---|---|---|
| **bound-x railway** (winner) | `x -> … 89 x >> less >> ("A" \|) >?> … >!> "F"` | binder, Bool conds, railway ops | elif ladders; prettiest |
| sugar-free flat rows | `ok \| guard` / `merge` line pairs | nothing beyond core | same, operator-free |
| deferred peel | conds in miss slots, sum deepens, `case`/merge-ladder collapse | core (+`case`) | seeing the whole tree in the type |
| quoted words | `_ [c] [a] >> if / elif / otherwise` (+`ifRoute`/`elifRoute`) | prelude words (shipped) | guards as data; unbound subject |
| `\|\|` + `choose` | clause list, `[p] [a]` lanes | shipped | guard lists you build/filter/reorder |
| `cond` tree | `x >> negative ["neg"] [ … ] >> cond` | core | nested if-then-else, fully `_`-free |

Key discovery behind the winner: with the subject **bound**, conditions
are points and `Bool = (•|•)` tracks are empty, so row arms are points
riding **bare** (delay law) — no quotes, no `_`, no apply. Closure
kills argument-threading; only nesting or auto-framing kills
push-framing.

Uncommitted: pointful `ifP/elifP/otherwiseP` (`(c a -> c ... >> apply >>
verdict >> (a ... >> apply >> in1 | in2) >> merge)` etc.) — tested,
simpler than the stack versions, first guard needs no `_`; continuation
guards still do. Add if the quoted-word style sees use with bound
subjects.

### 5. Zero-absorption endgame

Absorption is now only `{>=>, >?>, >!>, ||}`. All three fishes
decompose (`t1 >> [t2] >> word`), and `||` is list sugar, so zero
absorption is *achievable* — every newline strictly `>>`. Kept for
terseness (decision: thin sugar stays). The bound-x railway leans on
`>?>` absorbing; going to zero would force `ok |`/`merge` spelling.
Revisit only with a concrete win.

### 6. Naming

`ok`/`miss` (= `in1`/`in2`) read well in flow position. `then/elif/
otherwise` are now claimed by the quoted-word combinators. The fishes
have no word names (`mapHit`/`orElse` drafts dropped). `merge` barely
appears in the final idioms; no alias needed. `hit/miss` as *track*
vocabulary is entrenched in docs — fine, but stop using it for value
names.

### 7. Monads & do-notation — TABLED

The flow-block insight: do-notation is the special case of a
connective-per-row block where every connective is `then`; the guard
ladder is the same block with `elif` rows (Alternative, not Monad —
no do-sugar produces it). Real open problem when resumed: bind
resolution without typeclasses — monomorphic blocks first; whether
principal types can select the monad structurally is the interesting
question.

### 8. Open row tails — hygiene issue

`in1/in2/not/ok/miss` carry open tails (`σ`). Encountered concretely:
`less >> not` failed to close against a 2-row Bool context in one
draft (`(• | • | σ) vs Str`); `assocL/assocR` are isos only up to
openness. Mostly harmless, occasionally bites. Consider: closed
variants, a tail-closing combinator, or checker-side finesse when a
closed row is demanded. Unexplored.

### 9. n-ary sum elimination

`eitherV` doesn't nest; `case(…)` is the only flat eliminator of a
deep sum. A value-level n-ary fold is blocked: heterogeneous branch
domains can't share a `List`, and nesting trips the same
scrutinee-vs-parameter issue that killed nested `eitherV`. If labeled
rows/records ever land, revisit (a record of handlers is the missing
type).

---

## Part 2 — Report: traditional logical connectives and Braid control flow

### The three tiers

Braid separates what classical notation conflates — a proposition, a
decision procedure, and a guarded action:

| tier | objects | connectives | character |
|---|---|---|---|
| **propositional** | `Bool = (•\|•)` values | `and, or, xor, implies, not` | total, computed, no control; both args evaluated (they're wires) |
| **routing** | routers `X ⇒ (X\|X)` / quoted `[p]` | `both, either, negate`; chains `>=>`, `>?>` | short-circuit; order matters; *this* is control |
| **execution** | actions on tracks | rows `(f\|g)`, `when, unless, cond, select` | runs code conditionally; merge law: arms agree on result |

The Bool tier's `implies = (a b -> a [b] [true] ... >> cond)` is honest
material implication `¬a ∨ b` — a truth table, not a control construct.

### Conjunction, disjunction, negation as *composition*

The router chains are the connectives-as-control:

- `p? >=> q?` — hit iff **p and q** (q runs only on p's hit: short-circuit ∧)
- `p? >?> q?` — miss iff **neither** (q runs only on p's miss: short-circuit ∨, first hit wins)
- `not = (miss | ok) >> merge` — the track swap (the sum braiding)

So *and is sequencing on the hit track; or is sequencing on the miss
track; not is the braiding.* An elif ladder is a disjunction of
conjunctions read straight off the wiring.

### The conditional `if a then b` — three distinct things

1. **Material implication** (proposition): `a b >> implies : Bool Bool ⇒
   Bool`. Total; no branch untaken; both sides already evaluated.
2. **Guarded execution** (control): `when` / the one-armed row
   `a >> (b |) >> merge : X ⇒ X` with `b : X ⇒ X`. The merge law forces
   the untaken branch to be *representable as identity* — "if a then b"
   as an action is only coherent when doing nothing is a valid outcome
   of the same type. (Classical logic never has to say this.)
3. **The implication object** (internal hom): `Fn⟨A ⇒ B⟩`. A value that
   *is* "a entails b". **Modus ponens is `apply : Fn⟨A ⇒ B⟩ A ⇒ B`** —
   the eliminator of implication, literally. `curry`/`uncurry` (task
   #15, pending) are the deduction theorem: `A B ⇒ C  ↔  A ⇒ Fn⟨B ⇒ C⟩`.
   Under Curry–Howard, Braid's quotation tier is its implication
   fragment; the `[]` that keeps annoying us in control flow is the
   proof-term of an implication introduction.

### Contraposition — verified, with an operational asterisk

Classically `a → b ≡ ¬b → ¬a`. In Braid, contraposition is
**not-conjugation, and it exchanges the two fishes**: verified
behaviorally (2026-07-28, full parity×sign grid) as the router-tier De
Morgan law:

```braid
(odd? >=> negative?) >> not   ≍   (odd? >> not) >?> (negative? >> not)
-- not(p ∧ q) = ¬p ∨ ¬q : a then-chain, negated, is an else-chain of negations
```

Both sides produce identical verdicts on all inputs. But they are
**different processes**: the left runs `negative?` only on odds; the
right runs it only on evens. Same denotation, different short-circuit
direction, different work, and — if predicates ever carry effects or
refine their payloads differently per track — different behavior. So in
Braid, contraposition is an *extensional* equivalence (of verdicts),
not an *intensional* one (of wiring). Classical logic can't see this
distinction; a wire language can't avoid it. This is the same
denotation/operation gap the spec already notes for `laws.braid` — a
checked law is a license to rewrite, and contraposition is exactly such
a license: the optimizer may flip a then-chain into an else-chain when
the cheap predicate is on the wrong side.

Direction matters intuitionistically: `(a→b) ⊢ (¬b→¬a)` is
constructive; the converse needs decidability. Braid routers are
decidable *by construction* — a router always lands in its sum, every
predicate is total — so the classical equivalence is licensed at the
verdict tier. (If a "predicate" is ever a non-total railway stage, only
the constructive direction survives.)

### De Morgan as future laws.braid entries

The verified pair, plus its dual (`not(p ∨ q) = ¬p ∧ ¬q` via `>?>`/`>=>`
swapped), belong in `examples/laws.braid` as operational laws — each one
a license: reorder guards, flip chains, push `not` through a ladder.
