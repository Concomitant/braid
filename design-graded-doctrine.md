# Design note: the graded Doctrine, and the choice slot

*Superseded in part, 2026-10-05: §3's estimate priced the written-union
route (Route W). The constraint route shipped instead — a juxtaposition
in a grade position lowers to the `⊆` constraints `infer (Seq …)` already
emits — so items 1, 2, 5 and 6 cost a day and item 3 did not arise. §1,
§2, §4 and §5 stand. See design-macros.md, "the graded Doctrine".*

*Planning pass, 2026-10-03. No language code was written for this note.
Every claim about current behaviour is marked `[REPL]` (verified in the
shipped checker, docker `haskell:9.4-slim`, commit `aa7f84f`) or
`[code]` (read out of `src/MiniConcatTypechecker.hs`). Nothing here is
decided until Daniel says so. §2 settles part one's design question and
§3 measures what building it costs; §5 does the same for the choice
slot. The recommendation in both cases is to build the cheap half and
leave the expensive half unbuilt until the solver work is scheduled on
its own.*

---

## 1. The hole, and what it is not

```
def loud with Circuits = dup ; * ; print ; 1
  error: Cannot unify effects: IO vs pure (the unlabelled side's
  manifest is written and fixed: write =IO> on that arrow, or keep
  this code label-free)                                        [REPL]
```

The Doctrine's `embed : Fn⟨a ⇒ b⟩ ⇒ k(a, b)` is written pure, so the
transport functor is undefined on every effectful morphism. Stated
categorically: `with M` is a functor out of `K_∅`, and the base is not
`K_∅`. The base is the total category `∫_L K_L` of design-7b.md §2,
and a functor out of a graded category either forgets the grade or
lands in a graded family.

**Effectful transport already works, and the hole is narrower than the
error suggests.** A carrier whose inner arrow is written at the grade
transports effectful code today, with no language change:

```braid
data IOArr(a..., b...) = Fn⟨a =IO> b⟩
theory IOA(k(..., ...)) in Doctrine =
    embed   : Fn⟨a =IO> b⟩ =IO> k(a, b)
    compose : k(a, b) k(b, c) =IO> k(a, c)
    observe : k(Int, Int) =IO> Int

def loud  with Loudly = dup ; * ; print ; 1   # Int =IO Loudly> Int
def quiet with Loudly = dup ; *               # Int =IO Loudly> Int
def run in Loudly = loud ; observe            # • =IO Loudly> Int
```

That file runs, prints `9` from the embedded `print`, and prints `1`
from `observe` `[REPL]`. So the grade's home is **already the carrier**,
and `examples/circuits.braid` already writes one: `data Circuit(a...,
b...) = Fn⟨Box(a) =Recursive> Box(b) Circuit(a, b)⟩` has a grade in the
carrier, written, and fixed at `Recursive`. What is missing is not a
place for the grade. It is **polymorphism in the grade that is already
there**, and the price of its absence is the second line above:
`quiet` is pure and prints `=IO>`, because the theory chose one grade
for all its programs.

---

## 2. Where the grade lives: (iv), which is (ii) seen from the carrier

### (i) On the receipt only is unsound, and the hole is at the carrier

`loud : Int =Circuits IO> Int` with the carrier type unchanged requires
`embed` to **discard** its argument's grade: `embed : Fn⟨a =ε> b⟩ ⇒
k(a, b)` with `ε` unconstrained and unrecorded. The receipt then rides
on the arrow `• → Circuit(Int, Int)`, which is the arrow of
**construction**, and construction performs no IO: the closure is
inert. Execution happens at the exit, `observe : k(Int, Int)
=Recursive> Int`, on a different arrow. A set-of-labels grade on the
first arrow says nothing about the second.

The soundness hole is therefore precise, and it is about carriers
rather than about receipts. For a grade `L`, `K_L(Σ, Θ) = C(E_L ⊗ Σ,
E_L ⊗ Θ)`. Forgetting `L` **drops `E_L` from the objects**. Three cases:

| label | carrier | is (i) sound for it |
|---|---|---|
| carrier-less (`Recursive`, a functor receipt) | none; the fibre is a marked copy of the base | yes. The hom-sets are equal, so nothing is in the object to lose, and the provenance of the construction is a true statement about what was constructed |
| a resource (`Log`) | a wire of type `Log`, written | moot. The carrier is in the type, so `embed` of a `=Log>` stage is `embed` of `Fn⟨Log a ⇒ Log b⟩` and lands at `k(Log a, Log b)`. The grade is in the type by being in the object, and transport works today |
| `IO` | `World`, carriered and **never written** | **no**. (i) drops `World`, and `World` is the one carrier whose disappearance is invisible, because 7b b2 made it a singleton the elaborator never writes |

So (i) is sound for exactly the carrier-less labels and unsound for
`IO`, which is the only carriered label the elaborator does not write.
That is not a coincidence: it is 7b's b2 shortcut read as an attack.

The refusal is not hypothetical. A slot's declared grade **bounds** the
model's body:

```
error: model Loudly: slot 'observe' is Arr2(Int, a0) =IO> a0 but
theory A2 declares Arr2(Int, Int) ⇒ Int (Cannot unify effects: IO
vs pure …)                                                     [REPL]
```

So under (i)'s erasure, a carrier holding an effectful step forces its
theory to declare `observe : k(Int, Int) =IO> Int`, and then **every**
model of that theory claims IO at its exit whether or not it does any.
Over-approximating every exit is sound, and useless. (i) is ruled out
twice: the honest version is not writable, and the writable version is
imprecise for all models forever.

### (iii) The resource precedent does not extend to `IO`

Resources already do put the grade in the carrier, by putting a **wire**
there: `data R@k(a..., b...) = Fn⟨R a ⇒ R b⟩`, a pure inner arrow with
an extra wire `[code: resCarrierLine]`. `IO` has the same shape on
paper, `World ⊗ –`, and is blocked by two things the design chose
deliberately.

`World` is unwritable. A user's `data Circuit` would have to read
`Fn⟨World Box(a) =Recursive> World Box(b) Circuit(a, b)⟩`, and `World`
lives in the compiler's `@` namespace precisely so that no source can
write it or discharge it (MANUAL §3, design-7b.md §4b). Admitting it
into a `data` body is admitting `unWorld`, which is the one door 7b
welded shut.

And the fusion is wrong for a non-representable carrier.
`representableAt` fires only when the carrier's body is `Fn⟨E ρ ⇒ E σ⟩`
with a **pure** arrow and `E` the model's own name `[code]`, and when
it fires `runTransport` collapses transport to the routing pass. That
is right for a resource, where routing *is* the evaluator. `Circuit` is
codata whose composition is `compC`; there is nothing to fuse it into.

(iii) also covers the wrong labels. Most labels are carrier-less, so
"put the grade's carrier in the carrier" has nothing to put for them.
It is the answer for resources, and resources already have it.

### (ii) and (iv) are one answer

`k(ε, a, b)` with `embed : Fn⟨a =ε> b⟩ ⇒ k(ε, a, b)` and `data
Circuit(ε, a..., b...) = Fn⟨Box(a) =ε> Box(b) Circuit(ε, a, b)⟩` are
the same design written from the theory's side and the carrier's side.
Both need one new thing, an **effect-kinded type parameter** on
`theory` and on `data`, and both then need a second new thing that §3
measures and that the lead's estimate did not name.

### What a `data` body admits today

Fixed labels only, closed, with no tail. The type parser reads
`TokEffArrow ls` to `Eff (S.fromList ls) Nothing` `[code:
parseTyElem/parseFn, line 4720]`, and `Nothing` is the tail. There is
no syntax for an open effect tail and no way to write one, so the
"already the answer" reading of (iv) is not available: a written `data`
body's inner grade is a constant.

**Recommendation: (iv).** The grade belongs in the carrier because the
carrier is where the deferred computation lives, and because the type
system already forces it there. `circuits.braid` is the existence
proof, and the change is to make its `=Recursive>` a parameter instead
of a constant.

---

## 3. What (iv) costs, measured

Not a day. The lead's estimate, "a signature change plus routing the
grade through transport", names the first of six subsystems.

**1. A sixth `TyParam` kind.** `data TyParam = PWire | PStack | PWidth
| PCon String [Bool] | PRow` is named on 107 lines `[code]`. `pName`,
`pKind` and every exhaustive match take one line each; the arity list
is the problem (next item).

**2. `PCon String [Bool]` becomes a richer kind list.** The `[Bool]`
says wire-or-stack per hom-object argument. An effect argument is a
third case, so `[Bool]` becomes `[ArgKind]` at 11 sites that read the
field `[code]`, including `goArgs`'s per-argument kind dispatch, the
arity-mismatch messages, and `checkBaseSpellings`' `isCar`.

**3. The join in a signature, which is the real cost.** `compose :
k(ε, a, b) k(ε', b, c) ⇒ k(ε ∪ ε', a, c)` needs `ε ∪ ε'` written in a
type. `EffRow = Eff { eLabels :: Set String, eTail :: Maybe EVar }` has
**one** tail `[code]`, and the note on `EffSub` already says why: "one
tail cannot name a union of several". So `EffRow` grows a set of tails,
and `unifyEff` (64 lines of equality-with-absorption `[code]`) becomes
unification in a semilattice with variables. That is ACI1 unification,
which is not unitary: there is no single most-general unifier, so the
principality proof that `solve` (52 lines) rests on does not carry
over. 137 sites mention the effect machinery `[code]`. This item alone
is the largest change to the type system since grades.

**4. `checkExtends` inverts its central decision.** `matchArrow`
ignores the effect on purpose, and says so: "The effect is not
compared: a grade is what a MODEL may do, and the doctrine does not
bound it" `[code]`. A graded Doctrine makes the effect part of what is
matched. `matchStack`'s `MatchSt` carries three maps (constructor,
wire, stack) and needs a fourth; `ConMap` maps names to names and an
effect argument is not a name. `checkExtends` is 54 lines, `transportOf`
106.

**5. The redeclaration sweep.** Eight hand-written Doctrine theories
(`Arrow` ×3, `Vault`, `Columns`, `Reflective`, `Lifting`, `Prob`,
`GLA`), their ten carriers, eleven models, and the resource generator
(`resTheoryDecl`/`resCarrierLine`/`resModelDecl`, which nine resource
declarations drive). `representableAt`'s `g == effPure` test must learn
the graded shape without starting to fuse a carrier that must not fuse.

**6. The Doctrine's five laws are written programs.** `leftId`,
`rightId`, `assoc`, `embedFunctor`, `embedWide` name `embed`,
`compose`, `observe` and `sample` in source text in the prelude
`[code]`. A graded `compose` changes their types, and they must still
type and still run.

### The cheap partial answer, for the record

A **theory-level** effect parameter, instantiated once per model:
`theory Arrow(ε, k(..., ...)) in Doctrine` with `model Circuits in
Arrow(pure, Circuit)` and `model Loud in Arrow(IO, IOCircuit)`. No join
is needed, because `compose`'s two arguments share the model's single
`ε` and `ε ∪ ε = ε`. Item 3 disappears, which is most of the cost.

It does not fix the stated hole. `def loud with Circuits` still fails,
because `Circuits` is the pure instance; the author writes `with Loud`
instead. What it buys over §1's hand-written file is one theory and one
set of laws instead of one per grade. Whether that is worth items 1, 2,
4, 5 and 6 is Daniel's call, and the honest answer is probably not.

### What to build instead, today

The refusal. `def loud with Circuits` reports *Cannot unify effects: IO
vs pure* with a hint that names the wrong fix, because the hint is the
generic one and the context is a transported scope. The fix it should
name is the theory's: this scope transports into a category whose
`embed` takes a pure program, so either the theory declares `embed` at
the grade, or the effect goes outside the scope. One refusal, no new
sort, and it is under a day.

---

## 4. The choice slot: what is true

**A row transports today.** The claim in `examples/frame.braid` and
`examples/prob.braid` that a sum "cannot transport" is false as a
typing claim:

```braid
def branchy with M3 = dup ; lt? ; (forget ; 1 | forget ; 2)
#   branchy : Int =M3> (Int | Int)                            [REPL]
def tagged  with M3 = dup ; lt?
#   tagged : Int =M3> (Int Int | Int Int)                     [REPL]
```

`embed` takes the whole stage, a row included, as one opaque function,
and the hom-object ranges over stacks so a sum is one wire like any
other. What is missing is not typing. It is that **the model gets no
handle on the branch**: `Enum` cannot branch into two different
kernels, so `coinSnd` flips a coin the program ignores, and `Circuits`
cannot route a tag through two sub-circuits that each keep their own
state.

**`left` is writable today, and so is the form a transport pass would
emit.** Both verified at commit `aa7f84f` `[REPL]`:

```braid
theory Ch(k(..., ...)) in Doctrine =
    embed : Fn⟨a ⇒ b⟩ ⇒ k(a, b)   compose : k(a, b) k(b, c) ⇒ k(a, c)
    left  : k(a, b) ⇒ k((a | c), (b | c))   observe : k(Int, Int) ⇒ Int

def leftA   = (f -> [( f ... ; unArr4 ... ; ev ; alt1 | alt2 ) ; merge] ; Arr4)
def swapRow = (alt2 | alt1) ; merge
#   leftA   : Arr4(ρ0, ρ1) ⇒ Arr4((ρ0 | ρ2), (ρ1 | ρ2 | σ0))
#   swapRow : (ρ0 | ρ1) ⇒ (ρ1 | ρ0 | σ0)
```

An extra slot does not disturb `with`: `def easy with Chose = dup ; *`
is `Int =Chose> Int`, `left` being neither an exit nor an entry
`[REPL]`.

### Doctrine-optional, and the argument is the refusal

Sums are a **program form** of the base, like `;` and juxtaposition.
The Doctrine owns `;` through `compose` and gets the tensor for free
from the hom-object over stacks. A row is the third form, and it is the
one the Doctrine has nothing to say about, so `left` belongs beside
`compose` and `embed`.

`under` is not the precedent it looks like. `Prob` declares `under :
k(a, b) ⇒ k(c a, c b)` because its carrier needs a whiskering that its
point-mass `embed` does not supply; 7a **deleted** the strength from
the Doctrine because the base's own `...` supplies it there. `under` is
the precedent for a model-specific structure, not for a base program
form being a theory's business.

The decisive argument is the refusal. Per-theory, `with M` on a theory
with no `left` must still refuse a row, and the refusal must name the
fix, and the fix is a name the theory does not have. A refusal that
names the fix puts `left` in the Doctrine whether or not the slot is.

### One slot, and `embed` is a prerequisite

One slot suffices. The row symmetry is base-expressible, `swapRow`
above, so `right f = swapRow ; left f ; swapRow`. For `(f | g)` at one
row the pass emits four stages:

```
left F ; _ [swapRow] ; _ embed ; compose ; _ (left G) ; compose
        ; _ [swapRow] ; _ embed ; compose
```

and the hand-written form types `[REPL]`. For a row with k tracks it is
k applications of `left` and k rotations, the rotation being the
k-cycle built from `there`/`altN`.

**`left` therefore presupposes `embed`**, because the rotations are
base programs that have to be embedded. Two consequences the lead's
scope did not have. The level table gains a **sub-row under `+ embed`**
rather than a row of its own, since there is no `compose + left` level.
And a reader-transported theory cannot have `left` at all: the
rotations are not in its generator table, so `GLA`/`Dense` is out by
construction, as it is out of `embed`.

One wrinkle to record. `alt1`, `alt2` and `there` are open-row
injections and `merge` cannot close a row, so the emitted form's result
row carries a residual the author did not write: `branchHand : • ⇒
Arr4((Int | Int), (Int | Int | σ0))` `[REPL]`. A written closed
expectation still unifies, `σ0 := RNil`, but the displayed type of a
transported row changes.

### The laws are run, not proved or sampled

A theory's laws are generated defs that `runLaw` executes at module
start, and anything but `true` is a module error `[code]`. There is no
prove/sample verdict for them; that vocabulary belongs to
`transformation` squares, where `tsqWhy` records why a square was not
sampled `[code]`. So the three choice laws (`left` of `embed` is
`embed` of `(f | id)`; `left` distributes over `compose`; the
coproduct's unit) join the existing five as runnable checks, stated the
way those five are, funnelled down to `k(Int, Int)` through
`embed [alt1]` and `embed [merge]` so that `observe` can see them. A
declared `transformation` over a theory with `left` gains one more
square, and that square is where prove-or-sample applies.

---

## 5. What the choice slot costs

Not a day either, and the expensive item is again the second one.

1. **The slot, detected.** `transportOf` reads `left` off its declared
   arrow as it reads `compose` and `embed`, `Transport` gains a
   `tpLeft`, `tpTransports` is untouched. Small.
2. **The transport pass must decompose a row stage.** `runTransport`
   takes each stage opaquely in 60 lines. Routing a row structurally
   means recursing into each arm (an arm is bare code, so it is a
   spine), transporting each, and interleaving the rotations. It is a
   third elaboration mode beside the stage-wise and atom-wise ones, and
   harder than either, because it is the only recursive one. Budget it
   against `readTransport`, 115 lines, and expect more: it needs its
   own refusal class for an arm the model cannot carry, and it must
   leave the opaque path intact for models that declare no `left`.
3. **Three model fills.** `Funcs` is `leftA` above. `Frame` is a row
   program over `List(Box(a))` where the boxed row is a sum of stacks.
   `Enum` re-tags each outcome of a `Weighted` list and returns `dirac`
   on the right track. None is a one-liner.
4. **Two flagship rewrites, with output changes.** `frame.braid` gets
   `filter : row ⇒ (row | •)` under `with Frame`, and `keep` stays for
   the mask form. Prefer `filter` when the predicate is a row program
   and `keep` when the mask is already a column, which is what
   `bigOnes` has. `prob.braid`'s `montyE` branches on `car = 0` and
   flips only on the left track, so §7's tally stops summing two
   branches that agree and the printed distribution changes shape. That
   is a deliberate output change in a 900-line example, and every line
   of it has to be listed.

**`left` does not give `Frame` a filter on its own.** `left f` at
`Col` is `Fn⟨List(Box((a | c))) ⇒ List(Box((b | c)))⟩`, a list of the
same length. Dropping rows changes the length, which is not what
ArrowChoice provides; the collapse `k(a, (b | •)) ⇒ k(a, b)` is an
`ArrowZero`/`ArrowPlus` structure, or a `mapMaybe`. So item 4's
`filter` is `embed`-plus-`left` for the deciding and a frame-level
collapse for the dropping, and the collapse needs a fourth slot nobody
has scoped. `frame.braid`'s comment is wrong about the cause and right
about the conclusion: `keep` is what the Doctrine can express.

**Recommendation.** Build items 1 and 3 and nothing else, as a
`left`-declaring theory and model in one example, with the laws and the
hand-written emission form. That is a day, it is honest, and it makes
the slot's shape reviewable before the recursive transport mode is
written. Leave item 2 and the two flagship rewrites for a scheduled
pass, and fix `frame.braid`'s and `prob.braid`'s comments to say "the
transport pass does not emit it" rather than "it cannot transport",
which is what is true.
