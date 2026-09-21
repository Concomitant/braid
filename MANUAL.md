# The Braid Manual

A reference for every language feature. Types shown are the checker's
actual output (`:t`), not paraphrases. Companion docs:
`guide-open-arity.md` (width-polymorphic words), `design-*.md` (why
each feature is the way it is), `examples/` (everything running).

---

## 1. Running Braid

```sh
# prebuilt binary (GitHub Releases): a file runs it, no file = the REPL
./braid examples/registrar.braid
./braid

# or the repo script, no install — same interface, toolchain in a
# container (drop the file for the REPL, `-` to read stdin)
./braid examples/registrar.braid
```

REPL commands: `:t <prog>` type · `:t! <prog>` raw (no alias folding) ·
`:tc <prog>` the type of the `Code` it leaves (§12) ·
`:doc <name>` doc comment · `:defs` whole prelude with types ·
`:transformations` every declared transformation, with the verdict on
each of its squares · `:s` show stack · `:clear` reset stack · `:q` quit. Every REPL line runs
against a **persistent typed stack**; a line whose input doesn't match
the current stack is rejected with a message naming the stack.

## 2. Lexical structure

| syntax | meaning |
|---|---|
| `# …` | comment to end of line |
| `## …` | doc comment — binds to the next `def`/`type`/`data`; shown by `:doc` |
| `17`, `-4` | Int literal (a constant: `• ⇒ Int`) |
| `"text"` | Str literal (escapes: `\"` `\\` `\n`) |
| `.name` | Sym literal (interned symbol) |
| `>>` , `;` , newline | composition — all three are the same operator |
| `>>>` | compose, opening the previous stage's remainder (`a >>> b ≡ a pass >> b`) |
| `...` (or `…`) | the explicit remainder (§4); must be the final atom of its stage |
| `---` | the row tail (§5): the last alternative of a sum or a code row, and the fifth parameter kind |
| `[` `]` | quotation |
| `(` `)` | grouping / rows / type arguments / binders |
| `\|` | row separator (rows / sum types) |
| `,` | separator in type arguments |
| `->` | binder arrow |
| `>=>` `>?>` `>!>` | railway operators (§7) |
| `^` | exponent in type position (`Int^3`); superscripts `Int³`, `ℝⁿ` also lex |
| `⟨` `⟩` `⇒` | `Fn` type brackets and arrow (type position): `Fn⟨Σ ⇒ Θ⟩` |
| `•` , `one` | the empty stack, in **type** position; the identity on it, in **term** position *(2026-09-20)*. Two spellings, one thing, in both positions — the display is `•` for the type and `one` for the word (§5, §9) |
| `=IO>` , `⇒!` , `->!` | the io manifest label on an arrow (§3); the last two are legacy spellings |
| `=Recursive>` , `=IO Recursive>` | any written label set, in any order — displayed sorted (§3) |
| `=Log>` , `=IO Log Counter>` | display only: an arrow threading resource wires, manifest included (§3, §8) |
| `=Traced>` | a scope's receipt: minted by `with Traced` — or by `with IntSum`, or any other `with` — never written (§3, §12) |
| `=Circuits>` | a transporting model's receipt: the same, with a CARRIER the display folds (§3, §8) |
| `import "f.braid"` | include another file's declarations (§8) |
| `table T = "f.csv"` | a CSV's header declares a type: the row type, its header word and its loader (§8) |

Identifiers are any run of characters not in the punctuation set —
`odd?`, `f'`, `+`, `*` are all ordinary names. Blank lines collapse.

**A newline is a strict `>>`.** Two things absorb one:

- the railway operators `>=>`/`>?>`/`>!>` — composition a newline cannot
  itself express, so the operator wins;
- a **bracket delimiter, on its inner side**: a break just after `(`/`[`
  or just before `)`/`]`. A bracket is an explicit scope, so a break
  against its edge is layout, not a stage boundary — this is what lets a
  wide atom wrap.

There is no line-continuation for `>>` or `|`, and a newline *between*
stages inside a bracket is still `>>`:

```braid
(               # break at the edge: layout
1 2             # ⇒ Int Int — ONE tensor stage
)
(1              # break between stages: composition
1 ... >> +)     # ⇒ Int — this is 1 >> (1 ... >> +)
```

Rows stay line-scoped everywhere (§6): `f |` ⏎ `| g` is two rows, not
one collided `| |`, which is what makes aligned track-columns work.

## 3. The model

A Braid program denotes a morphism in a cartesian category drawn as a
string diagram: the **stack is a product of wires**, `>>` is
composition, juxtaposition is the tensor.

**Everything exact.** Constants are maps from nothing (`1 : • ⇒ Int`);
operations consume exactly their inputs (`+ : Int Int ⇒ Int`). Nothing
has an implicit remainder — this is what keeps inference principal.

A **tensor stage** is a juxtaposition of atoms, aligned with wires left
to right (leftmost atom takes the deepest wires):

```braid
1 2         # • ⇒ Int Int          two constants side by side
2 id        # a ⇒ Int a            push a 2 beside an existing wire
1 +         # NOT increment: 1 ⊗ + = • Int Int ⇒ Int Int — strict tensor
1 ... >> +  # increment — the remainder says where the other wire comes from
```

Each atom in a stage covers exactly its own wires; every incoming wire
must be covered by some atom. `1 2 >> +` works (two made, two used);
`1 >> +` is a type error (one made, two needed).

**Every arrow carries a manifest** — a set of labels. A pure arrow
prints `⇒`; an arrow carrying labels prints them between `=` and `>`,
sorted, and the labels ride on the arrow just as resource names do.
`IO` is one label among them, minted by the four prims that touch the
world; a functor scope mints its own (below, and §12).

```braid
1 >> print                  # • =IO> •          composition propagates it
def shout = toStr >> print  # a0 =IO> •         inferred through defs
def quiet = toStr >> drop   # a0 ⇒ •            pure stays bare
[print]                     # • ⇒ Fn⟨a0 =IO> •⟩ pushing an action is pure
[print] 5 >> ev          # • =IO> •          ev transfers it out
[dup >> *] 5 >> ev       # • ⇒ Int           same ev, pure quote
```

Manifests are **inferred, never annotated**: four prims are marked io
(`print`, `readLine`, `readFile`, `writeFile` — §9) and
every other arrow's grade follows from composition. Higher-order words
(`ev`, `loop`, `map`, `foldExp`, `mapN`) share the grade of the
quotation they run, so one `ev` serves pure and effectful quotes
alike.

**Composition JOINS.** A grade is a *set* of labels, and `Σ =L> Θ`
followed by `Θ =M> Ξ` is `Σ =L∪M> Ξ`. The empty set is the bottom and
is contained in everything, so a pure stage sits beside any other and
contributes nothing; and because `∪` is commutative, `pure ; io` and
`io ; pure` have the same manifest (execution order is still left to
right — that is a fact about running, not about grading). The
consequence worth stating on its own: **a part is never asked for the
composite's labels.** `loop` may recurse, so `loop` is `=Recursive>`; the
quotation it runs is not, and a written pure `Fn⟨Int ⇒ (Int | Int)⟩`
goes straight into it.

Inference states the join as a `⊆` constraint and takes its least
solution, and a scheme carries whichever of those constraints survive
(that is how `loop` passes an io body's grade out to its caller without
demanding it). Like effect tails, **constraints never display** — not
in `:t`, not in `:t!`, not in `:defs`. Both of those render an arrow,
and a constraint relates two tails the arrow does not show; there is
nothing a reader could write in response to `ε3 ⊆ ε7`. What you see
instead is the effect it has: the labels that reached the arrow. Effect tails are invisible in display, the same hiding a `ρ`
tail already gets inside `Fn⟨…⟩`. Writing a grade in a type: §5 and
§8. The two edges: §14. A label set is **writable** wherever a type is
written — `=IO>`, `=Recursive>`, `=IO Recursive>`, in any order, displayed sorted;
the older `⇒!` and `->!` spellings still lex for old source and mean
`=IO>`.

**A threaded resource folds onto the arrow too.** A resource (§8) is
a nominal wire you thread rather than consume; resource wires ride
**deepest**, and when both sides of an arrow begin with the same run of
them, that run moves onto the arrow — which is exactly what "threaded
through" means. The io grade rides on the same arrow, because it says
the same kind of thing:

```text
note  : Str =Log> •                       -- Str in, Log threaded
bump  : • =Counter> •
score : Int ρ0 =Log Counter> Int ρ0       -- two resources, in `with` order
peek  : • =IO Log> •                      -- grade and resources, one arrow
```

The fold is display, not inference: it fires when the prefixes match
exactly, and a resource anywhere but the bottom prints as an ordinary
wire (`_ bump ... : a0 Counter ρ0 ⇒ a0 Counter ρ0`). Threading them by
hand is `_`/`...` as usual; `with` (§6) writes that padding for you.

*Amendment (2026-09-17): **a resource really is minted now.*** Until
stage 7b the table below said `R` was *minted by `with R`* and it was
not: the `=R>` was the display fold alone, and it fired with no `with`
in sight. It is minted now — a routed scope puts `R` on the manifest of
everything it elaborated, exactly as every other `with` does — and the
receipt rides **inside the claim's own stage** (`with@R ; unR ; R`)
rather than in a stage of its own, so a scope still elaborates to the
number of stages it always did. The fold stays **prefix-driven**: it
reads the carrier off the stack, subtracts the folded names from the
sorted label set and appends them in **carrier order**, which is why
`=Log Counter>` is in `with` order rather than alphabetical and why a
label and a resource of the same name print the name once. A resource
that is threaded by hand still folds with no label present — the label
is a *consistency* requirement where it appears, never a precondition.

What the mint buys is the **error**. A written pure expectation meeting
routed code used to complain about a wire the user never wrote
(*Cannot unify stacks: Log Int vs Int*); it now says
*Cannot unify effects: Log vs pure*, and either shape carries the hint
that names the fix — **you forgot to install** (§14).

*And `IO` stops being an exception in the statement.* Every label names
a functor, and the functor's carrier is looked up from the label's own
declaration: a resource's is `R ⊗ –`, a carrier-less label's is the
identity on homs, and `IO`'s is `World ⊗ –` for an **abstract, linear
`World`**. That is the whole change — the table above has no exceptional
row any more, and nothing else moves. There is exactly **one** `World`
and it is ambient, so every representative in the fibre is determined,
the whiskering map is the **identity**, the elaborator never writes the
wire, and the four io prims stay marked. It is Clean's `*World` and
GHC's `State# RealWorld` with the wire erased because it is a singleton.
Discharge is impossible **structurally** rather than by a check: a
handler is `seed ; … ; unwrap`, and those come from the `data` machinery
a resource declaration drives — `World` is declared by none, so there is
no `World` and no `unWorld` to write one with, and the name it does have
is in the compiler's `@` namespace. `print : a0 =IO> •`, unchanged.

**And a `with` that changes anything leaves a receipt.** A scope (§6,
§12) elaborates the code under it — rewriting it, routing it, renaming
it — and mints its own name onto the manifest of what it elaborated, so
the arrow records not only what a word touches but what built it, and
every caller inherits the label by composition. **A receipt says "this
scope CHANGED this code", not "this scope was applied to it"**
*(2026-09-18)* — the stronger reading, and the useful one for auditing,
since code a scope left alone has nothing to audit:

```text
poly    : Int =Traced> Int          -- elaborated under `with Traced`
caller  : Int =Traced> Int          -- calls poly; the receipt travels
report  : Int =IO Traced> •         -- and unions with any other label
total   : Intⁿ⁰ =IntSum> Int        -- and a MODEL mints too: which
                                    --   model read this template
```

Only a `with` mints, and a `with` mints exactly when its action left
the code different from the code it was given — image membership, the
law the functor notes already state for an idempotent F (`F(p) = p` ⟺
p is in F's image). So a functor that finds nothing to rewrite, a model
whose slot names do not occur, and a `with Recursive` on a body that
never names the def all mint nothing. `in` (§6, §8) declares
what a def *is* rather than applying anything to it, so it mints
nothing either. The label is not written, cannot be written
(`with@Traced` in your own source is an error), and does not have to be
threaded — which is what makes it evidence rather than a comment. It
is also part of the type: a declaration that says `Fn⟨Int ⇒ Int⟩`
refuses instrumented code exactly as it refuses io (§12, §14).

**And recursion leaves one too — `Recursive`** (2026-09-09; a scope
name since 2026-09-14). `Recursive` says *may recurse without bound*,
not *diverges*: it records that the word went through the one operator
that can iterate forever, which is a fact about provenance and not a
termination proof. A definition is not in scope in its own body unless
its header says `with Recursive` (§8), and that scope is what mints the
label — like every other scope, through a receipt:

```text
fac    : Int =Recursive> Int              -- written under `with Recursive`
loop   : Fn⟨ρ0 ⇒ (ρ0 | ρ1)⟩ ρ0 =Recursive> ρ1     -- the LOOP recurses, not the body
while  : Fn⟨ρ0 ⇒ (ρ1 | ρ2)⟩ Fn⟨ρ1 ⇒ ρ0⟩ ρ0 =Recursive> ρ2
fold   : Fn⟨a0 a1 ⇒ a0⟩ a0 List(a1) ⇒ a0    -- a structural recursor: bare
map    : Fn⟨a0 ⇒ a1⟩ List(a0) ⇒ List(a1)    -- derived from it: bare
report : Int =IO Recursive> •             -- unions like any other label
```

The generated structural recursors (`foldList`, `foldTree`, `foldNat`,
§8) descend on a smaller value and mint nothing, so the whole derived
library — `fold`, `map`, `filter`, `reverse`, `append`, `concat` —
stays bare. The reading that buys: **an unlabelled word ties no knot,
and therefore terminates by construction.** Two honest edges on that
sentence: it is *run-time* code it speaks about — a functor word runs
in the other phase, where a step budget rather than `Recursive` is the bound
(§8) — and "knot-free ⟹ terminates" rests on the primitive set holding
no other unbounded construct, which is believed and has not been
audited end to end. It had a third until 2026-09-18, and that one was
a real hole rather than a caveat: a `data` declaration naming itself to
the **left of an arrow** made the typed Z combinator writable, so
general recursion typed **pure**. Such a declaration is now refused
(§5, §14), and there is exactly one door.

**And a MODEL WITH A CARRIER is a label with a carrier**
*(2026-09-13)*. When a model's theory is declared `in Doctrine` and
takes the doctrine's composition and embedding (§8), `with` of
that model is the functor that sends every stage of a scope to the
model's embedding and every `;` to its composition. `with Circuits`
mints `Circuits` exactly as any functor scope does — nothing on the
arrow is new — and what the label *adds to the objects* is the
hom-object `Circuit(a, b)`. At the base a transported word is
`• ⇒ Circuit(Int, Int)` carrying `Circuits`, and the display folds the
carrier onto the glyph, which is the same move that folds a threaded
resource:

```text
easy     : Int =Circuits Recursive> Int   -- one carrier, out of `•`, carrying the label
pair     : • =Circuits Recursive> Circuit(Int, Int) Circuit(Int, Int)
```

**The fold wants exactly one carrier.** `pair` above is two words of
the category side by side outside the scope: well-typed, and visibly
*not* composition in it — so it prints unfolded, and you can see the
two circuits. Composition is written under the clause (`def f with Circuits =
f ; g`). Like the resource fold this is display, not inference, and
like the resource fold it does not run backwards: a *written*
`Fn⟨Int =Circuits> Int⟩` means the labelled arrow it looks like, and the
carrier form is written out (`Fn⟨• =Circuits> Circuit(Int, Int)⟩`).

The built-in labels, then:

| label | minted by | carrier | says |
|---|---|---|---|
| `IO` | the four io prims (`print`, `readLine`, `readFile`, `writeFile`) | an abstract, linear `World` — one of it, ambient, never written | touched the world |
| `Recursive` | `with Recursive` on a `def` **that names itself** (§8) | none | ties a knot, and may recurse without bound |
| `F` (any functor) | `with F` on a `functor` (§12) | none | its graph morphism was extended along the wiring |
| `R` (any resource) | `with R` on a `model R in Doctrine` (§8), **or inferred routing** | a wire of type `R` | threads the `R` wire |
| `M` (any model with a carrier) | `with M` on a `model` whose theory has a hom-object (§8) | the hom-object `K(a, b)` | was built in the category `M` presents |
| `F(M)` (a family applied) | `with F(M)` on a `model F(T(a))` (§8) | the member's own carrier | was read by the model `F(M)` |

One mechanism, six readings; union along composition for all of them,
and every difference is in the carrier column — `IO` included since
2026-09-17, which is what took the last exception out of this table. An applied family mints
**one** label, the whole application: one model read the template, and
its argument never saw it.

## 4. The remainder discipline

Three spellings of "and the rest passes through":

| form | passes | example |
|---|---|---|
| `_` | exactly one wire | `_ 10 ; div` — divide by 10 |
| `...` | the whole rest, **threaded on top; the stage's pushes go to the bottom** | `1 ... >> +` increment; `[+] 0 ... >> foldExp` |
| `>>>` | opens the previous stage | `a >>> b` |

`_` is also `id` (the section hole: `2 _ >> *` is double, `_ 2 >> -` is
subtract-2). `...` must be the final atom of its stage. Because `X ...`
pushes X *underneath*, ending successive lines with `...` accumulates a
pile bottom-up — the `decide` ladder exploits this (§11).

**Lines that wrap** *(2026-09-14)*. A newline is a strict `>>`, which
until today meant a stage had to fit on one line. Three spellings say
"not yet". A line that **ends** with `;`/`>>` and a line that **begins**
with one are both legal and both compose with their neighbour — the
operator is redundant with the newline, which is exactly why writing it
reads well when a pipeline is carried down the page (both were errors
before, `Expected a tensor stage, got: TokSeq`, so no file changes
meaning). And a line ending in `\` drops the newline outright, so the
**tensor stage itself** wraps:

```braid
def dmul = Dual(a, da) Dual(b, db) -> (a b ; fmul) \
    ((a db ; fmul) (da b ; fmul) ; fadd) ; Dual

    (r -> r ; close?
       ; ((s t -> x) | (s t -> x (r ; step) ; fsub ; newton))
       ; merge)
```

`\` is the one continuation form because it is the only thing that is
stage-final where `|`, `...` and `---` are not, it is unwritable in a
program today, and indentation cannot be made to mean this: every
multi-line def body is indented deeper than its `def` line and relies on
newline = `>>`. Two refusals: a `\` that is not the last thing on its
line, and a `\` with no line after it. A `;` carried onto the next line
composes at `>>`, which binds **tighter** than `|` — so it continues the
last *arm* of a row, and a `| ---` residual still has to end its own
line. The rule is lexical: `\` and the redundant `;` are gone before the
parser runs, and `|`-led continuation lines are untouched.

**Placement rules** (one family, one logic — the open thing must come
last so the runtime segment can be its witness):
- an open-arity word must be the final atom of its stage (§13);
- an open binder (`x ... -> …`) must be the final atom of its stage;
- `...` must be the final atom of its stage;
- the naming binder `-> x y z` ends the stage it follows, and its body
  is the rest of the scope.

The header clauses are **not** in that family *(2026-09-16)*: `in` and
`with` are written left of a def's `=` and never appear in a spine, so
nothing in the body has to end for them (§6, §8). A scope is not a
stage.

## 5. Types

Inferred, principal, never annotated. Five variable sorts, four of
them visible:

| sort | display | ranges over |
|---|---|---|
| type | `a0, a1…` | one wire's element type |
| stack | `ρ0…` | a stack segment (always a tail) |
| row | `σ0…` | the tail of a sum's alternative list |
| exponent | `n0…` (shown superscript: `Intⁿ⁰`) | a width (unary natural) |
| effect | never displayed | the tail of an arrow's grade (§3) |

Type formers:

- **Base**: `Int`, `Float`, `Str`, `Sym`.

  **`Float`** *(2026-09-14)* is an IEEE double, and it is a base type
  **beside** `Int` rather than above it. There is no numeric tower and
  no overloading: `+ - * div mod lt?` are Int words, `fadd fsub fmul
  fdiv flt?` are Float words, and **no word is shared**. A mixed stage
  is a type error that names both vocabularies and the two crossings,
  `toFloat : Int ⇒ Float` and `floor : Float ⇒ Int`, which are written
  where you mean them. The whole word list is §9; `fneg` and `fabs` are
  prelude defs (§10).

  A **literal** is digits, a point, digits — `2.0`, `0.5`, `-2.5`. The
  point is the whole notation: `1e-3` is refused where it is written
  (*write the decimal point form*), because `-` cannot be an identifier
  character — it heads `->`, `---` and every negative literal — so an
  exponent form would need a lexer case of its own for a notation the
  display never prints back. A literal needs a leading digit: `.5` is a
  symbol, as it always was.

  **The display convention, pinned**: the **shortest decimal that reads
  back as the same double**, never in exponent notation, always with a
  point. So every finite Float prints as a Float literal and re-reads as
  itself, and `(0.1 0.2 ; fadd) ; print` prints
  `0.30000000000000004` — the seventeen digits that are true rather than
  the three that are convenient. The three non-finite doubles print
  `NaN`, `Infinity`, `-Infinity`; they are values, not literals, and
  splicing one into `Code` is refused.

  **`eq?` on Floats is structural**, which at `Float` means IEEE `==`:
  bit equality up to the one identification IEEE makes (`0.0` and
  `-0.0`) and the one it refuses (`NaN` equals nothing, itself
  included). It is not an epsilon comparison and will not become one —
  `(0.1 0.2 ; fadd) 0.3 ; eq?` is **false**, and that is the truth about
  the two doubles. Write your own tolerance test with `fabs` and `flt?`
  when you want one (`examples/autodiff.braid` does).
- **`•`** — the empty stack; the terminal object. Constants are points
  `• ⇒ A`; `forget : ρ ⇒ •` is the unique map to it.

  **It has a name, and the name is `one`** *(2026-09-20)*. `one : • ⇒ •`
  is the identity on the terminal object (§9), and `one` is also `•`'s
  **ASCII spelling in type position**, so `Fn(one -> a)` and
  `Fn⟨• ⇒ a⟩` are the same written type. `•` is the second spelling in
  **term** position, and it dies at the parse: `[•]` and `[one]` are one
  term, and `reflect`/`unparse` print `one`. Two ways to type it, one
  spelling per thing — exactly as `->` is typed and `⇒` is displayed.
  The type displays `•` and the word displays `one`; neither ever
  displays the other.

  **"One" means ONE INHABITANT, not one wire.** `•` is ZERO wires and
  one value, and that value is the empty stack. It is not the empty
  type: Braid has no initial object and no empty sum, so `none`,
  `nothing` and `empty` would each have named a thing the language does
  not have.

  What `one` is FOR is pinning. `pass : ρ0 ⇒ ρ0` is the same morphism
  at every width and therefore constrains nothing, so `[pass]` cannot
  stand where `[one] : • ⇒ Fn⟨• ⇒ •⟩` is wanted — a quotation whose own
  type says *nothing in, nothing out*. Before today that quotation was
  writable only as `[1 ; drop]`: two atoms, with an Int allocated in
  order to be discarded.

  Where it pins is where a quotation's type is unified. In a **tensor
  stage** it takes no wires and so constrains nothing — `dup one` is
  still `a0 ⇒ a0 a0` — and `one ...` is the identity on any stack,
  `ρ0 ⇒ ρ0`. But a bare `; one ;` in a spine **asserts the stack is
  empty**: there are no implicit remainders, so `1 ; one` is refused
  with *Cannot unify stacks: Int vs •*, which is the `1 ; 2` refusal
  and not a rule of its own (§4, §14).

  **Rendering a stack is a word, not a class** *(2026-09-17)*.
  `showStack : ρ0 ⇒ Str` (§9) takes the whole segment and returns the
  wires deepest-first, space separated, each one as `toStr` renders it
  — the REPL's own `:s` printer, said once. It is a **renderer, not a
  class**: there is no hook, no dispatch and no way to make a declared
  type print differently through it, and the same is true of `toStr`.
  A `Show` doctrine, if there is ever one, is a `theory` with a model
  per type and it is not this. `showStack` consumes and is open-tailed on
  `forget`'s convention — the whole segment as the final atom of its
  stage, the empty segment anywhere else — so nothing new was needed
  for it. A binder aims it at part of a stack (`dup ; _ (b -> b ;
  unBox ; showStack)`), which is what `examples/lifting.braid` logs
  with.
- **Products** are juxtaposition: `Int Str` is two wires. There is no
  *built-in* pair type — the stack is the pair — but you can declare
  one (`data Pair(a, b) = (a b)`), and `Box(...)` carries a whole stack
  as a single wire, which is how multi-wire aggregates go inside a
  `List` (§8). **Products stay flat**: since 2026-09-16 not even the
  Doctrine's hom-object nests them (§8).
- **Sums**: `(Δ₁ | … | Δₙ [| σ])` — one wire carrying alternative
  *stacks*. Rigid nesting: `(A | (B | C))` never flattens.
  `Bool = (• | •)`, `Maybe(...) = (... | •)` are prelude aliases.
  **`Maybe` is payload-FIRST**, unlike Haskell's `Nothing | Just a`.
  That order is arbitrary in Haskell but load-bearing here: `alt1` is the
  track `ok` builds and `>=>` threads, so a payload-second `Maybe`
  could not ride the railway at all (§7).

  **The two tails.** A sum has two open ends and they are different
  kinds. `...` continues a track's **wires** (a stack variable, `ρ`);
  `---` continues a row's **alternatives** (a row variable, `σ`). One
  glyph per kind, in every position — declaration heads, written types,
  terms. The inferred types have always told them apart by letter:

  ```
  braid> :t (toStr | not | ---)
  (a0 | (ρ0 | ρ1) | σ0) ⇒ (Str | (ρ1 | ρ0 | σ1) | σ0)

  braid> :t (toStr | not | pass)
  (a0 | (ρ0 | ρ1) | ρ2) ⇒ (Str | (ρ1 | ρ0 | σ0) | ρ2)
  ```

  The first row says *at least these two alternatives, maybe more* —
  `σ0` is the residual, and it passes. The second says *exactly three
  alternatives*, the third of which passes; `ρ2` is a track's contents,
  not a row. Before 2026-09-12 `| ...` meant the residual and there was
  no way to write the other one; `| ...` is now refused outright
  (§14) so no row silently changes meaning.

  A written `---` is an ordinary `σ` on display: `data Any2(---) =
  (Int | Str | ---)` gives `Any2 : (Int | Str | σ0) ⇒ Any2((σ0))`
  (§8). `(---)` — the sum that is all residual — is a legal type, and
  it is `into`'s result shape (§6, §9).
- **`Fn⟨Σ ⇒ Θ⟩`** — a reified program (quotation type). The internal
  hom: `ev` is modus ponens. The arrow inside carries its grade, and
  a declared one MEANS it: `Fn⟨Str ⇒ •⟩` refuses an io quotation
  (*Cannot unify effects: IO vs pure*); `Fn⟨Str =IO> •⟩` is the io form
  (§8). The same holds for every other label — `Fn⟨Int ⇒ Int⟩` refuses
  a quotation that USES `while` or a knot; write `Fn⟨Int =Recursive> Int⟩`
  (§14). It is only the quotation's own code that counts: handing a
  written pure `Fn` *to* `while` or `loop` is fine, since the label is
  on the loop and not on what it runs (§3).
- **Named types**: `type` aliases and `data` declarations (§8).
  Display folds structural types back to their alias names when they
  match exactly (`:t!` shows raw).

  **A declaration may not name itself to the left of an arrow**
  *(2026-09-18)*. `data Stream(a) = (a Fn⟨• =Recursive> Stream(a)⟩)` is
  fine — the self-occurrence is in the arrow's **output**, which is
  codata — and so is one under no arrow at all (`List`, `Tree`). A
  self-occurrence in an arrow's **input**, at any depth, is refused:

  ```text
  data Rec(a, b) = Fn⟨Rec(a, b) ⇒ Fn⟨a ⇒ b⟩⟩

  error: Type Rec: `Rec` occurs to the LEFT of an arrow in its own
  declaration, which admits general recursion with no `Recursive` on the
  arrow.
  ```

  That type is the typed Z combinator's, and with it general recursion
  types **pure**: `fixZ : Fn⟨Fn⟨a ⇒ b⟩ ⇒ Fn⟨a ⇒ b⟩⟩ ⇒ Fn⟨a ⇒ b⟩`, a
  factorial built from it `• ⇒ Fn⟨Int ⇒ Int⟩`, and no label on any
  arrow to say so. The refusal is what leaves `with Recursive` as the
  **one door** into recursion (§8, §14) — the alternative, minting
  `Recursive` on a negative declaration, would have been a rule with
  cases where this is a rule with none. Polarity is tracked through
  other declared types by their parameters' variance, so
  `data Neg(a) = Fn⟨a ⇒ Int⟩` then `data Bad = Neg(Bad)` is refused
  too; `type` aliases need no rule of their own, being expanded before
  the body is checked.

  **Named fields** *(2026-09-14)*. A **single-alternative** `data`
  declaration may name its positions, and each name becomes a
  **projection word**:

  ```braid
  data Trade = (sym: Str, px: Float, qty: Int)
  #   sym : Trade ⇒ Str      px : Trade ⇒ Float      qty : Trade ⇒ Int
  ```

  The names die at the parse. What is declared is the positional type
  it always was — `Trade : Str Float Int ⇒ Trade`, `unTrade` the other
  way, `Trade(s, p, q) -> …` destructuring by position — and what
  survives is a list of **words**, one projection each, generated
  beside `unTrade` and `foldTrade` and no different from them: they
  show in `:defs`, they `reflect`, they quote and go to `map`.
  A projection is `unTrade` and then the tensor stage that keeps one
  wire, which is why it is one wire: **a named field is exactly one
  wire**.

  **Column names are words, not types.** Nothing in the type system
  knows that `px` is called `px` — two declarations with the same
  layout are the same type, and a field name is looked up exactly as a
  `def` is. That is what makes a data frame's column names ordinary
  definitions (§12, `examples/frame.braid`) rather than a second kind
  of name with its own scoping. It is also why a name that is already
  a word is an **error**: objects are added, never merged (§14).

  **Generated by a `table`** *(2026-09-15)*. A `table Trades =
  "trades.csv"` declaration (§8) writes exactly this `data` line from
  the CSV's header, plus two words:

  ```braid
  data Trades   = (sym: Str, px: Float, qty: Int)   # names from the header
  headerTrades  : • ⇒ List(Str)                     # the header line, verbatim
  loadTrades    : Str =IO Recursive> (List(Trades) | Str)
  ```

  `headerTrades` is the file's header **as it was written** — it is a
  presentation, and printing it is what `examples/frame.braid`'s
  `printFrame` wants. The column **words** are the sanitized (or
  schema-written) names. `loadTrades` re-reads the file it is given and
  puts a row that does not read on the miss track, carrying its line
  number. Everything else the declaration generates is named
  `Trades@…`, the compiler's spelling, which source may not write.
- **Resources**: `model Name in Doctrine = <stack>` (§8) — a `data`
  declaration **and a model of the Doctrine** *(2026-09-17; spelled this
  way since 2026-09-18, when the `resource` keyword went)*.
  One nominal wire, carrying its contents boxed, meant to be threaded
  rather than consumed; a run of them shared by both sides of an arrow
  folds onto the arrow as `=Log Counter>` (§3). `with R` is transport
  into the model the declaration generates, and the routing pass is
  that model's **fused** evaluator — the fibre `C(R ⊗ Σ, R ⊗ Θ)` is
  representable, so `embed [s] ; compose` normalises to the `_`-padding
  the elaborator already wrote.
- **Exponents**: `A^n` (input `Int^3`, `R^n`; display `Int³`, `ℝⁿ`) — a
  segment repeated n times. `n` is erased at runtime; concrete
  exponents expand away. **The terminal object is a legal base**
  *(2026-09-20)*: `•^n` (equivalently `one^n`, or `(•)^n`) is the
  zero-wide bundle, and `•^k` is `•` for every literal k. Only the
  parenthesized form parsed before today, for no reason but the order
  of two equations in the stack parser. See §13 and
  `design-exponents.md`.
- **`Fin(n)`** — an index into a bundle of width n. `Aⁿ` *is* the
  function space `Fin(n) ⇒ A`, stored tabulated and flat. The bound is
  a type, erased exactly as every other width: at runtime a `Fin` is a
  bare `Int`. See §9 and `design-indices.md`.

## 6. Program forms

*Amendment (2026-09-16): `over` and `use` are gone. A def's two header
clauses are `in` (MEMBERSHIP — what this def is a morphism of) and
`with` (APPLICATION — the functors applied to its body), both written
LEFT OF THE `=`: `def NAME [in T] [with M …] = body`. A scope is not a
stage, so neither word may stand in a spine. A quotation is the other
place a body is written and takes the same `with` clause, introduced by
the same `=`: `[with Fuel = dup ; *]`. The receipt is `with@F`.*

### Quotation `[p]`
`[p] : • ⇒ Fn⟨…⟩` — pushes the program as a value; a **pure point**
even when `p` does real work, and even when that work is io
(`[print] : • ⇒ Fn⟨a0 =IO> •⟩` — the grade rides inside, and `ev`
transfers it out). Run with `ev : Fn⟨ρ0 ⇒ ρ1⟩ ρ0 ⇒ ρ1`
(the `Fn` sits *below* its arguments). Quotes capture in-scope binder
names (closures).

A quotation may open with the **`with` clause** a def takes, introduced
by the same `=`: `[with Fuel = dup ; *]` reifies the program *as the
scope elaborated it*, receipt and routing included, which is what
`traced.braid` and `metered.braid` print. It declares nothing, so there
is no `in` here.

### Grouping `(p)`
The enclosed program becomes one atom. Grouped compounds in non-final
tensor position are typed closed (their outer tails become `•`).

### Binders
```braid
(x y -> body)      # inline: an atom consuming two wires
[x y -> body]      # quoted: an Fn value (a closure)
def w =
    x y ->         # postfix: names the top wires; the REST of the
    body           # scope is the body
-> x y             # naming: LABELS two wires without consuming them
```
Parameters bind wires **leftmost = deepest**, exactly as atoms align in
a tensor stage, and are in scope as constants — including inside quotes
(closure capture). Bound names shadow prims/defs; duplicate parameters
are rejected.

**Destructuring binders** *(2026-09-14)*. A slot of a binder head may be
a constructor pattern over a **single-alternative** `data` type, naming
its fields:

```braid
def dneg = Dual(a, da) -> (a ; fneg) (da ; fneg) ; Dual
(Dual(a, da) Dual(b, db) -> …)   # one per slot
(Dual(a, da) x -> …)             # mixed with plain parameters
(Dual(a, da) ... -> …)           # and with the open form
(Wrap(Dual(a, da), n) -> …)      # a field may itself be a pattern
```

This is SYNTAX, and it dies before the parse tree exists: a pattern
rewrites, token for token, to the un-constructor stage a hand wrote
until today. `Dual(a, da) Dual(b, db) -> p` *is* `unDual _ ; _ _ unDual
; (a da b db -> p)`, and `Dual(a, da) -> p` *is* `unDual ; (a da -> p)`
— the `un`-stage for the j-th slot pads with `_`, one for each wire
already un-constructed to its left and one for each slot still whole to
its right. So nothing downstream knows about patterns: inference, the
runtime and `reflect` see ordinary binders, and reflecting a
destructuring binder prints exactly what reflecting the hand-written
form prints. The fields bind leftmost = deepest and shadow like any
parameter (§14 has what a pattern refuses).

**Binders are wiring, closures included** *(2026-09-12)*. `reflect`
(§12) compiles a binder away into the vocabulary Code already has. A
parameter used plainly is a `dup` on the parameter block; a parameter
used **inside a quotation** is a `capture`, and one used **inside a
row** is a `dist2` — the exponential's and the coproduct's own maps
(§10), not new primitives. So there is no closure exception:

```braid
:t (x -> [x ... >> +])
    a0 ⇒ Fn⟨Int ⇒ Int⟩
[(x -> [x ... >> +])] >> reflect >> ((c -> c >> unparse >> print) | print) >> forget
    dup pass >> _ (_ [dup pass >> _ + >> drop pass] >> capture) >> drop pass
[(n -> n >> zero >> (n >> drop >> 1 | n n >> *) >> merge)] >> reflect >> ((c -> c >> unparse >> print) | print) >> forget
    dup pass >> _ zero >> dup pass >> _ (dist2 >> (dup pass >> _ drop >> _ 1 >> drop pass
      | dup pass >> dup pass >> _ swap pass >> _ * >> drop pass)) >> _ merge >> drop pass
```

Read the first: `dup` the block, hand the copy to a quotation compiled
against a block of its own, then `capture` the copy into it — one
`capture` per parameter, the shallowest wire on the stack binding the
deepest input of the `Fn`. Read the second: `dup` the block, `dist2` it
into both tracks, compile each branch over its own copy, and let each
branch drop it. Both keep the original type, so nothing downstream
changes. `capture` and `dist2` are the two prelude names a module may
**not** shadow — reflected code names them, and shadowing one would be
capture.

`dist2` is the *derived* word, and it covers the closed two-track case
only. A wider row, or one with a residual, emits the generator
`#dist:K` instead — one member per written width, unspellable by
construction (`#` opens a comment), so it needs no shadowing rule:

```braid
[(x s -> s >> (x ... >> + | ---))] >> reflect >> ((c -> c >> unparse >> print) | print) >> merge
    _ dup pass >> dup pass >> _ swap pass
      >> _ _ (#dist:1 >> (dup pass >> _ + >> drop pass | ---)) >> drop drop pass
```

`#dist:K : a (ρ1 | … | ρK | σ) ⇒ (a ρ1 | … | a ρK | σ)` pushes the wire
into the first K alternatives and **passes the residual** — the only
thing that can be done with alternatives nobody can name. With it,
`reflect` is total on binder code (§12, §14).

**A parameter list uses the stage vocabulary**, one slot per wire, in
any order (slots align with wires exactly as atoms do — leftmost =
deepest). A name consumes one wire and binds it; `_` consumes one wire
and hands it to the *body*; `...` hands the body the whole rest.
Whatever the list does not name becomes the body's input:

```braid
(x     -> body)  : A ⇒ Δ       body : • ⇒ Δ   # input-closed (the default)
(x _   -> body)  : A B ⇒ Δ     body : B ⇒ Δ
(x _ z -> body)  : A B C ⇒ Δ   body : B ⇒ Δ   # `_` may sit anywhere
(x ... -> body)  : A ρ ⇒ Δ     body : ρ ⇒ Δ   # open binder

1 2 3 >> (x ... -> x x ... >> + + >> +)       # 1 1 2 3 → 2 5 → 7
1 2 3 >> (x _ z -> z _ x)                     # → 3 2 1
```

An **open binder** hands the remainder *to* the body, so the body can
position it with `...` — unlike `(x -> body) ...`, which routes the
remainder *around* the binder and leaves the body unable to touch it.
Same wires, different power. (`_` slots, by contrast, are pure
convenience: for a fixed arity you can always name the wire instead —
`(x _ z -> z _ x)` ≡ `(x y z -> z y x)`.)

Rules: `...` must be last, and only one. An open binder is an
open-arity word, so it must be the final atom of its stage.
Everything-exact still applies inside — the body must account for the
wires `_`/`...` give it (`(x _ -> x)` is an error: the `_` wire goes
unused). Every binder `reflect`s, compiling to ordinary wiring (§12).

#### The naming binder `-> x y z`

**The arrow's side says what happens to the wires.** Names *before* it
are cut from the stack; names *after* it are labels — identity at
runtime, so the wires flow straight on and the names are also in scope
for the rest of the enclosing scope. In a drawn diagram you write a
label beside a wire without cutting it; this is that
(`examples/tag.braid`).

It is sugar for the open binder that puts back what it took —

```braid
-> x y z   ≡   x y z ... -> x y z ...
```

— so it needs no machinery of its own, and its type is the identity:

```text
braid> :t -> x -> pass
-> x -> pass : a0 ρ0 ⇒ a0 ρ0
braid> :t -> a b -> pass
-> a b -> pass : a0 a1 ρ0 ⇒ a0 a1 ρ0
```

**Slots use the stage vocabulary**, exactly as the cutting form does: a
name takes one wire, `_` skips one. Slots are positional from the
deepest wire — the same alignment as atoms in `print print _` — so `_`
is how you name the third wire without naming the first two:

```braid
1 "a" .foo -> _ _ tag -> print print drop
tag >> print          # .foo
```

`...` is rejected: passing the rest along is what the form already *is*.

Because the wire is still on the stack, each later mention of a name is
a `dup` in diagram terms — and a name outlives its wire:

```braid
7 -> x -> drop        # the wire goes...
x x >> *              # ...the name remains: 49
```

**Placement.** The arrow ends the stage it follows, so a naming binder
can sit mid-line (`1 "a" .foo -> x _ y`), after a separator
(`5 ; -> x`), or lead a scope (`def f =` ⏎ `-> h m f`). Its body is the
rest of the scope, introduced by an explicit `->` or by an ordinary
stage break (`;`, `>>`, or a newline). A binder with nothing after it
is an error — the names would have nothing to reach.

One collision to know about: when the stage before the arrow is a run
of bare identifiers, `a b -> c d` is claimed by the *cutting* binder at
the start of a scope or after a newline (its documented position), and
read as *naming* anywhere else. Anything with a literal, group, or
quote in it — like `1 "a" .foo -> x _ y` — is unambiguous either way.

### The header clauses: `with` applies, `in` declares

Two words, and the difference between them is the whole shape of the
declaration layer. Both are **header clauses** — they are written left
of the `=`, never in the body:

```text
def NAME [in T] [with M …] = body
```

`in` at most once, `with` a list, `in` before `with`, and the body is a
pure spine.

**`with X`** *applies* X to the body. One rule, every kind: *the body is
written in the DOMAIN of X, and X is applied to it.*

**`in X`** *declares* that this def **is a morphism of X**. It applies
nothing, writes no wires and mints no label. It says what the def is;
the body is exactly as written.

| clause | X is | the body is written in | what happens |
|---|---|---|---|
| `with Inst` | a model of theory T | T's vocabulary (slot names) | renamed to Inst's words — *into* the base |
| `with Opt` | a model of `Base` | the base | its generators renamed to their images — base to base |
| `with Mod` | a model of `Base` **with an object map** | the base | reinterpreted at another type: literals through `via`, generators to their images, defs unfolded — base to base, but the arrow changes (§8) |
| `with R` | a resource | the base | routed: `R ⊗ –`, wires written *out* of the base. **Transport into the model `model R in Doctrine` generates, in fused form**, and the header is optional — routing is inferred (below) |
| `with F` | a functor | the base | rewritten by F's graph morphism, extended along the spine, *out* of the base |
| `with M` | a model whose theory has a hom-object | the base | **transported**: every stage is embedded, `;` is the composition, *out* of the base |
| `in T` | a theory | T's vocabulary | nothing — the def is a **template** over T |
| `in M` | a model whose theory has a hom-object | M's vocabulary | nothing — the def is written in M's words, and if it builds one carrier out of nothing it is a **morphism of M** |
| `with Recursive` | the built-in **marker** (§8) | the base, plus the def's own name | rewritten to the closed knot form — applied **innermost**, before every other scope on the header |

Models of base theories point *into* the base; a model with a carrier,
a resource and a functor point *out* of it. `in` is the only way to
declare membership, and `with` the only way to apply a functor. Every
`with` leaves a **receipt** on the arrow (§3, §12); `in` leaves none,
because nothing was applied.

`in` names exactly one thing. `def f in Ring with Log = …` is a
template that also threads a resource: two words, two jobs.

One `with` clause may name **several kinds at once**, freely mixed —
they are kinds of scoped selection, not separate features:

```braid
model Log in Doctrine = Str
theory Sink(a)   = emit : a ⇒ a
model Loud in Sink(Int) = emit = dup ; print ...

def run =
    with Log Loud       # a resource AND a model
    dup ; *
    emit                # resolves to Loud's; the Log threads past it
```

A resource contributes a wire the elaborator threads; a model
contributes no wire at all and disappears at elaboration, leaving its
slots renamed.

`with` names **resources, models, functors and the marker `Recursive`**
(§8) and applies them to the def's whole body. An elaborator running
between parse and inference writes every `_` and `...` the threading
needs, from the resource declarations alone:

```braid
model Log     in Doctrine = Str
model Counter in Doctrine = Int
def note = unLog _ ; cat ; Log                  # Str =Log> •
def bump = unCounter ; 1 ... ; + ; Counter      # • =Counter> •

def score with Log Counter =
    dup ; *
    bump
    "scored "
    note
```

The same program written by hand — same wires, same type, all of the
arithmetic visible, and a third resource would renumber every line:

```braid
def scoreByHand =
    _ _ (dup ; *) ...
    _ bump ...
    _ _ "scored " ...
    swap ...                    # bring Log up beside the Str
    _ note ...
    swap ...                    # and put it back
```

Both are `Int ρ0 =Log Counter> Int ρ0`. Inference is the *checker* of
the elaboration, never an input to it: the elaborator places the wires
at statically known offsets (resources ride deepest, in `with` order),
and the ordinary type checker verifies the result.

*Amendment (2026-09-17): **the header is optional — routing is
inferred.*** A def is routed for a resource when the scheme of an atom
in its body, **alone in its stage**, carries that resource as its
deepest wire on both sides. The wire is then padded under every other
stage exactly as if `with E` had been written, and the def's **callers**
are routed the same way, transitively, until the wire meets an
**install site** (a written seed) or a **handler** (a discharge). A
resource word originates its label at the leaf, exactly as the four io
prims originate `IO`, and the label propagates by composition like every
other.

```braid
def note = unLog _ ; cat ; Log
def f    = "x" ; note              # f : ρ0 =Log> ρ0 — no header
```

`with E` on a resource **stays legal and is exactly what inference
does** — routing is idempotent, so the header is the *explicit form*
rather than a second mechanism — and it is the **override**: it names
the scope, where inference only proposes one. `def h with Log Counter =
dup ; * ; bump` is routed over both even though only `bump` threads
anything.

Two things are never auto-routed. A body that names the carrier's
constructor or un-constructor (`Log` / `unLog`) is **handling the wire
itself** — an install site or a handler — so padding would put a second
wire beside the one it holds; that is what keeps `collectLog` and
`note` working. And a stage that writes **its own `_` and `...`** around
the resource word is threading **by hand** and says so: `scoreByHand`
above and `def tick = _ bump ...` keep exactly the types they had.

The one rare edge is loud, never silent: a def that receives the
carrier as a **value** and also calls a resource word ends up holding
two `E` wires and is refused by name, because the carrier is nominal
and a `Str` is never a `Log`. A missing install stays *you forgot to
install*.

`:t!` says when a def was routed by inference, and why:

```text
braid> :t! f
f : Log ρ0 ⇒ Log ρ0
  routed for Log: calls `note`
```

Invariant five is untouched: routing reads the schemes of **callees**
in the prefix scope — fixed before this def is touched, as good as
written — and never the manifest of the def being elaborated.

**`with` asserts its claim.** The incoming wires must really be those
resources, even when the body never touches one:

```braid
def f with Log = dup          # a0 ρ0 =Log> a0 a0 ρ0 — Log is claimed,
                                #   though the body never mentions it
```

**`with` also selects models**, and may mix them with resources in
one header — it is the same word for both kinds of scoped selection:

```braid
def total with IntSum = [op] unit ... ; foldExp   # Intⁿ⁰ =IntSum> Int
```

The `=IntSum>` is the scope's **receipt** *(2026-09-13)*: every `with`
mints, models included, so the arrow records which model read the
body. That is provenance in exactly the sense a functor's receipt is.

One clause may name both kinds at once — `with Log Counter IntSum`
opens a scope over two resources and one model.

A model name binds the theory's slots to that model's programs
for the rest of the scope. Unlike a resource, a model claims no
wire and asserts nothing about the incoming stack: the selection is a
renaming at elaboration (§8), so it disappears before inference.

**The third kind of name is a functor** (§8, §12): `with Fuel Metered`
threads the resource and then hands the routed, renamed body — as
`Code` — to the word `Metered` names, splicing back what it returns.

**A model whose theory joins the DOCTRINE transports** *(2026-09-13)*.
There is no fourth keyword: if the theory is declared `in Doctrine`
and takes the doctrine's composition and embedding (§8), `with`
of one of its models takes over `;` itself — every stage becomes the
embedding of that stage and every `;` becomes the composition, so a
block reads as the ordinary program it is and comes out as a value of
the category the model presents. The model's slot words are in scope
too, so `with Circuits` is the old renaming *plus* owned composition.
Its **exits** — the slots that take the carrier and hand back base,
`observe` and kin — are refused inside the scope and called under
`in Circuits`, which transports nothing: *entering is a marker,
leaving is a model*. One such model per header.

**A theory is not one of them.** `with Monoid` is refused:

```
`with Monoid` names a theory: `with` applies a functor, and a theory is
not one — write `in Monoid` to make this def a template
```

That is the one row that used to break the rule, and `in` is where it
went (§8).

One clause, four kinds for `with` plus the templates `in` declares,
applied in a fixed order. **The order is ACTIONS, not keywords**
*(restated 2026-09-18)*: templates **expand**, then **renames**, then
**routes**, then **composes**, then **rewrites**, left to right — so a
rewrite always sees finished wiring, and an expanded template body is
routed by every scope it landed in, exactly as if it had been written
there.

Which action a name takes is read off its **declaration** and never off
a keyword: a carrier declared `model R in Doctrine` routes; a model
whose theory has slots renames; a model of `Base` rewrites by its
table; a model whose theory has a hom-object composes; a functor
rewrites the spine. The elaborator has never partitioned any other way,
which is why folding `resource` into `model` (§8) changed nothing here.

`with F G` applies F and then G, and that **is** their composite —
functor composition is `;` on the extensions — which is why one clause
may name several and why the order is left to right. When the order
carries meaning, put the names on one header in the order you mean.
The extension word each declaration generates (`Metered`, `Traced`, at
`Code ⇒ Code`) is in scope for the module's main program, its model
bindings and its laws — which is where `lift2 [Metered]` and
`examples/optimizer.braid`'s functor laws name it — and a def body
composes with its header instead, because the extension is written
below the defs the morphism may name (the ordering rule again).

Every `with` scope leaves its RECEIPT — the label on the manifest
of everything it elaborated (§3, §12) — and `in` leaves none.

**What `with` does to a pure stage is `lift`** (§10), an ordinary
prelude word: `lift : Fn⟨ρ0 ⇒ ρ1⟩ ⇒ Fn⟨a0 ρ0 ⇒ a0 ρ1⟩` runs a program
one wire deeper, composable once per context wire. Nothing about
ambient threading is machinery you cannot write yourself; `with` only
saves you the counting. See `examples/resources.braid` and §14 for the
current limits (one resource operation per stage, or a word threading
the whole scope unchanged).

### Rows `(p₁ | p₂ | …)`
The sum functor's action: one wire in carrying `(Δ₁|Δ₂|…)`, component
i runs on alternative i, results re-tagged in place. Arms are **bare**
programs (the delay law: a row is the one context where bare code is
conditional). Sugar:

| form | means |
|---|---|
| `(f \|)` | `(f \| pass)` — trailing bar passes the last track |
| `(\| f)` | `(pass \| f)` — leading bar passes the first track |
| `(\| f \|)`, `(f \| \|)`, … | **every** empty arm is `pass` — any track, any count |
| `(f \| ---)` | open row: identity on all remaining alternatives (row residual σ) |
| `(f \| ...)` | **refused** — `...` continues wires, `---` continues alternatives (§14) |

Rows are **line-scoped**: bare rows work without parens (`ok | guard`
on its own line), and a row cannot span a line break. Each arm lives
on one line.

**Track-column layout**: over a *flat* sum, successive bare-row lines
each touch one track and draw the others straight through — aligned
`|`s are literally the wires, and the text reads as the string diagram
(`examples/vertical.braid`):

```braid
route3                              # Int ⇒ (Int | Int | Int), flat
drop >> "negative" |                |
|                    drop >> "zero" |
|                    |                toStr
(print | print | print)
forget
```

Flat sums come from the inject-and-collapse idiom — each router arm
injects into the *same* flat sum, `merge` collapses:
`negative? >> (alt1 | zero? >> (alt2 | alt3) >> merge) >> merge`.

`merge : (ρ0 | ρ0) ⇒ ρ0` rejoins agreeing tracks (the codiagonal).
Arms must agree on the result type to merge.

**Rows are decidable** *(2026-09-13)*. `sameCode` normalizes a row: it
follows an injection it knows, and where it does not it *splits* — one
branch per track — so `alt1 ; (f | g) ; merge = f` and `(alt1 | alt2) ;
merge = id` are proved rather than sampled (§12.9,
`examples/distributive.braid`). The residual is compared **semantically**,
not as a flag: over a closed two-track sum, `(f | ---)` and `(f | pass)`
are the same morphism, and `sameCode` says so.

### The open eliminator: `into`
`merge`, `case2` and `otherwise` all need a **closed** row — they are
copairings, and a copairing needs one handler per alternative. Over a
residual there is exactly one copairing you can write, `[h, id]`, and
that is the prim:

```
into : Fn⟨ρ0 ⇒ (σ0)⟩ (ρ0 | σ0) ⇒ (σ0)
```

It handles the **first** alternative by mapping it into the *remaining*
row and shifts every other tag down one. Each `into` shortens the row
by one, so a ladder peels alternatives off the front and the existing
`otherwise` closes what is left:

```braid
s
[h1 ; alt1] ... ; into        # handle track 1 into the rest
[h2 ; alt1] ... ; into        # …then the next
_ [d] ; otherwise             # two left: pass one, run the default on the other
```

The `...` is not decoration: `into` wants its handler **deepest** (as
`ev`, `loop` and `caseN` do), and `[h] ...` is the stage that pushes a
quote under the wires already on the stack. `otherwise` wants its
default *shallowest*, hence `_ [d]`.

With one alternative left the result is the 1-ary sum `(Θ)`;
`there ; merge` is how a 1-ary sum comes back to a bare stack.
`examples/into.braid` runs the whole ladder, and the Elgot identity
`loop f = f >> [loop f] into` with it.

`>=>` is `[q, alt2]` — a *closed* copairing, and not a model of
`into`.

### Injections
`alt1 : ρ0 ⇒ (ρ0 | σ0)`, `alt2`, … `altN` — tag the whole input segment
at position N (open row tail). Aliases: `ok`/`here`/`again` ≡ `alt1`,
`miss`/`done` ≡ `alt2`. `there : (σ0) ⇒ (ρ0 | σ0)` shifts tags by one
(`here >> there ≡ alt2`).

### Building lists: `pack`
The primary list introduction is a word, not syntax — `pack : aⁿ ⇒
List(a)` boxes a bundle, and a **group is the delimiter**:

```braid
(1 2 3 ; pack)              # List(Int) — the stack IS the list
(x (10 x ; *) ; pack)       # elements are FULL programs, no special grammar
((1 2 ; pack) (3 ; pack) ; pack)     # nesting
(1 "a" 2 "b" ; pack2)       # two-wire elements: List(Int Str)
(pack)                      # empty (≡ nil); in final position it is open
```

One-way by design: there is no `unpack : List(a) ⇒ aⁿ` — a list's
length is runtime data, and the exponent is erased (elimination is
`foldList`/`uncons`).

The **vertical** form is a `...` ladder closed by a top-first pack
(`packR`, `pack2R` for two-wire lanes): each line pushes *under*, and
reading the segment top-first makes list order = text order:

```braid
def fbCases =
    [by15?] [drop >> "FizzBuzz"]      # first lane = first priority
    [by3?]  [drop >> "Fizz"] ...
    [by5?]  [drop >> "Buzz"] ...
    pack2R
```

(The old `|| e1 || e2` literal is REMOVED — `|` belongs to sums alone.)

(The old flat literal `list(e1, e2, …)` is REMOVED — `list` is now an
ordinary identifier. `(… ; pack)` is the flat form.)

### Eliminating nested sums: `case2` / `case3` / `case4`
The flat coproduct eliminators are prelude **words** (the old
`case(…)` special form is REMOVED — `case` is an ordinary identifier):
one quoted handler per track, sum on top, handlers below:

```braid
tag >> [h1] [h2] [h3] ... >> case3     # (Δ1 | (Δ2 | Δ3)) ⇒ R
```

`case3 ≡ (f g h s -> s >> (f ... >> ev | (g ... >> ev |
h ... >> ev) >> merge) >> merge)` — heterogeneous handler domains,
one shared result; to sums what `foldList` is to lists. Handlers are
quoted (the `[]` tax), unlike bare row arms — write the nested rows by
hand when bareness matters.

## 7. Railway operators

Parse-time sugar, all one shape — next stage on one track, a default
injector on the other:

```
t1 >=> t2   ≡  t1 >> (t2   | alt2) >> merge     -- Kleisli: thread the hit track
t1 >?> t2   ≡  t1 >> (alt1  | t2)  >> merge     -- elif: thread the miss track
t1 >!> t2   ≡  t1 >> (pass | t2)  >> merge     -- close with a total default
```

They bind looser than `>>` (each side is a whole `>>`-chain) and may
span line breaks (the only operators that do). They are
deliberately thin: the row form on the right is always available.

## 8. Definitions, types, modules

*Amendment (2026-09-16): `over` and `use` are gone, and every head now
reads the same way. A def is `def NAME [in T] [with M …] = body`; a
theory extending another is `theory Arrow(k(..., ...)) in Doctrine`; a
model's head says which theory it interprets, `model Floats in
Smooth(Float, Float)`, and a family's drops its dead parameter name,
`model Fwd(Smooth(a, _)) in Smooth(Dual(a), a)`; a transformation names
its hom-set, `transformation Value in Fwd(Floats) ⇒ Floats = value,
zeroTangent`. Four glyphs, one meaning each: `;` COMPOSES, `,` LISTS a
declaration's items, `:` TYPES a slot, `=` DEFINES a body — so `;`
between two bindings is refused by name. Under `with M`, a def
declared `in T` for M's theory is INSTANTIATED and one with no `in` is
TRANSPORTED; never both.*

```braid
def name = program            # inline body — ends at the line
def name =                    # block body — `=` ends the line,
    program                   # body on the following (indented) lines
    continues
def name in T with M … = body # the two header clauses (below)
```

- `## doc` lines immediately before a `def`/`type`/`data` attach to it.
- Defs may **shadow** prims and prelude words; duplicate defs of the
  same name are an error.
- **Self-reference is marked**: a definition is **not in scope in its
  own body** unless its header says so. `def f = … f …` is refused —
  "`f` refers to itself: write `with Recursive` in its header (MANUAL
  §8)" — and so is the old `recurse` spelling, which is gone.
- **Recursion is a marker** *(2026-09-14)*. `with Recursive` in a def's
  header puts the def's **own name** in scope in its own body, and
  nothing else:

  ```braid
  def fac with Recursive =
      (n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> fac) >> *)) >> merge)
  # fac : Int =Recursive> Int      5 >> fac  →  120
  ```

  It is not a special form. Elaboration rewrites the body to the closed
  form the language already had — a binder with the knot deepest, every
  self-call routed through it — and does so **before inference** and
  **innermost** among the header's scopes, so `with Traced Recursive`
  traces the closed spine. Every elaborated def is therefore still a
  **closed spine** over its prefix scope, which is what keeps
  `reflect`, the per-stage schemes and every functor total.

  The rewrite is syntactic: no types are consulted, and a binder
  parameter named like the def **shadows** it exactly as it shadows any
  other word. A self-call inside a quotation is a **capture**, and
  abstraction elimination handles it like any other captured wire —
  which is what makes guarded corecursion (`examples/stream.braid`)
  ordinary code.

  A point-free body needs no binder at all; the name is a word:

  ```braid
  def until100 with Recursive = lt100? >> (double >> until100 | _) >> merge
  ```

  `Recursive` is the **receipt** of that scope (§3), minted exactly as
  `with Traced` mints `Traced` — when the scope CHANGED the code, which
  here means the body named the def and a knot was tied. A body that
  never names it gets no knot and no label *(2026-09-18)*, including
  one where a binder parameter shadows the def's name. The knot the
  marker ties carries the label too, and a manifest is a set, so a
  marked def that also calls `loop` says `Recursive` once.
- **`fix` is derived** *(2026-09-14)*, and is for **open** recursion —
  a body someone else hands you, a memoizing or logging `self`, a body
  you built at runtime:

  ```braid
  fix : Fn⟨Fn⟨ρ0 =Recursive> ρ1⟩ ρ0 ⇒ ρ1⟩ =Recursive> Fn⟨ρ0 =Recursive> ρ1⟩
  ```

  The body receives the knotted function **deepest**, then its own
  arguments, so the recursive call is an ordinary quoted call —
  `… >> self ... >> ev`. Three stages: quote the body, tie the knot,
  `ev` it. `... ` carries the arguments over the quote (a stage's
  leftmost atom is its deepest wire, so `[body] ...` pushes the quote
  *under* them).

  ```braid
  def facBody = [(self n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> self ... >> ev) >> *)) >> merge)]
  def fac     = facBody ... >> fix ... >> ev
  ```

  Reach for the marker first: it is the same knot with the plumbing
  written for you. Reach for `loop`/`while`/`until` (§10, §11) before
  either when the recursion is a tail call — it is one word and needs
  no knot — and for the **generated structural recursor** (`foldTree`,
  `foldNat`, the prelude's `fold`) when the recursion is structural,
  since those descend on a smaller value and terminate by construction
  — and, being bounded, mint no `Recursive`.
- **The knot itself is not a word.** The machinery the marker emits is
  spelled `#fix`, and `#` opens a comment, so no program and no
  reflected atom can name it — the same trick that keeps `#dist:K` and
  `with@F` out of source. It is why `fix` could leave the primitive set
  (§9, 48 → 47) without the language losing a knot.

  **There is exactly one door** *(2026-09-18)*. `#fix` is unspellable
  and `with Recursive` is the only thing that opens it, so an
  unlabelled word ties no knot — but until 2026-09-18 that was not the
  whole story, because a `data` declaration naming itself to the **left
  of an arrow** made the typed Z combinator writable and general
  recursion available with a **pure** manifest. Such a declaration is
  now refused (§5, §14). With that door shut, provenance and the
  semantic property coincide: the label is minted where the knot is
  tied, and there is nowhere else to tie one.
- **Functors reach inside** *(2026-09-12)*: a self-call inside a row
  component or a quotation reflects (§6, §12), so `with Traced` over a
  `with Recursive` factorial traces every stage and prints `24`.
- Let-polymorphism: defs generalize over all four variable sorts.
- The prelude is auto-loaded user code; `:defs` lists it.

```braid
type YN = Bool                        # alias (display folds to it)
type Result(a, e) = (a | e)           # parameterized; each param is ONE WIRE
type Box(...) = (...)                 # `...` — a whole STACK, as one wire
type Tagged(t, ...) = (t ...)         # mixed: a wire, then the stack
type T = Int^3                        # an RHS is a STACK — exponents fine
type Mat(n, m) = Fn⟨Int^n ⇒ Int^m⟩    # n, m are WIDTHS: used under `^`
type Sq(n) = Mat(n, n)                # widths pass on to another alias
type Endo(a) = Fn⟨a ⇒ a⟩              # a reified program as a type…
type Pred(a) = Fn(a -> (a | a))       # …Unicode Fn⟨Σ ⇒ Θ⟩ or ASCII Fn(Σ -> Θ)
type Sink(a) = Fn⟨a =IO> •⟩           # an io program: =IO> (writable; ASCII `->!` or old `⇒!` still lex)
data List(a) = (• | a List(a))        # recursive nominal type
data Tree(a) = (a | Tree(a) Tree(a))
data Stream(a) = (a Fn⟨• =Recursive> Stream(a)⟩)  # codata: recursion THROUGH a Fn
```

**Parameters are kinded**, four ways. A bare name stands for exactly
**one wire**; `...` stands for a whole **stack**, and may only be the
last parameter (at most one); `---` stands for a **row** — the tail of
a sum's alternatives — and is also last (at most one, after the `...`
if both are there); a name used under `^` in the body is a **width**.
The last-position rules are what keep every stack and row variable in
tail position, so no declaration can spell one with anything after it:

```braid
data Pair(a, b) = (a b)        # two wires — inexpressible before kinds
data Box(...)   = (...)        # a whole stack in one wire
data Bad(...)   = (... Int)    # rejected: '...' must be last in its stack
type L = List(Int Str)         # rejected: List's cell takes one wire
```

**Named stack parameters** *(2026-09-16)*. A parameter written with a
trailing `...` is a stack **with a name**, and there may be several,
anywhere in the list:

```braid
data Circuit(a..., b...) = Fn⟨Box(a) =Recursive> Box(b) Circuit(a, b)⟩
data Bad(a..., b...)     = a b     # rejected: the stack parameter 'a'
                                   # must be the last thing in its stack
```

The body spells each by its name. The one-at-most, must-come-last rule
above is the **anonymous** `...`'s — it is spelled `...` in the body, and
one spelling names one thing — while a named stack parameter is held to
the same law where it belongs, in the **body**: a stack variable sits in
tail position or it is a splice, and a splice is unspellable. This is
what lets a hom-object range over whole stacks (§8).

**Row parameters** *(2026-09-12)* say "at least these alternatives,
maybe more" in a written type — the `σ` that inference has always
minted, given a spelling. `---` is the last alternative of a row, never
a bare element:

```braid
data Any2(---)   = (Int | Str | ---)             # Any2 : (Int | Str | σ0) ⇒ Any2((σ0))
data Peeler(---) = Fn⟨(Int | ---) ⇒ (Str | ---)⟩ # a written residual inside an Fn
type Rest(---)   = (---)                         # the all-residual sum: `into`'s result shape
theory Recover(---) =
    recover : (Str | ---) ⇒ (---)                # …and in a theory slot

data Bad(---, a) = (a | ---)   # rejected: '---' must be the last type parameter
data Bad2(a)     = (a | ---)   # rejected: '---' needs a `---` parameter on the declaration
type Bad3(---)   = (--- Int)   # rejected: '---' must be the last alternative of its row
```

A row argument is written the way a row is written anywhere — as a
parenthesized list of alternatives — which is why the argument list of
a rolled `Any2` shows two sets of parens: the outer ones are the
argument list, the inner ones the row. The `---` itself displays as the
ordinary `σ` (§5). Roll and unroll are the ascription that forces a
quotation to a written residual type, and that type is then usable as
an `evalAs` witness:

```braid
[(s -> s >> (toStr | ---))] >> Peeler >> unPeeler
    • ⇒ Fn⟨(Int | σ0) ⇒ (Str | σ0)⟩
```

Widths are declared **by use**, not by annotation: the two roles are
syntactically disjoint (a wire stands where a type stands, a width only
after `^`), so position decides the kind and one parameter cannot be
both. Width parameters are **`type`-only** for now — a `data` type
would need its argument list to carry widths — and every `^n` in a body
must name a parameter:

```braid
type Bad(n) = (Int^n n)        # rejected: parameter 'n' is used both as a
                               #   wire and as a width (^n)
data BadD(n) = (• | Int^n)     # rejected: width parameter 'n' is supported
                               #   on `type` aliases only, not on
                               #   recursive/`data` declarations
type Bad2 = (• | Int^n)        # rejected: Exponent variable ^n is not a
                               #   parameter of this declaration — add it
                               #   to the parameter list
```

Width aliases display-fold like any other: with `Sq` in scope,
`:t [dupN >> addN]` prints `• ⇒ Sq(n0)`.

Because `List`'s parameter sits *before* the recursive slot in
`(• | a List(a))`, it is forced to be a wire — which is why a list cell
is one wire and `Box` is how a pair-list is spelled:
`pack2 : (a b)ⁿ ⇒ List(Box(a b))`.

A `data Name(...)` declaration generates:
- `Name` — the constructor (roll): body stack ⇒ `Name(…)`;
- `unName` — the unroll: `Name(…)` ⇒ body sum;
- `foldName` — the structural eliminator, one quoted case per
  alternative, recursive slots pre-folded (e.g. `foldList :
  Fn⟨• ⇒ b⟩ Fn⟨b ρ ⇒ b⟩ List(ρ) ⇒ b`).

Roll/unroll are free at runtime. Type parameters must occur in the
body. A declaration's right-hand side is parsed as a stack,
so both literal exponents (`type T3 = (Int^3 | Str)`) and exponent
*variables* (`type Mat(n, m) = Fn⟨Int^n ⇒ Int^m⟩`) belong there.

**`model Name in Doctrine = <stack>`** *(spelled `resource Name =
<stack>` until 2026-09-18)* declares a threaded wire — a `data`
declaration, nominal for the same reason `data` is, **and a model of
the Doctrine**. It is a `model` head because that is what it always
was: since 2026-09-17 the declaration writes a carrier `R@k`, a theory
`R@t in Doctrine` and `model R in R@t(R@k)`, and everything downstream
reads it as one (`:doc R` prints all three).

The **body is a STACK**, with no `=` in it, and that is what tells this
head from every other `model` head — a body of `p = q` lines is a
table, a body with no `=` is a carrier. Same content-directed rule the
object map uses; no new punctuation, no position to remember.

`in Doctrine` here is the one place `in` names a **sub-presentation**.
The generated model interprets `compose` and `embed` and *not*
`observe`/`sample`, because a generated `observe` would have to run a
resource program, which needs a seed, and seeds live at install sites.
So a plain `model M in T` is total over `T`'s slots and this one is
not — the only such head in the language, and it says so here rather
than leaving a reader to find out.

```braid
model Log     in Doctrine = Str
model Counter in Doctrine = Int
model GameState in Doctrine = Int Int
```

- **Nominal.** `Int Int` is never silently a GameState — `def notState
  = swap : a0 a1 ⇒ a1 a0`, unfolded. Structural folding would rename
  every def that happened to thread two Ints; a resource's meaning is
  exactly the part its shape does not carry, so it declares a distinct
  type instead.
- **One wire**, its contents boxed, whatever the declared stack's
  width. That is what makes `=Log Counter>` an ordered run of wires
  (§3) rather than a guess about widths.
- **Roll and unroll, no fold.** `Log : Str ⇒ Log` and `unLog : Log ⇒
  Str` are generated as for any `data`; `foldLog` is *not* — you unroll
  a resource, you do not eliminate it by points (`foldLog` reports
  *Unknown primitive*). Roll/unroll are free at runtime.
- **Rides deepest.** Resource wires sit at the bottom of the stack, in
  the order a `with` names them, which is what puts every offset a known
  distance from the deepest wire (§6). Operations are ordinary defs
  that unroll, work, and roll back:

```braid
def note = unLog _ ; cat ; Log                  # Str =Log> •
def bump = unCounter ; 1 ... ; + ; Counter      # • =Counter> •
```

Threading a resource by hand is `_` and `...` like anything else; `with`
(§6) writes that padding. See `examples/resources.braid` and
`design-effects.md`.

*Amendment (2026-09-17): **a resource is a model of the Doctrine**, and
the declaration generates it.* Beside `R`/`unR` it writes three more
declarations, in the compiler's `@` namespace and therefore unwritable
in source:

```braid
data  R@k(a..., b...) = Fn⟨R a ⇒ R b⟩
theory R@t(k(..., ...)) in Doctrine =
    compose : k(a, b) k(b, c) ⇒ k(a, c)
    embed   : Fn⟨a ⇒ b⟩ ⇒ k(a, b)
model R in R@t(R@k) = compose = R@then, embed = R@arr
```

`:doc R` prints all three — sugar you cannot read is a feature, not a
desugaring — and `:defs` hides them, as it hides every other `@` name.
The carrier is Power–Robinson's **state construction**, `K_R(Σ, Θ) =
C(R ⊗ Σ, R ⊗ Θ)`, and it is **representable**: the hom-object is an
object of the base, so fibre composition *is* base composition of
representatives. That is what makes `with R` **transport in fused
form** — `embed [s] ; compose` normalises to `_ s ...`, which is
exactly what the routing pass already wrote, so nothing elaborates
differently and `examples/metered.braid` still burns seven units.

The theory declares `compose` and `embed` **only**, and that is forced
rather than lazy. `observe : k(Int, Int) ⇒ Int` would have to *run* a
resource program, which needs a **seed**, and seeds live at the install
site with no declared defaults — a generated `observe` would be
`mempty`-conjuring by another name. The happy consequence is that no
inherited law runs: every Doctrine law names `observe` or `sample`, so
the `inherited` filter keeps none. The category laws hold by
construction (`embed` is padding, `compose` is `;`).

Two things follow. `in R` is still refused — a representable fibre's
carrier is *cancelled*, so no def ever holds one; write `with R`. And
the model takes the resource's own name, so a `functor` or a `model` of
that name is now a duplicate declaration rather than a shadow.

Routing itself no longer needs the header at all — see §6.

**`Dict`, the dictionary's own wire** *(2026-09-17)*. A declaration is
an **act on the dictionary**, and the dictionary is a resource like any
other: a label whose carrier is looked up from its declaration, exactly
as `Log`'s is `Log ⊗ –` and `IO`'s is `World ⊗ –`. Every declaration
word says so in its own arrow — `defW : Code Str =Dict> •` — which is
the phase distinction the keyword-initial surface marks, written down
as a grade.

What it holds is the module's **declarations so far**: the defs with
their headers and source, the type lines, the theory/model/functor/
transformation blocks, the imports, the tables, the keyword table, and
the program lines the declarations did not take. It is not the finished
module — a module holds an environment, a scheme and a term, none of
which has a Braid rep, and handing one to a program would be a
reflection of the checker rather than a declaration layer. `Dict` is the
**write** handle; the **read** side already exists and is the reflection
words (`declOf`, `typeOfWord`, `envOf`, §12), which read the four tables
the checker holds at the point the word runs.

**A program cannot discharge it, structurally.** A handler is `seed ;
… ; unwrap`, and both ends come from the `data` machinery a
`model R in Doctrine` line drives. `Dict` is declared by no such
line — it is not declared at all — so there is no `Dict` to seed one with and no `unDict` to open
one with, and the name may not be taken:

```text
`Dict` is the dictionary's own wire and may not be declared: `Dict` is
  the carrier every declaration word acts on (`defW : Code Str =Dict>
  •`), it is threaded by the loader, and there is no `Dict` to seed one
  with and no `unDict` to open one with — which is what keeps a program
  from discharging it.  Rename it.  MANUAL § 8.
```

That is `World`'s argument, made once for both: the wire whose carrier
lives in the compiler's `@` namespace is discharged by the **host**, and
here the host is the loader — it holds the dictionary, hands it to each
declaration word in turn, and turns what comes back into a module.
`:doc Dict` prints all of this, including the two words it deliberately
has not got.

**`theory` / `model`** — named slots, models, and laws that run.
Both are **block** declarations: a header line ending in `=`, then
indented lines, the same shape as `def name =` with an indented body. A
theory's entries are `slot : Σ ⇒ Θ` and `law name = <program>`; a
model's are `slot = <program>`, and a model has the **inline** form too
— `model Ints in Ring(Int) = add = +, mul = *` — exactly as `def` has
both. `;` NEVER separates two of them: it composes, so the separator is
a comma on one line and a newline in a block, and the `;` inside `mul =
dup ; *` is the body's own composition (balanced brackets make that
exact). Writing one is refused by name:

```text
`;` composes; separate bindings with `,` or a newline
```

One rule for models, transformations and theories alike. Theory parameters are kinded: a bare
name is one wire, `...` a stack, and `k(..., ...)` a type **constructor**
whose arguments are kinded one by one (below).

**THE MODEL HEAD IS ONE GRAMMAR** *(2026-09-17)*, and every kind of
model is a setting of it:

```text
model NAME [ ( PARAM ) ] in THEORY [ ( ARGS ) ] [ ( A ↦ B via c [, r] ) ] = BINDINGS
```

Three optional clauses around one required one. `( PARAM )` names the
theory an argument model must model, and makes this head a **family**
(`model Fwd(Smooth(a, _)) in Smooth(Dual(a), a)`, applied by `with
Fwd(Floats)`). `( ARGS )` are the theory's arguments. `( A ↦ B via c )`
is the **object map** (below). The two parenthesized clauses after the
theory are told apart by **content and not by position** — a group
containing `↦` is the object map, and there is nothing to disambiguate
because a type expression never contains `↦`.

| the head | the model it declares |
|---|---|
| `model IntSum in Monoid(Int)` | a plain model: object map = the theory's parameters at this model's arguments |
| `model Circuits in Arrow(Circuit)` | a Doctrine model: identity on base types, with `embed` total |
| `model Fwd(Smooth(a, _)) in Smooth(Dual(a), a)` | a family: object map = a substitution driven by the parameter |
| `model Opt in Base` | a model of the ambient presentation: identity object map, partial table |
| `model Mod in Base(Int ↦ Mod7 via reduce)` | ...the same, with a **written** object map |

They are one record (`Instance`) and one parser (`parseModelHead`).
Combinations that mean nothing are refused by name — an object map on a
model of a theory is *an object map is a `Base` model's clause*, because
such a model already maps objects; a model parameter on a model of
`Base` is refused because `Base` has no theory for an argument to model.

```braid
theory Monoid(a) =
    unit   : • ⇒ a
    op     : a a ⇒ a
    sample : • ⇒ a
    law leftUnit = (sample ; unit ... ; op) sample ; eq? ; (forget ; true | forget ; false) ; merge

model IntSum in Monoid(Int) =
    unit   = 0
    op     = +
    sample = 7

model StrCat in Monoid(Str) =
    unit   = ""
    op     = cat
    sample = "x"

def total  with IntSum = [op] unit ... ; foldExp     # Intⁿ⁰ =IntSum> Int
def joined with StrCat = [op] unit ... ; foldExp     # Strⁿ⁰ =StrCat> Str
```

**These are not typeclasses.** Nothing is inferred and nothing is
dispatched: `with IntSum` (§6) selects a model **by name**, and the
selection is a *renaming at elaboration* — each slot resolves to a
generated def, so resolution costs nothing per call, once per scope.
The trade is deliberate (`design-effects.md`): you give up inferring
*which* model, and get annotation-freeness, coherence in a
structural type system, and no need for higher kinds.

**Slot-local variables** (2026-09-09). A slot may name type variables
the theory does not declare, and each slot is **generalized over its
own**: they are quantified per slot, not shared between slots, and the
model's body must be at least as general as the result. Any
lowercase name that is neither a theory parameter nor a type in scope
is such a variable, and a `...` in a slot of a theory with no stack
parameter is a slot-local *stack*. So `box : b ⇒ a` in `theory
Wrap(a)` declares `∀b. b ⇒ a`, and a model filling it with
`_ 1 ; + ; toStr` is refused:

```text
model W in slot 'box' is Int ⇒ Str but theory Wrap declares a0 ⇒ Str
('b' is universally quantified in the expected type but this code
requires it to be Int — the expected type promises the code works for
every choice of 'b', so it must stay parametric in it)
```

Nothing in the checker changed for this: `declaredSlots` already
generalized a slot's arrow and `checkInstance` already compared bodies
to it by **subsumption**, so the variables only had to survive the
parser.

**Constructor parameters** (2026-09-09; kinded per argument
2026-09-16). A theory parameter may be a type constructor, written with
its arity visible as one mark per argument — `_` for a wire, `...` for a
whole stack, so `theory Arrow(k(..., ...))` and `theory Prob(k(..., ...),
d(_))`. The kind must be visible because the two bare readings are
already taken (a name is a wire, `...` is a stack), and a kind that is
invisible is a kind that is guessed. Slots then apply it, and a
lowercase name standing in a `...` position **is a stack variable** —
the kind is declared once, at the head, and read off here:

```braid
data Circuit(a..., b...) = Fn⟨Box(a) =Recursive> Box(b) Circuit(a, b)⟩

theory Arrow(k(..., ...)) =
    arrP    : Fn⟨a ⇒ b⟩ =Recursive> k(a, b)
    thenP   : k(a, b) k(b, c) =Recursive> k(a, c)
    …

model Circuits in Arrow(Circuit) =
    arrP    = arrC
    …
```

The model head names a **declared data type**, not a type
expression, and that name is substituted for `k` before any slot is
forward-declared or checked. So `k` is not a higher-kinded type
variable and inference never meets one — this is the ML-functor move,
and `Ty` still has no constructor variable. The slots come out as
ordinary types:

```text
braid> with Circuits
ambient: with Circuits   (:clear or a bare `with` to leave)
braid> :t arrP
arrP : Fn⟨ρ0 ⇒ ρ1⟩ =Recursive> Circuit(ρ0, ρ1)
braid> :t thenP
thenP : Circuit(ρ0, ρ1) Circuit(ρ1, ρ2) =Recursive> Circuit(ρ0, ρ2)
braid> with Funcs
ambient: with Funcs   (:clear or a bare `with` to leave)
braid> :t thenP
thenP : Arr(ρ0, ρ1) Arr(ρ1, ρ2) ⇒ Arr(ρ0, ρ2)
```

The slots carry `=Recursive>` because the `Circuit` model builds every
circuit under `with Recursive`; the function model does not, and a pure body under
a `=Recursive>` slot passes by absorption — which is why `Funcs`'s `thenP`
comes back bare. A slot declares the *most* a model may do, as ever.
What `arrP` does **not** ask for is a recursive *argument*: composition
joins (§3), so a knot-built embedding takes an ordinary
`Fn⟨a ⇒ b⟩`. It read `Fn⟨a =Recursive> b⟩` until 2026-09-12, and that was the
grade system unifying where it should join (§14).

A slot is reached **through its scope, or not at all**: the compiler's
own spelling for the generated def is `Circuits@arrP`, and writing an
`@` yourself is an elaboration error (§12).


Five things are refused, each naming what is wrong:

```text
theory T(k(_, _)) =  op : k ⇒ k
  Type parameter k is a type constructor of arity 2: it is not a wire,
  write it applied — k(_, _)

theory T(k(_, _)) =  op : k(a) ⇒ k(a)
  Type constructor parameter 'k' takes 2 argument(s), but was given 1

model Bad in Arrow(Nope)
  model Bad in theory Arrow declares 'k' as a type constructor of
  arity 2, so its argument names a declared data type; 'Nope' is not one

model Bad in Arrow(One)          # data One(a) = a
  model Bad in theory Arrow declares 'k' with arity 2, but One takes
  1 argument(s)

model Bad in Arrow(T)            # theory Arrow(k(..., ...)), data T(a, b)
  model Bad: T cannot fill the constructor parameter 'k' — theory Arrow
  declares it at k(..., ...), so T's parameters must be declared `...`
  (a stack) where that says `...`
```

`Fn` cannot fill a constructor parameter: it is built in and takes an
arrow rather than wires, and the refusal says so and suggests the
one-line wrapper (`data Arr(a, b) = Fn⟨a ⇒ b⟩`) that makes plain
functions a model. `examples/circuits.braid` declares the Arrow
interface once and audits both models — circuits and functions —
against the doctrine's five runnable laws.

**A model is audited, three ways**, each with its own message:

| check | example message |
|---|---|
| slot signatures, read at the model's argument | `model Bad in slot 'unit' is • ⇒ Str but theory Monoid declares • ⇒ Int` |
| completeness, and no extras | `model Partial in no binding for 'op' (declared by theory Monoid)` · `model Extra: 'huh' is not an operation of theory Monoid` |
| a law is a program `• ⇒ Bool` | `law 'silly' of I must be a program with type '• ⇒ Bool', but is • ⇒ Int` |

…and a **family** is audited once per member, at the member's own
evidence (below).

**Laws run.** They are ordinary Braid programs, and they execute **at
module start, before main**. A failing one rejects the module:

```text
law 'leftUnit' fails for model BadUnit in a model must be an
audited model of its theory
```

`theory` and `model` are file declarations, not REPL lines (the
REPL says so). See `examples/theories.braid`, §14 for the limits, and
`design-effects.md` for the position.

**A model parameterized by a model** *(2026-09-15)*. A model head takes
an optional **parameter list**, and a model that has one is not a model
at all — it is a **family**:

```braid
data Dual(a) = a a

model Fwd(Smooth(a, g)) in Smooth(Dual(a), a) =
    add = Dual(x, dx) Dual(y, dy) -> (x y ; add) (dx dy ; add) ; Dual
    lit = (c -> (c ; lit) (0.0 ; lit) ; Dual)
    …
```

Read it as a **functor Mod(Smooth) → Mod(Smooth)**: a map from models of
a theory to models of a theory, which is what an ML higher-order functor
is, what Kiselyov calls an interpreter transformer, and what the ring
construction R ↦ R[ε]/ε² is. `examples/autodiff.braid` is the case
worth having: `Fwd` is forward-mode differentiation, so applying it
twice differentiates twice.

**`with Fwd(Floats)` applies it**, and that is the one spelling. The
application is also the **name** of the model it mints — an ordinary
model, with ordinary slot defs, whose laws run at module start like any
other's. That is why the spelling is an application and not a scope
stack (`with Floats Fwd`): a `transformation` names a model, a receipt
prints one, and only the applied form is a name that can be written in
both places. `Fwd(Floats)` is minted once per module however many
headers ask for it, and

```braid
def polyDD with Fwd(Fwd(Floats)) = poly
#   polyDD : Dual(Dual(Float)) =Fwd(Fwd(Floats))> Dual(Dual(Float))
```

iterates: a family may be applied to a member of itself.

**The receipt is the whole application, as one label.** `with Fwd(Floats)`
mints `Fwd(Floats)` and not `Fwd` and `Floats`: a receipt says *which
model read the template*, one model did, and `Floats` never saw it. A
grade is a set of labels, and this contributes one.

**The carrier is substitution, never a type-level function.** The
parameter clause `Smooth(a, _)` **binds a name to each of the
argument model's own theory arguments**, and the head writes its own in
terms of them. At `Fwd(Floats)`, `Floats : Smooth(Float, Float)` gives
`a := Float` and the head reads `Smooth(Dual(Float), Float)`; at
`Fwd(Fwd(Floats))` it gives `a := Dual(Float)` and reads
`Smooth(Dual(Dual(Float)), Dual(Float))`. Nothing is applied at the type
level; a name is replaced.

**A family's slot bodies are templates over the PARAMETER's theory.**
Inside a body every theory name is the argument model's — including the
name of the slot being defined, which is *not* in scope in its own
body. That is why the head needs no name for the parameter and does not
have one: a body reaches the parameter's slots by the theory's names,
and `_` fills a binder the head does not use. So `add = …
add …` is unambiguous with no rule to learn, and `lit = (c -> (c ; lit)
(0.0 ; lit) ; Dual)` reads exactly as it looks: R's `lit` twice. (The
zero tangent is `0.0 ; lit` rather than a new `zero` slot because the
theory already names its zero and `law addUnit` already pins it — one
spelling per thing.)

**Laws are checked at each instantiation, not once for the family.**
Checking them generically would need equality modulo the parameter
theory's laws, and there is no such thing here. So every member runs the
theory's laws on **its own evidence**, and a false family is refused at
its **first instantiation**, naming the member — which names the family
and the argument at once:

```text
law 'mulAssoc' fails for model Fwd(Floats): a model must be an audited
model of its theory  (a model PARAMETERIZED by a model cannot be
audited once for the family … so its laws are checked AT EACH
INSTANTIATION, on that member's own evidence, and this is the first
one that named it)
```

**One parameter, for now.** Two would give one slot name two meanings
inside a body, since a body is written in the parameter's vocabulary;
the head says so rather than guessing. (This is also why the parameter
has no name: with one parameter there is nothing to disambiguate.)

**`:defs` lists a family** with the spelling that applies it, and
`:import` counts it apart from the models (`5 models, 1 parameterized
model`): a family is not a model and not a def.

**The head is a sequence of optional clauses.** Today:

```text
model NAME [ ( Theory(binders) ) ] in THEORY [ ( args ) ]
```

and a third clause is coming — an **object map**, `model FwdAD in Base(Float
↦ Dual)`, a functor given on generators with a substitution on types.
The general form the two collapse into: *a model is a presentation
interpreted in a category, given by an object map and an image for each
generator.* Today's `Base` models are the identity-object-map case with
an explicit generator table; doctrine models are the identity on base
types with `embed` total; a parameterized model is a type-level
**substitution** with generator images written over the parameter's
words. See `design-macros.md` (2026-09-15).

### `in T`: a template — a def written over a theory

A def whose header is **`in T`** for a theory `T` is a *template*: it
is a morphism of `T`, its body waits for a model, and it is not a
def at all until one arrives. A def whose `with` header names an
**model** supplies one — every template it calls is expanded there,
renamed by that model, and **re-inferred there**:

```braid
def fold1 in Monoid = [op] unit ... ; foldExp  # a template over Monoid

def total  with IntSum = fold1                   # instantiates it
def joined with StrCat = fold1                   # and again, elsewhere
```

Because each instantiation is inferred on its own, each gets its own
**principal type** — there is no rank-1 wall, and nothing is passed at
run time:

```text
braid> :t total
total : Intⁿ⁰ =IntSum> Int
braid> :t joined
joined : Strⁿ⁰ =StrCat> Str
braid> with IntSum
ambient: with IntSum   (:clear or a bare `with` to leave)
braid> :t fold1
fold1 : Intⁿ⁰ =IntSum> Int
braid> with StrCat
ambient: with StrCat   (:clear or a bare `with` to leave)
braid> :t fold1
fold1 : Strⁿ⁰ =StrCat> Str
```

The `in Monoid` on `fold1` mints nothing — it applied nothing. The
label on each instantiation is the `with IntSum` / `with StrCat` that
read the template.

This is ML's functor application performed by the mechanism that
already existed: `with Inst` is a renaming, and a template is a body
that waits for one. There is no new syntax, no parameter list, and no
`@`.

**The rules, each with its message.** A template is *recorded*, not
defined: it never enters the environment or the runtime scope, because
it has no body that runs before a model says what its slots mean.
So calling one outside every model scope of its theory is an
elaboration error that names the **theory**, not a missing word:

```text
fold1 needs a model of Monoid in scope (`with <model>` before
calling it)
```

A model of the *wrong* theory in scope gives the same message —
scope selection is by theory, and nothing is searched for. Templates
may call templates (`examples/build.braid`), and the instantiating
scope instantiates the whole chain. Nested scopes resolve
**innermost-first**, which is what renaming already did. Four more
refusals:

```text
def f with Monoid = op
  `with Monoid` names a theory: `with` applies a functor, and a theory is
  not one — write `in Monoid` to make this def a template

def f =
    1
    over Monoid
    op
  `over` is gone since 2026-09-16: saying what a def is a morphism of
  is a def's HEADER CLAUSE, not a stage — write `def <name> in <X> = …`
  (MANUAL §8)

def f in Monoid Pointed = op
  `in Monoid Pointed`: a def is ONE thing, so `in` names exactly one
  theory (making this def a template) or one model with a carrier
  (making it a word of that category).  `with` is the clause that takes
  a list.

def loopy in Monoid = dup ; op ; loopy
  template loopy calls itself: a template is expanded at the call, so it
  cannot recurse
```

The last of those is reported where the template is *instantiated*, not
where it is written: a template's body is stored unexpanded, so the
no-self-reference rule above meets it only when a `with <model>`
scope inlines it.

The other clause survives, so `def f in Monoid with Log = …` is a
template that also threads a resource; the resource is routed where the
template *lands*, not where it was written.

**`in` also decides instantiate against transport** *(2026-09-16)*.
When `with M` names a model of a **Doctrine** theory (below), there are
two things it could mean and the `in` clause says which:

| the def | `with M` does | because |
|---|---|---|
| `def f in T with M = …`, T = M's theory | **instantiates**: M's words replace the slot names and the spine stays BASE composition | the body is already a morphism of `B[T]`, and a morphism of `B[T]` composes like the base |
| `def f with M = …`, no `in` | **transports**: every stage becomes `embed` of itself and every `;` becomes `compose` | the body is a base program, and M is the functor that carries it in |

Never both — transporting a template would embed the expansion's own
`embed` and `compose`. That is why a template over a Doctrine theory is
writable at all:

```braid
def bothFlip in Prob = ([swap] ; embed) (flip ; under) ; compose ; …
def bothFlipE in Prob with Enum = bothFlip   # instantiated, not transported
```

The two readings are **different programs with different types**, and
both are legal. Under `Enum` (`examples/prob.braid`):

```text
def a with Enum = half ; flip ; dup      # a0 =Enum Recursive> Bool Bool
def b in Enum   = flip ; dup             # • =Recursive> Kern(Float, Bool) Kern(Float, Bool)
```

`a` is the Markov copy — one flip, copied, so HH and TT at ½ each. `b`
is two kernel *values* side by side, which is not a kernel at all. `in`
is what tells them apart.

**`in` with a `with` of the same model is the mixed case**, and it is
allowed: `def mixed in Funcs with Funcs = sample ; (x -> x 2 ; *)`
puts `Funcs`' own words inline *and* transports the base stages around
them.

**`in Recursive` is refused.** `Recursive` is applied, not lived in:

```text
`Recursive` is applied, not lived in: write `with Recursive`; the
open-recursion body is `fix` by hand (MANUAL §8)
```

`with Recursive` is `in B[f]` plus the knot model, where `B[f]` is the
base extended by the def's own name — a one-slot theory per def whose
slot type is inferred. `in Recursive` would be the *open*-recursion
half of that: a body written over the slot, with no knot tied. Writing
it by hand is `fix`, which is what the marker rewrites to anyway.

**A template is over a theory, never over a resource name.** A resource
scope is *routing* — the offsets come from the header's arity — so a
body waiting for a resource would be waiting for an arity rather than
for a name; and the operations a generic handler needs (a seed, an
unroller) are per-carrier words, which is exactly what a theory names.
`examples/resources.braid` writes the generic handler that way, and it
is two lines per resource.

**Not "functors".** Templates are model-parameterized *defs*;
`functor` (below) is the macro keyword, and for Haskell readers neither
is `Functor`/`fmap`.

**`functor Name = <graph morphism>`** *(retyped 2026-09-18)* names a
**functor**, and takes a **graph morphism**: a program whose type is
`• ⇒ Fn⟨Stage ⇒ Code⟩` at pure grade — one image per generator. A
functor out of a FREE category *is* a graph morphism, so one image per
generator determines the whole functor by the universal property; that
is why the declaration needs nothing but this, and why it is functorial
rather than merely claimed to be.

```braid
functor Traced = [(s -> (s ; pack) (s ; markStage) ; append)]
functor Ticked = tick ... ; interpose
```

`with Traced` then extends the morphism along the scope's whole spine
at elaboration and splices the result back. The **extension is also a
word** of the functor's own name — `Traced : Code ⇒ Code` — so the same
functor is a value: `[Traced]` is a quote and `lift2 [Traced]` applies
it at run time. There is no `macro` keyword and nothing to register.

The morphism is checked at the first `with` (declarations are hoisted,
so that is where the prefix scope is what it will be at run time), and
once at its declaration whether or not anything applies it: *must be a
GRAPH MORPHISM* — with the arrow it actually has, named; *must be pure*
(it runs while the module is being checked, so it cannot do IO — the
`IO` label IS the phase distinction; other labels on it are harmless);
*must be defined before the functor line* (a functor is runnable before
its first use: the one place source order is semantic); and a looping
functor exhausts a step budget rather than hanging the compiler.

**A `Code ⇒ Code` word may not head a `with`** *(2026-09-18)*, and is
refused by name. Such a word is an endomap of the *object of
morphisms*: it has no object map, no generator images and no laws, and
nothing about it makes it commute with `;`. It has two homes, and the
refusal names both — `lift2 [w]` applies it at RUNTIME, checked per
program against the program's own type with the original as the
fallback; and a top-level declaration program (`[code] "name" ; defW`,
§12) DECLARES what it generates, for code that is generated rather than
rewritten. **Nothing is lost**: between them those two cover every use
the whole-spine scope had.

Not Haskell's `Functor`: nothing is dispatched on a type; this is a
functor out of the free category of programs, selected by name. §12 has
what a functor may and may not do; `examples/traced.braid` and
`metered.braid` are the two idioms, and `examples/optimizer.braid`
states the functor laws as theories.

**`model Name in Base = p = q, r = s`** *(2026-09-13)* is a **partial
model of the ambient presentation**. `Base` is the reserved theory
whose generators are *every word in scope*, each with its own scheme as
the slot's declared type; a binding gives a generator an image, and
every generator it does not name maps to itself. It is the same
declaration in a block, one binding per indented line, exactly as every
other model body has both forms:

```braid
model Opt in Base = dupInt = dup, twice = double

model Opt in Base
    dupInt = dup
    twice  = double
```

`with Opt` is then the renaming every `with Inst` performs — it descends
into quotations (so a knot body is rewritten where it lives), into a
row's tracks, into a residual row's written tracks, and into groups —
and mints `=Opt>` on everything it renamed, like any other scope. The
declaration also produces a **word** `Opt : Code ⇒ Code` (the table,
handed to the `rewrite` engine), so `lift2 [Opt]` applies the same
reinterpretation at run time with the program as its own fallback
(§12).

There is no separate machinery and no separate keyword: a rewriting of
the base *is* a model, a by-generators functor whose action on a
generator is a rename and whose action on everything else is
congruence. The keyword `rules` is gone:

```text
`rules` is gone: a rule set is a PARTIAL MODEL of the ambient
presentation, so it is written `model Name in Base = p = q, …` (or
one `p = q` per indented line).  MANUAL §8.
```

**Optimizer or dialect.** A model of `Base` whose images are
*provably equal* to the generators (`sameCode`, §12) is an
**optimizer**; one whose images merely satisfy the theory's laws is a
**reinterpretation** — a dialect. Both are models of `Base`, and the
distinction is semantic, not syntactic: `examples/optimizer.braid`
draws the line explicitly, two of its four bindings on each side.

`Base` itself may not be declared — its generators are not something a
user writes down (*`Base` is the ambient presentation and may not be
declared*).

**Why a declaration and not a type.** A word `replace : Fn⟨a ⇒ b⟩
Fn⟨a ⇒ b⟩ Code ⇒ Code` types — but its shared variables are
**unification**, "p and q have a common model", and that is
symmetric, while "q may stand wherever p stands" is not. The property
that *is* sufficient is `scheme(q) ≥ scheme(p)`, a rank-2 statement no
rank-1 `Fn` can hold. The routine that states it already exists, with
three other consumers (`checkInstance`, `runAs`, `interpose`):
`subsumes`. So a binding is checked **once**, where it is written, and
is free at every use — which is exactly what `checkInstance` has always
done to a slot:

> *Unification blesses a call; subsumption blesses a rule.*

Direction matters: a binding may only **generalize**, never narrow.

```text
model Bad in Base: `dup = dupInt` is refused: dup is used at a0 ⇒ a0
a0 but dupInt is Int ⇒ Int Int ('a0' is universally quantified in the
expected type but this code requires it to be Int — …).  A binding may
only GENERALIZE — the image's scheme must be at least as general as the
generator's type, or a program that typed before the reinterpretation
would not type after it.
```

The parametricity case is the one worth staring at. With `two : a ⇒ Int
Int`, `two = dup` would *run* perfectly well wherever it fired — and it
narrows `a ⇒ Int Int` to `Int ⇒ Int Int` everywhere else, so it is
refused: *two is used at a0 ⇒ Int Int but dup is a0 ⇒ a0 a0*.

**Grades ride along** for free, because `subsumes` compares them by ⊆
and `∅` is the bottom of the semilattice: a **pure** image under an
**io** generator passes (the reinterpretation can only remove effects),
and an io image under a pure generator is refused — *Cannot unify
effects: IO vs pure (the expected type fixes the grade; this code must
stay pure)*.

**What may not be a binding's side.** A theory **slot** (*a slot is not
a word outside `with`*), a name containing `@` (*the compiler's spelling
of a slot*), a **theory** name, a **template** (it has no type until an
model supplies one, and a binding is checked once), or a word not yet
defined. Models and functors share one namespace — every name
a `with` header may carry — so `model Opt in Base` beside `functor Opt
= …` is a *Duplicate model declaration*.

**v1 bindings are single words on both sides.** Multi-atom patterns —
`dup ; * = square` — are **not shipped**: they need a matcher over
spines and a story about what a pattern variable is, and no example has
asked for one yet. The engine itself is exposed as the unchecked prim
`rewrite : List(Sym) List(Sym) Code ⇒ Code`, the same way `interposeRaw`
is the unchecked half of `interpose`; nothing blesses a table you build
by hand, which is exactly why `lift2`'s fallback exists.

`examples/optimizer.braid` is the worked example: four interchangeable
words, a model of `Base`, the two bindings `sameCode` can prove and
the two it honestly cannot, the receipt on the arrow, the laws as
theories, and image membership.

### A model with an OBJECT MAP — `model Mod in Base(Int ↦ Mod7 via reduce)` *(2026-09-17)*

A model is **a presentation interpreted in a category, given by an
object map and an image for each generator**, and everything above
carried the *identity* object map: `with Opt` renames words and the
wires keep their types. The head's third clause writes the other half.

```braid
data Mod7 = Int
def reduce = (x -> x 7 ; mod ; Mod7)

model Mod in Base(Int ↦ Mod7 via reduce) =
    + = addM
    * = mulM
    - = subM
```

**The map.** `Int ↦ Mod7` is the **substitution** `Int := Mod7`,
applied structurally — under `List`, under a data type's arguments,
through an `Fn` arrow, along a stack. It is a substitution and *not* a
type-level function, which is the whole reason it is principal:
substitution commutes with unification, so a transported program has a
principal type for the same reason the original did. `↦` is the glyph,
and it is deliberately not `⇒`: `⇒` is the arrow of every **written
type**, and an object map is not a type but a function on objects.

The source `A` is a **nominal** name — a base type, or a `data`/`type`
name of arity zero. A parameterized source would make the map a
type-level function (what is `List(a) ↦ …` at an unknown `a`?), and it
is refused.

**`via c` is the image of the LITERAL FAMILY.** Every literal of the
mapped type is a generator; there are infinitely many of them and none
of them is a word, so a table cannot name them and the head does. Under
`with Mod`, `3` elaborates to `3 ; reduce`. This is not a detail: in
`examples/modular.braid` §7 a floor-halving map sends `3` to `1` and
the transported polynomial computes something the untransported one
never did, which is exactly what a functor on the whole presentation
means.

When `A` is **nominal** there are no literals of it at all, and `c` is
then the map on *values* — what the conjugation below coerces with. It
is still required, and still checked at `A ⇒ B`: an object map with no
way from `A` to `B` is not one.

**The table.** Each image is checked by subsumption at the generator's
scheme **with the substitution applied** — `+ : Int Int ⇒ Int` is
checked at `Mod7 Mod7 ⇒ Mod7` — by the same `subsumes` that blesses
every other binding, so an image may only generalize. Any word may
appear, because `Base`'s generators are every word in scope.

Images here are **programs**, not single words, and the reason is the
same one that makes them single words above: a model of `Base` with the
identity map also declares a `Code ⇒ Code` word, and `Code` carries
names. An object-mapped model declares **no such word** — its action on
a literal is not a rename and its action on a def is an unfolding, and a
rewrite table holds neither — so its images are ordinary programs,
inlined at each use and re-inferred where they land (each use gets its
own principal type, exactly as a template's expansion does). An image
applies nothing: `with` and `in` inside one are refused.

**The refusal is TYPE-DIRECTED.** At `with M`, each atom gets one of
five answers:

| the atom | what happens |
|---|---|
| a generator the table names | its image, inlined |
| a **literal** of `A` | `lit ; c` |
| a word whose scheme **never mentions `A`** | **unchanged** — the functor is the identity off `A`, and wiring (`dup`, `swap`, `drop`, `_`) is always in this row |
| a word that mentions `A` and **has a body** | **UNFOLDED**: `F(def) = F(body)`, transitively |
| a word that mentions `A` with neither | conjugated (below), or **refused by name** |

The third row is what makes `with M` twice the identity the second
time — after one pass there is no `A` left in any type, so nothing
mentions the mapped object — and what makes `with M` then `with N`
(for `N` mapping `B ↦ C`) compose.

The fifth is the refusal, where the scope is written:

```text
`div` has no image under model Mod: Mod maps Int ↦ Mod7, and
`div : Int Int ⇒ Int` mentions Int — so the functor has nothing to
send it to.  Add `div = …` to `model Mod`, declare a retraction
(`via reduce, r` with `r : Mod7 ⇒ Int`) so it is derived by
conjugation, or do not call it here.
```

`div` and `lt?` are *right* to be refused at Z/7 — it is neither
ordered nor of characteristic zero — but the checker does not know
that. It knows that a functor with no value on a generator is not a
functor, which is the same refusal for a better reason.

**Transitive unfolding.** A def called under the scope is transported
too, and so is everything *it* calls. Each is minted once per def per
model as a generated word `M@def` — a cache, not an inlining: one word,
one type, however many times it is called. `:defs` does not list it
(`@` is the compiler's character and you cannot name it); `:doc M@poly`
shows it. `fix` transports as **structure** — a functor of the doctrine
preserves the fixpoint, and the walk enters quotations — so a def
written under `with Recursive` comes along with no case of its own.

**Retraction and conjugation.** `via c, r` declares a retraction
`r : B ⇒ A` with `c ; r = id_A`. Where one is given, every generator the
table does not name is **derived by conjugation**: one `r` per `A` input
wire, one `c` per `A` output wire, read off the generator's own arrow
(an open arrow has no wires to count, and says so). Table entries
override. A retraction makes the **empty table total**, so this is a
complete model:

```braid
model Milli in Base(Meters ↦ Mm via toMm, toM) =
```

`Meters : Int ⇒ Meters` becomes `Meters ; toMm`, `unMeters : Meters ⇒
Int` becomes `toM ; unMeters`, and a def written over metres runs over
millimetres. Note what conjugation is *not*: `r ; c` is only an
idempotent unless `c` is an iso, so a conjugated word sees `B` only
through `c`'s image.

**Two laws, and who decides them.** A declaration like this states laws
`Base` has no samples to run: the retraction (`c ; r = id_A`) and, for
an image given to a word that **has** a body, `image = F(body)`.
`sameCode` (§12) decides both where it reaches — a proof in the free
category, for every input — and where it does not, the binding stands
and the model is recorded as a **DIALECT**. `:doc M` says which:

```text
## model Mod in Base(Int ↦ Mod7 via reduce) — + = addM, * = mulM, - = subM.
   No retraction, so every generator that mentions Int needs an image of
   its own.  An object-mapped model declares no `Code ⇒ Code` word …
```

That is the optimizer/dialect line of the previous section, drawn by
the same procedure. Refusing instead would rule out every image whose
truth is arithmetic, which is all of them.

**The receipt** is one label per model, `=Mod>`, as for a family's
application — on the def whose header named the model. The unfoldings
are its internals and carry none: a receipt is minted by a scope, and
nobody wrote one around `M@poly`.

**Map-out only is refused.** There is no `model M in Base(A ↦ B)`
without `via`, because the literals of `A` would have no image and the
map would be a claim about types with nothing behind it on values.

`examples/modular.braid` is the worked example: Z/7 by canonical
representatives, one polynomial run over two rings, `div` and `lt?`
refused by name, `transformation Reduce in Ints ⇒ Mods` audited square
by square, floor-halving as the contrast (a perfectly good object map
whose `transformation` is refused at the `add` square), and a nominal
source with a retraction and an empty table.

**An object map is a `Base` model's clause.** A model of a theory
already maps objects — by instantiating the theory's parameters at its
own arguments — and a second map at a mapped type would be a functor
into a category whose objects nobody has named. Refused for now, with
the clause to write instead; whether it means anything is the one
question this stage leaves open (`design-macros.md`, 2026-09-17).

**A model whose theory joins the DOCTRINE transports** *(2026-09-13;
it was a shape rule for half a day, and the `mode` keyword before
that; the hom-object went over STACKS 2026-09-16)*. The prelude declares
one theory every module sees:

```braid
theory Doctrine(k(..., ...)) =
    compose : k(a, b) k(b, c) ⇒ k(a, c)
    embed   : Fn⟨a ⇒ b⟩ ⇒ k(a, b)
    observe : k(Int, Int) ⇒ Int
    sample  : • ⇒ k(Int, Int)
    law leftId … rightId … assoc … embedFunctor … embedWide
```

`k(..., ...)` is the hom-object and its two arguments are **stacks**, so
`a`, `b` and `c` above name whole sides of a diagram and not single
wires. A theory **joins** it by declaring its operations, at its
signatures:

```braid
theory Arrow(k(..., ...)) in Doctrine =
    embed   : Fn⟨a ⇒ b⟩ =Recursive> k(a, b)
    compose : k(a, b) k(b, c) =Recursive> k(a, c)
    observe : k(Int, Int) =Recursive> Int
    sample  : • =Recursive> k(Int, Int)

model Circuits in Arrow(Circuit) = …

def easy    with Circuits = add1 ; dbl     # Int =Circuits Recursive> Int
def easyOut in Circuits = easy ; observe
```

`easy` elaborates to `[add1] ; embed ; _ [dbl] ; _ embed ; compose` —
which you may write by hand under `in Circuits`, and the two print
the same thing.

**`in D` in a theory head is `in` doing its one job**: declaring
membership, applying nothing, minting nothing. The elaborator *checks
the claim* — each slot whose name is one of `D`'s must be `D`'s arrow,
with `D`'s constructor parameters instantiated consistently across the
whole theory — and then it knows, without reading a shape, that `with
Circuits` transports. Deviations that are refused, each naming the
fix: a slot of a doctrine name at another signature; two slots reading
one parameter two ways; a hom-object that is not the theory's own
parameter (a model must be able to choose the carrier); an `in` that
takes none of the named theory's operations (it declared nothing);
extension of a theory that itself extends one (extension is one level
deep).

**The grade is the extending theory's.** `Doctrine`'s slots are
written pure; `Arrow`'s are `=Recursive>` because circuits are built
under `with Recursive`. Only the *stacks* are checked against the doctrine — a grade
says what a model may do, and the doctrine does not bound it.

**There is no pairing, and no strength** *(2026-09-16)*. Until that date
the Doctrine had a second constructor parameter `p(_, _)` and a slot
`first : k(a, b) ⇒ k(p(a, c), p(b, c))`, and three of its laws were about
that slot. Both existed for one reason: a hom-object that named one
WIRE per side could not hold a wide stage, so the stage had to be
*packed*. Products in Braid are flat — the stack is the product — and
the hom-object was the one place they nested. Over stacks a stage of
any width embeds as **itself**, so the packing, the parameter that named
it, the `data Pair` every model file declared to BE it, and the routing
pass that wrote it out are all gone together. `embedWide` is the law
that replaces the three: `embed [f] ; embed [g] = embed [f ; g]` at a
stage that is one wire in and two out, and at one that **whiskers** —
`(_ 1 ; +) _`, a stage on the deepest wire with one riding above. The
whiskering happens in the BASE, inside the quotation, before `embed`
sees it, so there is nothing left for a strength law to say.

**The two levels are what the theory declared.**

| declared | it licenses |
|---|---|
| `compose` | `in M ; f g ; compose` — carriers built by hand compose. `with M` is refused: *theory `Half` takes Doctrine's `compose` and not its `embed` (`Fn⟨ρ ⇒ σ⟩ ⇒ k(ρ, σ)`) … `in Half` and compose by hand.* |
| `+ embed` | `with M` transports **any** stage, at the width it is written. |

Slots that are not the doctrine's are classified exactly as 5c read
them: a slot taking the carrier and returning base is an **exit**
(refused inside `with M`, called under `in M`), one taking `•` to a
single carrier is an **entry** (already a stage of the category, left
alone). Identity is `embed [pass]` and needs no slot.

**The laws are the doctrine's, and they run.** A model is audited
against every inherited law it can *state* — every slot the law names
is one its theory declared. `Arrow` above takes all four slots, so all
five laws run, for `Circuits` and for `Funcs`, and again for
`Reified` in `examples/reified.braid`. A theory that takes `compose`
and `embed` and no evidence — `Vault`, the sealed category — runs
none, which is the honest reading of *sealed*: nothing can be observed
leaving it, the audit included. They are sampled laws (`observe` at
`sample` points); what `sameCode` can and cannot decide about them is
in §12 and in `examples/circuits.braid`'s closing comment.

This is not Braid inventing a doctrine. It is the **base's own**
structure — a Freyd category, Hughes' `arr`/`>>>` (Atkey,
*What is a categorical model of arrows?*; READING) — written down as
an ordinary theory, so that "a target must have the structure the
source has" is *declared and checked* rather than assumed. That is
what a functor is.

**There is no routing discipline** *(2026-09-16)*. A hom-object
`k(ρ, σ)` names a whole **stack** on each side, so a transported spine
is one carrier wire whose two objects are the base stacks themselves.
Every stage becomes `embed [stage]`, whatever it covers, and every `;`
becomes `compose`:

```braid
def sq with Circuits = dup ; *             # Int =Circuits Recursive> Int
#   with@Circuits >> [dup] >> Circuits@embed
#              >> _ [*] >> _ Circuits@embed >> Circuits@compose
```

Nothing reads an arity, nothing packs, nothing whiskers. The base
already makes every stage cover the stack it is handed — that is what
`_` and `...` are for (§4) — so the base's own widths ride through the
functor untouched, and a stage that does not cover its stack gets the
base's own refusal rather than a second one from the elaborator. A
stage with no input wire is ordinary too: `k(•, Int)` is a hom-object
between stacks, and `•` is a stack.

Until this date the paragraph above described `embed [unP … ; stage ;
P …]` whiskered by `first` once per wire riding above — sixty-nine
lines of elaborator, all of it there because the carrier was one wire.

**A model may still declare a strength, and one does.** A base stage
whiskers in the base, but a **generator** does not: an entry slot like
`examples/prob.braid`'s `flip : • ⇒ k(Float, Bool)` is a carrier at a
fixed width, and nothing in the base can widen a carrier. A Markov
category is exactly a theory with such generators, so `Prob` declares
the widening itself, as an ordinary slot of its own:

```braid
under : k(a, b) =Recursive> k(c a, c b)
```

One wire `c` rides **under** the kernel's domain. There is no pairing
in that signature and nothing to unpack: over stacks the strength is
whiskering, and whiskering is concatenation. `c` is a wire rather than a
stack because a stack variable can only sit in tail position — `c a` is
spellable and `a c` is a splice — which is the rule every declaration in
the language obeys (§5). `under` is not a doctrine slot, so it is
available under `in M` and ignored by transport, exactly like any other
slot the doctrine does not name.

**`in M`: a morphism built by hand** *(2026-09-13)*. `with M`
transports a base program into the category; some morphisms of the
category are not the transport of any base program — a stateful circuit
is the whole reason Arrows exist — and before this they were stranded,
because treating a def as a word of `M` on the evidence of its inferred
type is the sharpest edge in the language. `in M` is the written
declaration instead:

```braid
def sum0 in Circuits = 0 ; sumFrom      # • =Recursive> Circuit(Int, Int)
def running with Circuits = sum0 ; dbl     # Int =Circuits Recursive> Int
```

`in M` opens M's **vocabulary** — its slot words are in scope — and
applies nothing. What the def *is* then follows from its arrow: one
that builds **one carrier out of nothing**, `• ⇒ Circuit(a, b)`, is a
morphism of the category and joins M's word table, so `with M` leaves it
alone and composes it exactly like a transported one; one that does not
is an ordinary base word written in M's words — an observation, a
runner, a composite that exits. The *written header* is what makes the
question askable at all: a def with no header that happens to produce a
carrier is still not a word of M, so no inferred type is ever scanned
for membership. A header that does neither — no carrier, and none of
M's words used — is refused, because it did nothing.

`in M` **mints nothing**, so a hand-built word prints as the carrier
it is, *unfolded*. That is the honest reading and it is the difference
the receipt exists to record: `=Circuits>` says *this code went through
the functor*, and `sum0` did not — claiming the label would claim
membership in the functor's **image**, which is strictly stronger.
Membership is carried by the carrier in the type and the entry in the
word table; the composite `running`, which *was* transported, carries
the label and folds.

**A transporting model declares a word of its own name** as well, so
`[Circuits]` is an ordinary quote and `lift2 [Circuits]` applies the
functor at run time. (It will always fall back: transport changes the
program's type, and `lift2`'s witness is the program itself.) The word
seeds with an identity carrier where the scope does not, which `leftId`
is the law for. It embeds one stage at a time at one wire — all a
`Code ⇒ Code` word can promise without the widths the scope reads.

**Sealed categories, for free.** A theory that declares no exit cannot
be left: every stage is embedded and the only word that touches the
accumulated carrier is the composition, which returns one. Code written
in such a category can be consumed only by more code in it —
abstract-type sealing falling out of the exit rule rather than being a
feature. The honest limit: the carrier's own generated unroller is an
ordinary base word and Braid has no export lists, so a model seals the
*category*, not the *type*. `examples/circuits.braid` has both halves.

Errors, at the `theory` line, the `model` line or the `with`: *slot
`compose` is … but Doctrine declares it …*; *`in Doctrine` declares
nothing*; *theory `T`'s constructor parameter `k` is `k(_, _)`, and
Doctrine declares the hom-object `k(..., ...)`*; *Duplicate model
declaration*; *a header may name at most one category*; and, inside a
scope, *`observe` leaves `Circuits`* and *`f` is a word of `Other`, so
it builds a carrier rather than being a program `embed` could embed*.
A stage that does not cover the stack it is handed is refused by
inference, in the base's own words, because that is what it is.

**`transformation Len in ListMonoid ⇒ IntSum = len`** *(2026-09-13,
shipped; spelled `morphism` until 2026-09-14, and `:` in place of `in`
until 2026-09-16 — a transformation's head says which hom-set of
Mod(T) it is a member of, which is membership, and `:` types a slot and
nothing else)*.
Two models of **one** theory, and a base word between their carriers.
Its components are a **list**, so `,` separates them: `transformation
Value in Fwd(Floats) ⇒ Floats = value, zeroTangent`, one word per
theory parameter in order.
The claim is that the word is a **homomorphism**: for every slot
`s : Σ ⇒ Θ`, the square

```text
A@s ; K(Θ)   =   K(Σ) ; B@s
```

commutes, where `K` at a stack is the component **on each wire that is
the theory's parameter** and the identity on the rest — monoidal, so at
`a a` it is `len len`. Because the base is the **free** category on the
theory's generators, one square per generator is complete: the squares
for composites paste from the squares for generators. The arrow is `⇒`
because that is the arrow of every written type in Braid; `->` is only
its ASCII synonym there.

**Why `transformation`** *(2026-09-14)*. Two models of one theory are
two functors out of the presented category, and a map between them with
one component per object and a commuting square per generator is a
**natural transformation** between those functors — the generated
squares are naturality squares. `morphism` was correct only as "a
morphism in the category of models", which is underspecified. "Natural"
is implied: there is no other kind here, and the checker enforces it.
For an algebraic theory the same thing is a homomorphism of models; for
a theory over the `Doctrine` it is also an internal functor. The old
keyword is refused with a pointer to the new one, as `instance` and
`mode` are.

The declaration generates the squares and **decides** them, one of two
ways:

- **Proved** by `sameCode`, for every input and every interpretation of
  the words — which reaches as far as the normalizer does. A square
  that only passes the witness through is proved outright: `embed` and
  `sample` in `Forget`, in `examples/transformations.braid`. One that
  *applies* the witness is not, because a hom-object over stacks pins
  its `Fn⟨ρ ⇒ σ⟩` to a whole stack per side and `ev` of an open wire has
  no closed arity — which is where `compose` and `observe` go to the
  samples, and it is the same wall `Len` stands at. Before 2026-09-16
  the hom-object named one wire per side and all five proved; that is
  what flat products cost, said out loud.
- **Sampled**, at the theory's own evidence, when it is not: `sample`
  supplies the inputs, an exit observes a result that is a carrier (a
  carrier cannot be compared), `eq?` decides, and the check runs at
  module start beside the model laws. `Len` above is this case — `len`
  is a fold, and a fold applies its handler.

A square that neither proves nor samples is **refused**, naming the
slot and the reason: *the square for slot 'op' does not decide —
`sameCode` cannot prove it (ev of an open wire), and it cannot be
sampled: the theory declares no `sample : • ⇒ a` to supply its inputs
with. Add a `sample` slot to theory Mag, or state the square as a law of
the theory.* A square that runs and comes out false names the slot too:
*the square for slot 'unit' does not commute at the theory's samples*.

**`false` and a refusal are two answers, and both go to the evidence**
*(2026-09-14)*. `sameCode` answering **false** means *different as
programs of the free category*, which is a real answer about the free
category and **not** an answer about the model: the model's words
satisfy the theory's laws, and the normalizer has none of them.
`Transpose`'s five sampled squares are exactly that case — the two sides
are equal only up to the arithmetic of `fadd` and `fmul`, which are
uninterpreted here. So a square the normalizer decided false is sampled,
like a square it refused; a square it decided **false with no evidence
behind it** is refused as WRONG, naming the slot: *the square for slot
'pick' is FALSE — `sameCode` decides the two sides are different
programs of the free category, and there is no evidence that could say
otherwise*.

**The exit is applied whatever the parameter's kind** *(2026-09-14)*.
A sampled square compares two results, and when the result is the
carrier it compares them **through the theory's exit** — the slot
taking one carrier and handing back base. Until this date that was done
only for a hom-object parameter; a **wire** parameter was compared
directly, on the reasoning that `eq?` reaches an ordinary type. It
does — but an ordinary type may HOLD a quotation
(`data Rev = Float Fn⟨Float ⇒ Grad⟩`), and `eq?` on a quotation is
syntactic, so two extensionally equal continuations built by different
code answer `false` and a square that commutes is reported as not
commuting. `examples/autodiff.braid`'s `transformation Transpose in Fwd ⇒ Rev`
is the declaration that was refused that way and is declared now. Two
consequences, both worth knowing before declaring one:

- **A theory with no exit still compares carriers directly** — there is
  nothing else to compare them with — and a failure says so: *the two
  carriers were compared with `eq?` directly, since the theory declares
  no exit: if the carrier holds a function, `eq?` is syntactic —
  declare an exit `observe` in the theory*.
- **A sampled square establishes its claim AT THE EXIT.** `Transpose`'s
  exit is the value, so what its five sampled squares check is that
  forward and reverse agree on the value; the gradient is read by a
  word outside the theory (the exit problem, below).

**A square the normalizer PROVED is not sampled again** *(2026-09-14)*.
The sampled law is generated before the verdict is in, so a proved
square used to run one too — harmlessly, until the exit change gave a
strength slot (whose output is the hom-object at a *wider* pair of
stacks, which no exit fits) a law that weighed two carriers. Proof
outranks evidence.

**`:transformations`** lists every transformation in scope — own and
imported —
with the verdict on each square, read off the module rather than
decided again:

```text
braid> :transformations
Transpose : Fwd ⇒ Rev
  add      sampled (2 points; differ in the free category)
  …
  lit      proved
```

`proved` is `sameCode`, for every input; `sampled (n points; why)` is
the theory's evidence at the n inputs `sample` supplied, and `why` is
what the normalizer said instead of *true* — either `differ in the free
category` (it decided **false**, and the model's laws are what the free
category lacks) or its refusal in a few words (`ev of an open wire`,
``` `pack` has no closed arity ```, `case split under eta`, `nested past
3 levels`). A square with no inputs and nothing to say reads just
`sampled`. `:doc <name>` puts the same verdicts on one line under the
component's type.

The component is an ordinary **word** under the transformation's own
name,
forward-declared at the type the two model heads wrote
(`List(Int) ⇒ Int`), so a def may use it wherever it sits — and then
typed like any def, which may be more general (`Len : List(a) ⇒ Int`,
since `len` counts anything). `with Len` (reading a
template through one model and landing in another) is **not** shipped:
it wants a second elaboration of the template, and nothing has asked
for it yet.

**An exit whose result varies by model is a theory parameter**
*(2026-09-14)*. An exit is a slot (`observe : a ⇒ Float`), so it has ONE
type for every model — and a gradient does not: forward mode hands back
a tangent `Float`, reverse mode a whole `Grad`. The answer is not a slot
whose type varies with the model, which is not what a slot is; it is
that the exit's **result type** is a parameter the model instantiates:

```braid
theory Smooth(a, g) =
    …
    observe  : a ⇒ Float      # the value: one type for every model
    gradient : a ⇒ g          # the result varies, so `g` is a parameter

model Floats in Smooth(Float, Float)
model Fwd in Smooth(Dual, Float)
model Rev in Smooth(Rev, Grad)
```

A wire parameter used only in an exit's output types reaches nothing
else: it is instantiated per model and that is all.

**One component per parameter** *(2026-09-14)*. A component of
`transformation T in M ⇒ N` is a word on **one** of the theory's
parameters, and `gradient : a ⇒ g` has its two ends at *different* ones
— so a square like that cannot be drawn with a single component. A
natural transformation between models of a theory with n parameters is
n components, written in the theory's order:

```braid
transformation Value in Fwd ⇒ Floats = value, zeroTangent
transformation Transpose in Fwd ⇒ Rev    = transpose, gx
```

Each is checked at the arrow the two model heads wrote for *its*
parameter (`value : Dual ⇒ Float` at `a`, `zeroTangent : Float ⇒ Float`
at `g`), and the generated squares put the right component at each
position of the slot's stacks. A parameter whose type is the same in
both models writes `id` — an ordinary word, not a keyword. Giving the
wrong number of them is *theory S has 2 parameters and a natural
transformation has ONE COMPONENT PER PARAMETER, in order*. The
transformation's own **word** is the component at the first parameter,
which is the carrier.

Sampling follows the parameters too: a slot's input takes its evidence
from an entry of *that* parameter (`sample : • ⇒ a` feeds an `a`), and a
result is observed by an exit of *that* parameter — `observe : a ⇒ Float`
is not an exit for a `g`, so a `Grad` result is compared with `eq?`
directly, which is sound because a `Grad` is two Floats and not a
closure.

**Evidence is a generator.** `sample` is a slot like any other, so a
transformation must preserve it: `len` of `ListMonoid`'s sample must *be*
`IntSum`'s sample. That is why the example's list has seven elements.
If that reads as strict, it is the same strictness that makes a model
an audited model — what the theory declares is what the models owe.

**A point is one choice of entry per input wire** *(2026-09-17)*. A
theory's evidence is **every** slot that builds the parameter out of
nothing — `sample`, `sample2`, `zero`, `unit`, whatever it declared —
and a slot with two inputs is run at the **cross product**: three
entries make `add : a a ⇒ a` nine points, and `:transformations` reports
the nine. The count is capped at **64 points per square**, and the cap
is said rather than silent — over it the verdict reads `sampled (64 of
169 points; …)`, so an audit never reports evidence it did not take.
Until this, a square ran at the theory's **first** nullary entry alone,
which made the audit a fact about the order the slots were *written* in:
a theory declaring `zero` before `sample` certified floor-halving as a
ring homomorphism, because ⌊(0+0)/2⌋ = ⌊0/2⌋ + ⌊0/2⌋ and nothing else
was ever looked at (`examples/modular.braid` §7).

**When both models are models of a theory extending `Doctrine`** they
are internal categories, and a transformation between them is an
**internal functor**: the squares for `compose` and `embed` are exactly
functoriality — preserves composition, preserves the image of the base.
There is no strength square, because the Doctrine has no strength.
`examples/transformations.braid` has one — a
function that carries its name, and the functor that forgets the name.

**`Fn` in declarations** — write a reified program as `Fn⟨Σ ⇒ Θ⟩`
(Unicode, mirrors `:t`) or `Fn(Σ -> Θ)` (ASCII); the inner stacks parse
like any type stack (params splice, `•` — ASCII `one`, §5 — is empty,
`Fn` nests). The arrow's shape is part of the type: `⇒` declares a **pure** program and
rejects an io quotation, `Fn⟨Σ =IO> Θ⟩` (ASCII `Fn(Σ ->! Θ)`) declares an
io one and demands it (§3, §14). This
names function-carrier types — `Endo`, `Pred`, State-style monad
carriers — and, when the recursion runs *through* the `Fn`, gives
**codata**:

```braid
data Stream(a) = (a Fn⟨• =Recursive> Stream(a)⟩)   # head + a THUNKED tail
```

The thunk is declared `=Recursive>` because a stream producer is written
under `with Recursive` (below), and a written arrow means what it says: an unlabelled
`Fn⟨• ⇒ Stream(a)⟩` refuses the very thunk the producer makes. `Recursive`
is the honest word for it — the object is **productive** (every force
returns one cell) but **unbounded** (there is no last cell), and `Recursive`
claims exactly the second thing.

A codata type gets constructor/unroll as usual but **no `foldName`** —
a structural fold through the thunk would diverge, so it is withheld by
construction; you observe instead (`unStream`, then `ev` to force
one cell). Productive corecursion guards its self-call under a quote —
`def from with Recursive = (n -> n [n 1 >> + >> from] >> Stream)`,
whose self-call still sits under the thunk — a self-call inside a
quotation is a **capture**, and abstraction elimination handles it. See
`examples/stream.braid`. Caveat: a `Fn` type whose stacks carry two
open stack-params (`Fn⟨s ⇒ s a⟩`) parses and expands, but won't
display-fold back (the leading-splice match is ambiguous — pin one
arity if you need the fold).

### Declaration words *(2026-09-17)*

**Beneath every keyword is a word.** A keyword line is parsed, whole,
into a **call** of an ordinary word acting on the dictionary:

```text
def f = body              ≡   [body] "f" defW
type Pair = Int Int       ≡   ⌜Int Int⌝ "Pair" typeW
import "util.braid"       ≡   "util.braid" importW
```

and the pipeline runs the calls, in file order, against `Dict`. The
surface does not change by one character. What changes is that there is
now one **table** saying what a keyword *is*, and it is open.

| keyword | its word | arrow |
|---|---|---|
| `def` | `defW` | `Code Str =Dict> •` |
| `type` | `typeW` | `TypeRep Str =Dict> •` |
| `data` | `dataW` | `TypeRep Str =Dict> •` |
| `theory` | `theoryW` | `Str Str =Dict> •` |
| `model` | `modelW` | `Str Str =Dict> •` |
| `transformation` | `transformationW` | `Str Str =Dict> •` |
| `functor` | `functorW` | `Str Str =Dict> •` |
| `import` | `importW` | `Str =Dict IO> •` |
| `table` | `tableW` | `Str Str =Dict IO> •` |
| `keyword` | `keywordW` | `Str Str =Dict> •` |
| *(none, until bound)* | `testW` | `Code Str =Dict> •` |

**The two that read the world say so in the grade.** `importW` and
`tableW` are `=Dict IO>`; the other nine are `=Dict>`. That is the ONE
place IO happens before anything is checked — the loader resolves a path
and reads a file — and the grade is the manifest of exactly that.
`:t importW` prints it.

**What an argument may be, exactly.** Three shapes, and the list is
closed:

| shape | what it is | where it comes from |
|---|---|---|
| `Code` | an already-parsed program | the parser, for a keyword line; `getCode`, `parse` or a functor's output, for a program |
| `Str` | a name, a header, a path — text the word *reads*, never parses | a literal, `cat`, `toStr` |
| `TypeRep` | an already-parsed type | the parser; `typeOfWord`, `typeOfCode` (§12) |

All three are **post-parse**, which is exactly the line direction 3
draws: post-parse `Code` functors only, parsing words never. A reader
macro would break uniform reading — you could not read a file without
running it — and it would make hygiene a discipline rather than a
property of the representation. A word that wanted a fourth shape would
be asking for one under another name.

**How a line is parsed into them.** Every declaration line is `KEYWORD
<head> = <body>`, split at its own first `=`, the body running to the
end of the line or into the indented block beneath it. The head is the
`Str`; the body is read at the word's declared shape; the arguments are
pushed in that order and the word is called postfix. A keyword whose
line has no `=` (`import "u.braid"`) takes the head alone.

**Locations are untouched.** A call carries the line its *body* starts
on, exactly as the def bucket carried it before there was a table, and
every refusal is raised from the same place against the same raw line —
so `file:line, in def X` says what it always said.

**A program may declare too.** A top-level group is a **declaration
line** when its **grade** says so — when what it does carries `Dict`:

```braid
([dup ; *] ; getCode) "square" ; defW      # `def square = dup ; *`

def declare = (n -> (n ; bodyFor) (n ; nameFor) ; defW)
[(acc n -> n ; declare ; acc)] 0 (1 2 3 ; pack) ; fold ; drop
```

The second line names `defW` nowhere: it is a declaration line because
`declare` is `=Dict>` and the grade propagates. That is what a manifest
is for, and it is the same mark the keyword makes, read off the arrow
rather than off the first token.

Three rules, each refused by name:

- **It must take nothing and leave nothing** (`• =Dict> •`), because it
  is lifted out of main and run above it, and otherwise that would
  change what main does.
- **It may not touch the world.** It runs at check time, before main, so
  its output would arrive before anything main prints. Reading a file
  before anything is checked is the **loader's**, and `import` and
  `table` are its words.
- **`defW` is the one of the eleven a program may call.** The other ten
  declare things the module's own defs are checked *against*, and those
  are checked above the program that would declare them.

**The table is open** — `keyword <name> = <a declaration word>`. From
that line on, `<name> x = …` is a declaration, collected the way a `def`
is (either an inline body or an indented block) and parsed into `[body]
"x" <word>`:

```braid
keyword test = testW
test squareIs25 = (5 ; square) (25) ; eq? ; verdict
```

`testW` is a declaration word the kernel ships with **no keyword of its
own**, which is what makes the binding worth having: it registers a
**check**, and a check runs at module start beside the laws and must
answer `true`. A check that is not `• ⇒ Bool` is refused at the
declaration, the same courtesy a law gets.

**And the word may be the module's own.** A declaration word is any word
at `Code Str =Dict> •`:

```braid
def twiceW = (c n -> c n ; defW ; (c c ; append) (n ; _ "Twice" ; cat) ; defW)
keyword double = twiceW
double bump = _ 1 ; +          # declares `bump` and `bumpTwice`
```

A keyword line for a bound word becomes a **declaration line**, run with
the module's own declaration program in file order — which is why the
word may be one the module writes. `keyword` refuses a name the language
already uses: *`keyword def` is refused: def is already a keyword of the
language, and a keyword names one declaration word.*

**A keyword word takes already-parsed arguments, and that is all it may
take.** A bound keyword's line is `<keyword> <name> = <body>` — a `Str`
and a `Code`, in that order, pushed and the word called postfix. There
is no form in which a keyword word receives the line's TEXT, because
that word would be a parsing word, and those are refused permanently.

**Where a programmatic def lands.** Above main and **below** the
module's written defs — the dictionary a compile-time word sees is the
dictionary so far, which is the same ordering rule a `functor` obeys. So
main may call it and a written `def` may not.

`examples/dictionary.braid` is the whole of this running; `:defs` in a
session lists the words it declared, and `typeOfWord` answers about them
like any other.

### Modules: `import "path.braid"`

One file's declarations in another file's scope, written as a
declaration line and resolved before anything is checked:

```braid
import "geometry.braid"
import "lib/shapes.braid"      # relative to THIS file's directory
```

What travels is **declarations** — defs, `type`/`data`,
`theory`, `model`, `functor`, and their `##` docs. What does not is
the imported file's **main program**: a library's demo is its own
business, and the file still runs it when you run that file directly.
An imported file is checked as part of the composite module, so it has
to be a valid module on its own.

The rules, all of which are one rule — an import is the **inclusion**
of one module's presentation into another, so objects are added and
never merged:

- **A clash is an error**, naming both files: *in `b.braid`: `poly` is
  already defined in `a.braid`*. There is no namespacing and no `as` in
  this version; two files that both want the name have to settle it.
- **A file is included once**, however many routes reach it. A diamond
  (`a` imports `b` and `c`, both of which import `util`) is not a
  duplicate-definition error.
- **A cycle is an error** naming the path that closes it: *import
  cycle: a.braid → b.braid → a.braid*.
- **Imports are resolved first**, depth-first in file order, so the
  ordering rule (a functor is runnable before its first `with`, §6)
  extends across files unchanged.
- **A relative path is relative to the importing file**, which is what
  lets a directory of modules move as one; failing that, the current
  directory is tried, so a program read from a pipe (`braid -`) can
  import too. Found in neither, the error names both places.

Nothing above needed machinery of its own: inclusion is textual, and
the composite is checked as a single module. That is also why a
`theory` declared in one file and its `model` in another simply
work. See `examples/imports.braid`.

Reading the file is the **loader's** IO, at the same boundary that
reads the program you ran; elaboration still sees only parsed
declarations and stays pure. A module checked without a file context —
a REPL line, an embedded source string — has nothing to resolve an
import against and says so.

In a session, `:import "path.braid"` does the same thing, and is the
only way a session gets a `theory`, an `model` or a `functor`, since
it cannot declare one:

```text
braid> :import "examples/traced.braid"
imported examples/traced.braid   (9 defs, 2 functors)
braid> def poly2 with Traced = dup >> *
def poly2 : ∀ . Int =IO Traced> Int
```

### Tables: `table Trades = "trades.csv"` *(2026-09-15)*

A CSV's header **is a presentation**: it declares a data type. So the
directing type is written — in a file — and the file at check time is
source:

```braid
table Trades = "examples/data/trades.csv"
#   data Trades  = (sym: Str, px: Float, qty: Int)
#   headerTrades : • ⇒ List(Str)
#   loadTrades   : Str =IO Recursive> (List(Trades) | Str)
```

The **loader** resolves the line, at the same IO boundary `import`
already uses and nowhere else. It resolves the path by the import rule
above, reads the **whole file**, and writes Braid text that is included
exactly as an imported file's declarations are — spliced in under the
`table` line, which stays where it was written. Nothing about `table`
runs: the generated text is the only thing that does.

- **The names** come from the header, sanitized: each space, tab and
  `-` becomes `_`, and the first letter is lowercased. What that leaves
  must be a word — a letter, then letters, digits or `_` — and a header
  that is not one, or that clashes with a word already in scope, is an
  error naming the fix (the schema form, below).
- **The types are read off the data**: `Int` if every cell in the
  column is an Int literal, else `Float` if every cell is a Float or an
  Int literal, else `Str`. The whole file is read, so nothing is
  guessed about a row that was not looked at.
- **A blank cell is refused** in this version, naming line and column: a
  column has one type and a blank is not a value of it.
- **`loadTrades` re-reads the file** when it runs. A CSV that changed
  since the check puts its first bad row on the miss track, by line
  number — the ordinary railway, and the whole load is `sequence` over
  the rows.

The **schema form** writes the names and the types instead, positionally:

```braid
table Sector(ticker: Str, sector: Str, weight: Float) = "sectors.csv"
```

Each cell must then read at the type that was written (or the check
refuses, naming line and column), and the arity must match the header.
There is **one** such form, not one for renaming and one for ascribing,
because renaming a column and giving it a type are the same act:
naming it. `Str`, `Int` and `Float` are the three types a column may
have; a column of anything else is a join, and a join is a program.

A table crosses a file boundary like everything else: `import` of a
file with a `table` line (and `:import` of one in a session) runs the
loader for it, and the CSV resolves against that file's directory, then
the current one. A module checked **without** a file context — a REPL
line, an embedded source string — has nothing to resolve the CSV
against and says so. See `examples/frame.braid`.

## 9. Primitive reference

**The kernel admits three presentations** (each derives the others,
verified): the single-wire generators `{_, dup, swap, drop}`; binders
(`dup = (x -> x x)` …), which abstraction elimination compiles back
into the generators; and the segment tier (`dup = (x -> x >> dupN)`,
`drop = (x -> x >> forget)` — the
generators are the width-1 shadows of the open-width words). The
single-wire basis stays primitive because it is the normal-form
alphabet reflected `Code` is written in. `pass` is not merely
equivalent to `...` — the remainder marker *denotes* `pass`; they are
one term with two spellings. Derived-but-primitive-looking words
(`odd?`-family, `pack`/`pack2`, `sumN`, `mapN`, `foldExp`, `id`,
`loop`, `gt?`/`gte?`/`lte?`) live in the prelude — the design bet ("primitives span
everything else in the language itself") is proven in both directions.

**There are 64 primitives** *(2026-09-21: the N-family reduced to one
catamorphism — `foldExp`, `foldExp2`, `mapN`, `mapN2` out, `mapAccumN`
in, 67 → 64; 2026-09-20: `one`, 66 → 67; 2026-09-17:
`showStack`, 65 → 66; the count had said 60 since 2026-09-14 and was
stale)*. **The count is of words source can name, and it therefore
EXCLUDES `#fix`**, the knot `with Recursive` emits: `#` opens a
comment, so no program and no reflected atom can spell it. Every count
in this manual and in the README is that count; the kernel holds one
more morphism than any of them reports, and it is always this one.
`#fix` is a generator of the free category all the same — and since
2026-09-18 an irreducible one, because nothing else in the language can
produce an unbounded knot (§8, §5). A word keeps its place here
only if it is a **structure map** of the doctrine — cartesian
(`_`/`dup`/`swap`/`drop`/`pass`/`forget`), coproduct (`alt1…altN`,
`there`, `merge`), exponential (`ev`), the open
coproduct (`into`), the ONE eliminator over `Aⁿ` and its Naperian
rewirings — or if it
**touches the implementation**: arithmetic and strings, `eq?`, the four
io edges, reflection (`parse`/`unparse`/`reflect`/`evalAs`/`sameCode`/
`sameCodeC`/`interpose`/`rewrite`), and the type-level `weaken`/`finInt`. Everything else is
a prelude def with its derivation visible.

**`asFloat?` and `split` are implementation prims** *(2026-09-14, 58 →
60)*, and they are in the kernel on the same criterion `cat`, `toStr`
and `asInt?` are: a `Str` is a machine string, and nothing in the
language can take one apart. `split` is the general cutter, so there is
no separate `lines` — one spelling per thing, and a newline is a
separator like any other. They arrived with `examples/frame.braid`,
which has to read a CSV.

**The eleven Float words are implementation prims** *(2026-09-14, 47 →
58)*, in the kernel for exactly the reason the Int arithmetic and the
four io edges are: a double is a machine number and nothing in the
language can build one. They span no structure — they are the machine,
written down. `fneg` and `fabs` are *not* among them: negation is
`0.0` minus, absolute value is one comparison, so both are prelude defs
(§10), and equality is the polymorphic `eq?`, which already reaches a
Float. There is no second spelling of equality and no `feq?`. **Recursion left this list
on 2026-09-14** (48 → 47): the knot is spelled `#fix`, which source
cannot write, and `with Recursive` is the only thing that emits it —
so `fix` is a prelude def (§10) like `loop`.

Wiring (cartesian structure):

| word | type | note |
|---|---|---|
| `_` | `a0 ⇒ a0` | the identity: the section hole, marking where the incoming wire goes. `id` is the WORD for the same morphism and is a **prelude def** (`def id = _`) — one morphism, one prim |
| `swap` | `a0 a1 ⇒ a1 a0` | |
| `dup` | `a0 ⇒ a0 a0` | Δ |
| `drop` | `a0 ⇒ •` | |
| `pass` | `ρ0 ⇒ ρ0` | identity on the whole segment |
| `forget` | `ρ0 ⇒ •` | terminal morphism |
| `one` | `• ⇒ •` | the identity ON the terminal object, and the only prim that is monomorphic on purpose: `pass` names the same morphism at every width and so pins nothing, which is why `[pass]` cannot serve where `[one] : • ⇒ Fn⟨• ⇒ •⟩` does. `•` is its glyph spelling in term position; ONE INHABITANT, not one wire (§5). A prim and not a prelude def because it must RUN NOTHING — the def would be `1 ; drop`, which allocates an Int to discard it *(2026-09-20)* |

Arithmetic & strings (all exact; `-`, `div`, `mod` are bottom-op-top):

| word | type |
|---|---|
| `+` `-` `*` `div` `mod` | `Int Int ⇒ Int` |
| `fadd` `fsub` `fmul` `fdiv` | `Float Float ⇒ Float` — Float arithmetic (2026-09-14). One scheme, `f` + the operation spelled out: a symbolic family (`f+ f- f*`) cannot be had, because `-` is not an identifier character, so `f-` is two atoms — and a scheme that breaks on subtraction is not a scheme |
| `fexp` `fsin` `fcos` `fsqrt` | `Float ⇒ Float` |
| `toFloat` | `Int ⇒ Float` — the only way up |
| `floor` | `Float ⇒ Int` — the only way down; the mathematical floor (`-2.7 ; floor` is `-3`) |
| `cat` | `Str Str ⇒ Str` |
| `toStr` | `a0 ⇒ Str` |
| `showStack` | `ρ0 ⇒ Str` — the whole segment, deepest wire first, space separated, each wire as `toStr` renders it and as the REPL's `:s` prints it. A RENDERER, NOT A CLASS: nothing hooks a user-defined rendering into it. Consuming and open-tailed on `forget`'s convention: the whole segment as the final atom of its stage, the empty one anywhere else. A binder aims it at part of a stack — `dup ; _ (b -> b ; unBox ; showStack)` *(2026-09-17)* |
| `asInt?` | `Str ⇒ (Int \| Str)` |
| `asFloat?` | `Str ⇒ (Float \| Str)` — reads exactly the SOURCE notation for a Float literal (optional `-`, digits, point, digits), which is also what the display prints, so `toStr ; asFloat?` is the identity on every finite Float *(2026-09-14)* |
| `split` | `Str Str ⇒ List(Str)` — `s sep ; split`: n+1 pieces for n occurrences, so pieces and separators rebuild the original exactly, empty pieces included. An empty separator cuts nothing *(2026-09-14)* |
| `symStr` | `Sym ⇒ Str` |
| `print` | `a0 =IO> •` — io (§3) |
| `true` / `false` | `• ⇒ Bool` |

Routers (the primitive comparators; hit = track 1 — the predicate
routers `odd?` `even?` `zero?` `negative?` are DERIVED prelude words
now, via `mod`/`equals`/`less` and the `(n | n)` re-routing pattern):

| word | type |
|---|---|
| `eq?` | `a0 a0 ⇒ (a0 a0 \| a0 a0)` — structural equality, any value |
| `lt?` | `Int Int ⇒ (Int Int \| Int Int)` — the only primitive order on `Int`. `gt?` `gte?` `lte?` are **prelude defs** derived from it (§10), with identical schemes |
| `flt?` | `Float Float ⇒ (Float Float \| Float Float)` — the same, on `Float` (2026-09-14). The Float comparators that mirror `gt?`/`gte?`/`lte?` are not in the prelude: `swap`, `not` and a two-track row derive each in one stage where it is wanted |

Sums & control:

| word | type |
|---|---|
| `alt1`…`altN`, `ok`/`here`/`again`, `miss`/`done` | `ρ0 ⇒ (… \| ρ0 \| σ0)` — spelled `in1`…`inN` before 2026-09-12; renamed (one spelling, **no `inN` alias**) because `[h >> alt1] into` read badly and `in` is the prefix `into` lives beside |
| `there` | `(σ0) ⇒ (ρ0 \| σ0)` |
| `merge` | `(ρ0 \| ρ0) ⇒ ρ0` |
| `into` | `Fn⟨ρ0 ⇒ (σ0)⟩ (ρ0 \| σ0) ⇒ (σ0)` — the **open** eliminator (§6): the copairing `[h, id]`, handling the first alternative into the remaining row and shifting the rest. Not derivable: over a residual it is the only copairing there is. |
| `ev` | `Fn⟨ρ0 ⇒ ρ1⟩ ρ0 ⇒ ρ1` — the exponential's **counit**; spelled `apply` before 2026-09-12, renamed to match `curry` (§10). The only word that consumes an `Fn`, and not derivable: naming a value never runs it. |

Metaprogramming & IO (railway-typed edges):

| word | type |
|---|---|
| `reflect` | `Fn⟨ρ0 ⇒ ρ1⟩ ⇒ (Code \| Str)` |
| `evalAs` | `Fn⟨ρ0 ⇒ ρ1⟩ Code ρ0 ⇒ (ρ1 \| Str ρ0)` — witness-checked |
| `unparse` | `Code ⇒ Str` |
| `parse` | `Str ⇒ (Code \| Str)` |
| `checkedStage` | `Code ⇒ Code` — η, having been CHECKED to fit at every cut: `ρ ⇒ ρ`, or `E ρ ⇒ E ρ` over resource wires (§12). `interpose = checkedStage ; interposeRaw` is the prelude word built on it, at `Code ⇒ Fn⟨Stage ⇒ Code⟩` |
| `rewrite` | `List(Sym) List(Sym) Code ⇒ Code` — `froms tos c`: rename atoms by a table, through quotes, rows and groups. The runtime engine, unchecked on its own: `model … in Base` is where a table is blessed (§8) |
| `sameCode` | `Fn⟨Σ ⇒ Θ⟩ Fn⟨Σ ⇒ Θ⟩ ⇒ Bool` — same morphism? decided by normalizing to a case tree over the free bicartesian closed category; errors outside the structural fragment (§12.9) |
| `sameCodeC` | `Code Code ⇒ Bool` — the same question over Code values, and the only form a law about a FUNCTOR can take. One procedure with `sameCode` since 2026-09-13; the two always agree (§12.9) |
| `readLine` | `• =IO> (Str \| Str)` — io; one line from stdin, EOF misses |
| `readFile` | `Str =IO> (Str \| Str)` — io |
| `writeFile` | `Str Str =IO> (• \| Str)` — io; hit is the empty success, miss carries the error |

These three and `print` are the **whole** io surface: nothing else is
marked, every other grade is inferred (§3). `reflect` and `parse` stay
pure — `reflect` READS a quotation, it never runs it — and so does
`evalAs`, which takes its grade from its witness: a pure witness admits
only pure code and stays pure, an io witness permits io. That is the
sandbox — what runtime-loaded code may do is bounded by the type you
were willing to write for it. Handing a pure witness io code rides the
miss track: `Cannot unify effects: IO vs pure (the expected type fixes
the grade; this code must stay pure)`. See `examples/witness.braid`.

Exponent tier (widths erased; see §13):

| word | type |
|---|---|
| `mapAccumN` | `Fn⟨a0 a1 ⇒ a0 a2⟩ a0 a1ⁿ ⇒ a0 a2ⁿ` — the tier's ONE catamorphism |
| `dupN` | `a0ⁿ ⇒ a0ⁿ a0ⁿ` |
| `zipN` | `a0ⁿ a1ⁿ ⇒ Box(a0 a1)ⁿ` — merge two lanes, ONE WIRE per element |
| `unzipN` | `(a0 a1)ⁿ ⇒ a0ⁿ a1ⁿ` — split the flat stack-native form |
| `at` | `Fin(n) a0ⁿ ⇒ a0` — index the bundle; 0 is the DEEPEST wire |
| `indicesN` | `a0ⁿ ⇒ (Fin(n) a0)ⁿ` — tag every wire with its own index |

**`foldExp`, `foldExp2`, `mapN` and `mapN2` left this list on
2026-09-21** (67 → 64): all four are `mapAccumN` at a different motive
and are now prelude defs with character-for-character the schemes they
had (§13). `mapAccumN` rebuilds a bundle as it folds, which is what
lets you **lift an ordinary word pointwise**. `addN` and `scaleN` are
prelude defs too — and so is any lift you need:

```braid
def addN  = zipN >> [unBox >> +] ... >> mapN    # the bundle monoid ∇
def mulN  = zipN >> [unBox >> *] ... >> mapN    # NOT linear — outside the GLA set
def maxN  = zipN >> [(p -> p >> unBox >> (x y -> (x y >> less) [y] [x] ... >> cond))] ... >> mapN
def negN  = [0 _ >> -] ... >> mapN
```

**Indices.** `Aⁿ` *is* the function space `Fin(n) ⇒ A`, stored
tabulated and flat; `Fin(n)` is an index into a bundle of width n. The
bound is a type and is erased like every other width — at runtime a
`Fin` is a bare `Int`. `at` and `indicesN` (above) are the
exponent-shaped half; the rest:

| word | type |
|---|---|
| `checkedAt` | `Int a0ⁿ ⇒ (Fin(n) a0ⁿ \| Int a0ⁿ)` — bounds-check and route |
| `weaken` | `Fin(n) ⇒ Fin(n+1)` — runtime identity |
| `finInt` | `Fin(n) ⇒ Int` — runtime identity; forgets the bound |
| `fin0`, `fin1`, `fin2`, … | `• ⇒ Fin(n+k+1)` — index literals, like `altN` |

**Every index introduction's `n` must be forced by a relevant input** —
a literal's offset, or a live bundle on the stack. Hence two modes.
**Static**: a literal's offset *is* the proof that k is in range, and
`weaken` maintains it, so `at` needs no runtime check. **Dynamic**:
`checkedAt` tests an `Int` against the live segment's actual width and
ROUTES — the hit track is the witness, the same move `odd?` makes for
parity. There is deliberately no `tabulate` and no bare `asFin`: an
output-only `n` has no witness, exactly as for `zeroN` (§13). The full
argument is `design-indices.md`.

```braid
1 2 3 >> indicesN            # • ⇒ Fin(3) Int Fin(3) Int Fin(3) Int
fin1 10 20 30 >> at          # 20
10 20 30 >> indicesN         # stack: 0 10 1 20 2 30
1 10 20 30 >> checkedAt      # • ⇒ (Fin(3) Int Int Int | Int Int Int Int)
7 10 20 30 >> checkedAt >> (at >> print | forget >> "oob" >> print) >> merge
                             # oob
```

## 10. Prelude reference (all derived user code — `:defs` for types)

**Lists**: `nil` `cons` `uncons` `fold` (left fold) `foldList`
(structural) `map` `filter` `reverse` `append` `concat` `single`
`flatMap` `len` `sum` `product` `range` `downFrom` `take` `skip` `zip`
(`List(a) List(b) ⇒ List(a b)`) `unzip` (its inverse, `List(Box(a b)) ⇒
List(a) List(b)` — 2026-09-14) `nth` (`Int List(a) ⇒ Maybe(a)`,
counting from 0 — 2026-09-14) `all` `any` `partitionSum` `sequence`
(List over the sum monad) `printAll`.

**Router algebra** (quoted predicates as values): `not` (track swap)
`negate` `both` `either` `equals?` `less?` `equalsTo` `lessThan`
`else?` (always-hit) `assocL`/`assocR` (re-nest a sum);
`splice : (ρ0 | (σ0)) ⇒ (ρ0 | σ0)` (flatten one level of nesting into
the parent row, any inner arity); the ladder steps `settle :
(ρ0 | (ρ0 | ρ1)) ⇒ (ρ0 | ρ1)` (guard ladder — fold an agreeing answer
into the pile) and `settleR : ((ρ0 | ρ1) | ρ1) ⇒ (ρ0 | ρ1)` (its
validation mirror). See `examples/settle.braid`.

**Float** *(2026-09-14)*: `fneg : Float ⇒ Float` (`0.0` minus) and
`fabs : Float ⇒ Float` (one `flt?` and a two-track row). Everything
else about a double is a machine fact and therefore a prim (§9).

**Verdict tier** (forget the data, keep the decision): `verdict :
(ρ0|ρ1) ⇒ Bool`, and long forms `equals` `less` `odd` `even` `zero`
`negative`. Bool connectives: `and` `or` `xor` `implies`; muxes
`select` `swapIf`; `condFn`/`cond`, `whenFn`/`when`,
`unlessFn`/`unless`.

**Guard ladders** (§11): `if` `elif` `else` `otherwise` `decide`
`firstTrue` `matchWith` `choose` `ifRoute` `elifRoute`.

**Knots** *(derived since 2026-09-14)*: `fix :
Fn⟨Fn⟨ρ0 =Recursive> ρ1⟩ ρ0 ⇒ ρ1⟩ =Recursive> Fn⟨ρ0 =Recursive> ρ1⟩` is
the parameterized (Conway) fixpoint on `Fn`, for **open** recursion —
a body someone else wrote (§8). It is a prelude def under the marker,
eta-expanded because Braid is call-by-value:

```braid
def fix with Recursive = (b -> [(b >> fix >> id) ... >> b ... >> ev])
```

The `id` says the knot is **one wire**: a grouped atom in non-final
position is closed (§4), and closing would otherwise erase the knot's
own arity. Its arrow carries `Recursive` where the old primitive's was
pure — the derived word runs the knot's `ev`, and the scope it is
written under tied one, so it minted (§3).

**Loops** *(all derived since 2026-09-12)*: `loop :
Fn⟨ρ0 ⇒ (ρ0 | ρ1)⟩ ρ0 =Recursive> ρ1` is the **Elgot dagger**, and it is
a prelude def under the same marker:

```braid
def loop with Recursive = (f ... -> f ... >> ev >> (f ... >> loop | pass) >> merge)
```

`f† = ∇ ∘ (f† + id) ∘ f`, written out: the body routes into
`(continue | done)`, the continue track re-enters through the knot, the
done track falls out, and `merge` — the codiagonal ∇ — joins them. Note
it needs **no `into`**: the row is closed and two-track, so the
copairing `[f†, id]` is just `(f† | pass) >> merge`; `into` (§6) is for
the open case. `Recursive` is the marker's receipt, and it sits on
`loop`'s **own** arrow, because the knot is what recurses and the body
is asked for nothing (§3: composition joins). A written
pure `Fn⟨Σ ⇒ (Σ|Θ)⟩` therefore goes straight in. Cost measured:
100 000 iterations in 3.2 s against 1.9 s for the builtin, and no
growth in memory.

*(Between 2026-09-12 morning and evening this paragraph said the
opposite — that `loop`'s body reads `=Recursive>` and a written pure `Fn` is
refused. That was composition unifying grades rather than joining
them, and it was a bug; see design-effects.md, "composition JOINS".)*

`while` `until` (+ `whileFn`/`untilFn`) are three-line defs over it:
`while : Fn⟨ρ0 ⇒ (ρ1 | ρ2)⟩ Fn⟨ρ1 ⇒ ρ0⟩ ρ0 =Recursive> ρ2`.

**The identity and the order** *(2026-09-12)*: `def id = _` — `_` is
the identity prim (the positional spelling), `id` the word for it.
`def gt? = swap >> lt? >> (swap | swap)`, `def gte? = lt? >> not >>
(pass | pass)`, `def lte? = gt? >> not >> (pass | pass)` — one
primitive order, `lt?`, and the other three read off it. The trailing
closed 2-row is not decoration: `not` is built from injections, which
are open, so `(pass | pass)` re-closes the row and makes the derived
schemes **identical** to the prims' (`Int Int ⇒ (Int Int | Int Int)`).

**Bundles**: `sumN : Intⁿ ⇒ Int`; `pack : aⁿ ⇒ List(a)` and `pack2`
(derived from their own eliminators — `foldExp` + `cons`/`reverse`,
Church-style for `pack2`).

**The closed structure** *(2026-09-12)*: `curry : Fn⟨a ρ0 ⇒ ρ1⟩ ⇒
Fn⟨a ⇒ Fn⟨ρ0 ⇒ ρ1⟩⟩` — λ, the other half of the exponential whose
counit is the prim `ev` (§9). It is a **prelude def**, not a prim:
`def curry = (f -> [(x -> [x ... >> f ... >> ev])])`, and its own body
is the one binder-into-quote that abstraction elimination takes as a
generator rather than eliminating (§6). From it: `capture : a
Fn⟨a ρ0 ⇒ ρ1⟩ ⇒ Fn⟨ρ0 ⇒ ρ1⟩` (partial application — `curry` then `ev`),
and the distributivity family `dist2 : a (ρ0 | ρ1) ⇒ (a ρ0 | a ρ1 | σ0)`
with its inverse `undist2 : (a ρ0 | a ρ1) ⇒ a (ρ0 | ρ1 | σ0)`, plus
`dist3`/`dist4`/`undist3`/`undist4`. Distributivity is a **theorem**
here, not an axiom: `P × –` is a left adjoint (that *is* `curry`), left
adjoints preserve coproducts, and `dist2`'s body is that proof — capture
the wire into one handler per track, then `case2`. `undist` needs no
closed structure: it is the map any category with coproducts has.
`distN` follows `caseN`'s arity family and, like `caseN`, the sums
**nest** — polymorphism does not reach a row's width.
`examples/distributive.braid` runs seven laws over two models.

**Strength**: `lift : Fn⟨ρ0 ⇒ ρ1⟩ ⇒ Fn⟨a0 ρ0 ⇒ a0 ρ1⟩` — run a program
one wire deeper, the wire beneath untouched; compose it once per
context wire (`[dup >> *] >> lift >> lift : • ⇒ Fn⟨a0 a1 Int ⇒ a0 a1
Int⟩`). This is tensorial strength, the action of `(A ⊗ −)` on a
morphism, and it is exactly what threads a resource past a pure stage —
so ambient threading (§6) needs no machinery for the pure case, only
the counting. `def lift = (f -> [_ (f ... >> ev)])`.

**Code** (§12): `getCode : Fn⟨ρ0 ⇒ ρ1⟩ ⇒ Code` (`reflect`, or `nil`
when `reflect` misses); `stagewise : Fn⟨Stage ⇒ Code⟩ Code ⇒ Code` —
the EXTENSION of a graph morphism to a whole spine, which is what a
`functor` declaration applies (§8) — and `atomwise : Fn⟨Atom ⇒ Stage⟩
Code ⇒ Code`, the same one level down (`flatMap` on the spine, both);
`interpose : Code ⇒ Fn⟨Stage ⇒ Code⟩`, which BUILDS the graph morphism
that inserts a checked stage after every generator, and `interposeRaw`
(same, unchecked) with the prim `checkedStage : Code ⇒ Code` between
them; `lift2 : Fn⟨Code ⇒ Code⟩ Fn⟨ρ0 ⇒ ρ1⟩ ⇒ Fn⟨ρ0 ⇒ ρ1⟩` — any
`Code ⇒ Code` word applied at runtime, the program its own witness and
its own fallback; `box`.

## 11. Control flow — the idioms

Two tiers of predicate: **routers** (`odd?`, keep + route — branches
receive the data) and **verdicts** (`odd`, forget to `Bool`).
`verdict` converts. Then, by situation:

```braid
# bound subject + word ladder (the general elif chain)
def sign =
    x ->
    (x ; negative) "neg"  >> if
    _ (x ; zero)   "zero" >> elif
    _ (x ; toStr)         >> else       # or: _ [lazy] >> otherwise

# lane accumulation: `...` stacks lanes, decide folds — no _, no quotes
def grade =
    x ->
    (89 x ; less) "A" ...
    (79 x ; less) "B" ...
    "F"               ...
    decide

# railway ladder (operators, no _): each guard ends (answer |)
def grade2 =
        x ->
        (89 x ; less) "A" >> if
    >?> (79 x ; less) "B" >> if
    >!> "F"

# routers when branches need the routed value
odd? >> (dup ; * | 1 ... ; +) >> merge

# deferred peel: the sum deepens; case3 folds the tree
negative? >> (drop ; "neg" | pass) >> (pass | zero?)
    >> [pass] [drop ; "zero"] [toStr] ... >> case3

# guards as data: pack2/pack2R clause lists, probed by choose / matchWith
x [default] ([p?] [action] … >> pack2) >> matchWith

# loops
7 >> [_ 100 >> less?] [2 _ >> *] ... >> while      # → 112

# general recursion: mark the def, and call it by name (§8)
def double100 with Recursive = _ 100 >> less? >> (2 _ >> * >> double100 | _) >> merge

# open recursion, when the body is a value someone hands you (§8, §10)
[(self ... -> _ 100 >> less? >> (2 _ >> * >> self ... >> ev | _) >> merge)] ... >> fix ... >> ev
```

There is **no guard syntax in the parser** — every idiom above is
prelude defs plus core forms. See `examples/ladder.braid` and
`design-control-flow.md` for the full inventory and the reasoning.

## 12. Metaprogramming

Metaprogramming in Braid is a **ladder of declarations**, and reading it
in order is most of learning it. `Code` is the *bottom* rung, not the
first: it is what you reach for when nothing above it fits.

**1. A theory is a presentation** (§8). `theory Monoid(a) = unit : • ⇒
a ; op : a a ⇒ a` names generators and their types, and laws that run.
Nothing is dispatched and nothing is inferred: a theory is a
vocabulary with a signature.

**1¼. A model may map the OBJECTS too** *(2026-09-17)*. `model Mod in
Base(Int ↦ Mod7 via reduce)` is a functor on the ambient presentation
whose action on objects is the substitution `Int := Mod7`; `via` gives
the literal family its image, the table gives the generators theirs, a
def with neither is **unfolded** (`F(def) = F(body)`, cached as
`M@def`), and a word that mentions the mapped type with none of the
three is refused by name. `examples/modular.braid` runs one polynomial
over `Int` and over Z/7 without writing it twice, and — in the same
file — shows that this is *not* the same claim as being a ring
homomorphism, which is what `transformation` is for.

**1½. A model may be built out of another model** *(2026-09-15)*.
`model Fwd(Smooth(a, g)) in Smooth(Dual(a), a)` is a **family** — a
functor Mod(Smooth) → Mod(Smooth) — and `with Fwd(Floats)` applies it,
minting a model whose name is the application. It is the *presentation*
level of the same move `functor` makes at the *code* level: a functor
rewrites a program, a family rewrites a model. Neither is a dictionary
and neither is inferred. Laws cannot be checked for the family (that
would need equality modulo the parameter theory's laws); they are
checked at each instantiation (§8).

**2. `in T` declares a morphism of it** — a **template**. `def fold1
in Monoid = [op] unit ... ; foldExp` is a body written in the
theory's vocabulary, waiting for a model. It applies nothing and mints
nothing; it is not even a def until a model arrives.

**3. `with X` applies** — one rule, every kind: *what follows is written
in the domain of X, and X is applied to it.* An **model** points
*into* the base (`with IntSum ; fold1` renames slot names to that
model's words and re-infers); a **model with a carrier**, a
**resource** and a **functor** point *out* of it (`with Circuits`
transports composition itself into the category that model presents;
`with Fuel` writes the routing;
`with Traced` extends a graph morphism along the wiring). A model of
`Base` — `model Opt in Base = dupInt = dup` — is the base
reinterpreting itself, and is where optimizers live (§8).

**4. Every `with` leaves a receipt.** The label on the arrow is
inference's record of what the elaborated code went through:
`total : Intⁿ⁰ =IntSum> Int`, `easy : Int =Circuits Recursive> Int`,
`poly : Int =Opt> Int`. Markers are **written** (the `with`), receipts
are **inferred** (the label); only a `with` mints, and every `with` does.
A written type must carry the label too, so an unlabelled witness
refuses instrumented code exactly as a pure one refuses io — which is
the whole difference between an optimizer you can audit and one you
must trust.

**5. A functor over `Code` — instrumentation and retrofit.** Everything
above is by generators, checked once, and free at every use. So is
this, and that is the change of 2026-09-18: `functor F = <graph
morphism>` gives ONE IMAGE PER GENERATOR, `Fn⟨Stage ⇒ Code⟩`, and the
extension along a spine is computed rather than written — a functor out
of a free category *is* a graph morphism, so functoriality is the
universal property and not a promise. What is still untyped is the
middle: the image is a program on syntax, spliced and re-inferred, so
the IMAGES are unchecked even though the functor is one. Reach for it
when what you want is not a model of anything — a tracer, a meter, a
rewrite over the shape of a spine rather than over its words — and read
*Functors, and the ones known to type* below for where the guarantees
stop.

There is no longer a whole-spine escape hatch: a `Code ⇒ Code` word may
not head a `with` (§8). Its two homes are `lift2 [w]` — the runtime
lift, checked per program — and a declaration program, for code that is
generated rather than rewritten.

**The worked example of rungs 1–3 is `examples/autodiff.braid`**
*(2026-09-14)*, and it is worth reading precisely for what it does
*not* contain: no `Code`, no `functor`, no `getCode`, and no chain
rule. Differentiation is a functor into pairs of a value and a linear
map (Elliott; §16), a model of a theory *is* a functor out of the free
category on the theory's generators, so the chain rule is the
statement that composition goes to composition — which is what a model
already promises. The file writes `theory Smooth(a, g)` (a ring with
`exp`, `sin` and `cos`), three models of it — `Floats` evaluates, `Fwd`
carries a tangent, `Rev` carries the transpose of the same linear map
as a continuation — and one body per program, written `in Smooth`
and read by all three. Each slot says what the derivative of **one**
operation is; nothing composes derivatives by hand, because `;` does.
`transformation Value in Fwd(Floats) ⇒ Floats = value, zeroTangent` is
the sentence *AD computes the right value*, and all ten of its squares
are **proved** by the normalizer rather than sampled; `transformation
Transpose : Fwd(Floats) ⇒ Rev` is
the sentence *forward and reverse are one linear map*, and its
verdicts are mixed — three proved, seven sampled through the exit
*(2026-09-14, 2026-09-15)*.

`Fwd` is a **family** *(2026-09-15)* — `model Fwd(Smooth(a, g)) in 
Smooth(Dual(a), a)` — so `with Fwd(Fwd(Floats))` differentiates the same
three templates **twice** and the file prints second derivatives. That
is also why the theory declares `cos`: a theory closed under `Fwd` must
be able to write each generator's derivative in its **own** vocabulary,
and while `Fwd` was hand-written over `Float` it could reach the base
word `fcos` instead.

**The second worked example is `examples/frame.braid`** *(2026-09-14)*
— a **data frame**, and it is worth reading for the same reason: there
is no loop over rows in it. You write a program on ONE ROW — a stack
of scalars, ordinary Braid — and a model lifts it to the frame:

```braid
data Trade = (sym: Str, px: Float, qty: Int)
def notional with Frame = dup ; px qty ; _ toFloat ; fmul
#   notional : Trade =Frame Recursive> Float
```

`Frame` models the same `Doctrine` `Circuits` does. Its hom-object
`Col(ρ, σ)` is a **function between columns** — a row program of any
width, because the arguments are whole stacks — `embed` is `map` and
`compose` is composition. "The other columns ride past" is what the
base's own `...` already means, so the two-wire stage `px qty` carries
with no strength to say it again. The model's laws are `map`'s functor
laws, and the doctrine's five run over them before the file prints
anything. The row store inside is a `List(Box(ρ))`, one list of boxed
rows: a *stack of lists* is the non-injective column store — three
columns of ten and ten columns of three are the same stack of Ints —
and it must not enter the type.

**The columns are the field words.** `sym`, `px` and `qty` are the
projections the `data` declaration generated (§5) — ordinary
definitions, so a column name composes, quotes and reflects like any
other word. Nothing in the type system knows a column is called `px`;
the header travels as runtime data, a `List(Str)` handed to the
printer.

**What stays at frame level, and why.** A functor cannot drop a row.
`map` preserves the index pointwise, so a transported row program
cannot move a row, drop one, or see its neighbours — which is exactly
right, and exactly why `keep`, `groupBy`, `sortBy`, `join` and the
aggregations are written **once**, on columns, outside any scope. The
division of labour is not a convention; it is what the model is.

**The index reading.** A frame *is* a map from an index to a row —
`Fn⟨I ⇒ row⟩` with its key set — and the file represents it as
`List(row)` with an implicit positional index `0 … n−1`, which is
`Fin(n) ⇒ row` stored tabulated and flat (§13). The implicit index is
what makes `map` index-preserving and `zip` meaningful; making it
explicit would want a key type in the hom-object, and `k(..., ...)`
takes two.

**The one thing the doctrine cannot carry** is a *filter written as a
row program*: `row ⇒ (row | •)` transports a SUM, and the Doctrine has
no choice slot (`ArrowChoice`'s `left`). `keep` sidesteps it — the
deciding is a column, which a functor may compute, and the dropping is
frame level.

**The third worked example is `examples/prob.braid`** *(2026-09-15)* —
**probability as a Markov category**, and it is the one that shows what
a model is *for*. A Markov category (Fritz; §16) is a monoidal category
in which every wire can be copied and discarded and **copying is not
natural**: copy after a coin flip gives two equal bits, two coin flips
give two independent ones. Braid's base is cartesian, so `dup` there
*is* natural — `examples/laws.braid` has the normalizer **prove**
`dup ; f f = f ; dup` for an arbitrary word — and a model of the
`Doctrine` whose hom-object is a **stochastic map** is the Markov
category `with M` maps into. So the distinction is drawn structurally:

```braid
def twoEqualE with Enum = half ; flip ; dup        -- ONE flip, copied
def twoIndepE with Enum = twoBiases ; bothFlipE    -- TWO flips
```

and the two `report`s differ — `{HH: ½, TT: ½}` against four cells of
¼ — in **all three models**. Nothing in the file declares that they
should; `dup` is transported by the functor, and the disagreement is
what the model *is*.

**A generator is an ENTRY at a kernel.** A hom-object `k(a, b)` names
one object on each side and there is no `k(•, b)`, because `•` is not a
wire. So a distribution is written as the kernel it is —
`flip : • ⇒ k(Float, Bool)` — and the bias arrives on the wire the
kernel consumes, produced by an ordinary base stage *inside* the
transported scope (`half = (n -> 0.5)`, one wire in, one wire out, so
the functor embeds it). Nothing special-cases a parameter. `report :
k(Int, b) ⇒ d(b)` is the **exit**, and its result is a theory
parameter — a *constructor* parameter this time, `d(_)`, since what a
model hands back about a kernel is `Weighted(b)`, `Draws(b)` or
`Reach(b)`. `Int` stands in for the monoidal unit the Doctrine has no
name for, and `report` runs at 0.

**Three models**: `Enum` (the finite distribution monad's Kleisli
category — `compose` is bind with the weights multiplied, exact),
`Sampler` (a seed threaded as a resource, a 48-bit LCG written in
Braid, so every printed count is reproducible), `Nondet` (the support
— a weight is a bit). The doctrine's five category laws run for all
three, at *stochastic* evidence, before the file prints. `Prob` also
declares a strength of its **own**, `under : k(a, b) ⇒ k(c a, c b)`,
because a Markov category's generators are carriers at a fixed width
and nothing in the base can widen a carrier; there is no pairing in it,
because over stacks whiskering is concatenation.

**And what it refuses.** `transformation Expect in Enum ⇒ anything` is
not declarable and the reason is mathematics, not machinery:
E[g(X)] ≠ g(E[X]), so expectation does not preserve composition.
What it *is* a homomorphism of is the convex structure, and that is a
second, one-carrier theory in the same file (`theory Convex(m)`, the
fair mixture) with `transformation Expect in Mixtures ⇒ Means` checked
at four squares. `Sampler ⇒ Enum` has no component at all — a sample
is not a function of the distribution. `Support : Enum ⇒ Nondet` is
mathematically a homomorphism and is *still* refused, at the `under`
square, for a reason worth knowing: a component must be generic in the
hom-object's arguments, so it can never **run** the carrier, and the
two sides are then closures that only the normalizer could weigh. See
§14.

### `Code`: reflection and splicing

`reflect` turns a quotation into its **spine**: `Code = List(Stage)`,
`Stage = List(Atom)`, `data Atom = (prim | int | str | sym | quote |
row | group)`. Lambdas reflect as pure wiring (abstraction
elimination) — **every** binder, open ones and the naming form
included, and whatever the body contains: injections, `merge`, open
groups. The parameter block is treated as a *resource* for the body's
duration — parked as the deepest wires, exactly where `with` parks a
resource, and every body stage routed over it with a leading `_` per
parameter; open-arity atoms eat upward and never reach it, a fetch is
a `dup` on the block swapped up into place, and the block is dropped
once at the end. **True closures reflect too** *(2026-09-12)*: a
parameter used inside a quotation becomes a `capture` and one used
inside a row becomes a `dist2` — or, for a wider row or one with a
residual, the generator `#dist:K` (§6) — so `reflect` is **total on
binder code**, full stop (the two corners §14 used to list closed with
stage 5a⅞). Code is an ordinary list — slice with `take`, transform
with `map`, reverse for the GLA transpose (`examples/transpose.braid`,
`code.braid`). `evalAs` checks the code against a
witness and runs it; failures ride the miss track *with the untouched
segment as evidence*. `unparse`/`parse` + `readFile`/`writeFile`
round-trip code through disk (`examples/io.braid`).
`box : Fn⟨ρ0 ⇒ ρ1⟩ Code ⇒ Fn⟨ρ0 ⇒ (ρ1 | Str ρ0)⟩` defers instead of
running — the other half of `reflect`'s round trip.

**Cut soundness** (`examples/cuts.braid`): Braid is not
token-concatenative, but at spine granularity the concatenative
property is a runnable theorem — every stage-boundary cut yields two
runnable pieces with `run(prefix) ; run(suffix) = run(whole)`, atom
slices within a stage are runnable sub-tensors, and any slice boxes.

### The splice check

Code that will only exist at runtime has no type the checker can
discover, so `evalAs` asks you to write one. Its first operand is a
**witness**: an ordinary program whose *arrow* is the expectation the
loaded code must meet. The witness is never applied. It is spelled as a
value because Braid has no type syntax inside terms — a program at the
type you mean is the way to name that type.

```braid
[dup ; *] c (7) ; evalAs      -- "I expect Int ⇒ Int"
```

The context types against the witness's `ρ0 ⇒ ρ1` with ordinary
variables, so a splice's result is ordinary too: usable, printable,
composable. When the splice runs, the loaded code's inferred scheme must
**subsume** the witness's arrow — be at least as general. Subsumption,
not unification, and the difference is the soundness of the whole
mechanism: types are erased by then, so the check cannot know which
instantiation of a polymorphic witness the context chose, and must
demand code that handles every one. Under a witness `[_]` (`a ⇒ a`),
code that is merely `Int ⇒ Int` is refused — unification would have
accepted it at `a := Int` and then run it on a `Str`.

A mismatch rides the miss track with the untouched input segment as
evidence — no crash, same error path as `parse` or `readFile`. And
because the witness is a real program, it is also the fallback: on a
miss it is still sitting there to run.

`box` defers the run the same way, witness and all:

```braid
box : Fn⟨ρ0 ⇒ ρ1⟩ Code ⇒ Fn⟨ρ0 ⇒ (ρ1 | Str ρ0)⟩
```

Cutting a program (`examples/cuts.braid`) is where this is felt: a cut
names an intermediate type the whole program never mentions, and it
differs per cut. Each cut states its own witnesses. That obligation is
the honest price — the type between the halves is a fact about the cut,
not about the program, so someone has to say it.

The code runs in the *witness's* scope — the words it may call are the
ones the witness could — so a prelude word that splices on your behalf
(`box`, `lift2`) still runs your code among your defs.

**Transport is the "models" row applied to composition itself**
*(2026-09-13)*. `with Inst` replaces a theory's *generators* by a
model's words and is known to type because `checkInstance` compared
each slot to its declared signature. When the theory has a hom-object
(§8), `with M` replaces the *composition* as well — `;` becomes M's
composition and each stage becomes M's embedding of that stage — and it
is known to type for exactly the same reason, plus the shape reading at
the `model` line. A functor out of a free category is determined on
generators; transport is what you get when you let it move the
composition too, and the price is that the result lives in the model's
hom-objects rather than in the base. The receipt records which category
you are in, and the carrier is what the label adds to the objects (§3).

See `examples/cuts.braid` for splices in context.

### Functors, and the ones known to type

A **functor** (§8) is a pure GRAPH MORPHISM — `Fn⟨Stage ⇒ Code⟩`, one
image per generator — extended along a scope's wiring by `with`. A
functor out of a free category *is* a graph morphism, so the extension
is the declaration's meaning and is computed rather than written
(`stagewise`); the extension is also a word `F : Code ⇒ Code`, which is
what `lift2 [F]` applies at run time. `reflect` forgets types — it goes from typed programs
down to `Code` — so a functor works on the untyped floor, and typing
its output is a *lifting* problem: does a typing exist over this
rewritten program? Braid answers it the only honest way, by
re-inferring the expansion at the splice (principal types; nothing is
trusted), and when no typing exists the error is reported inside code
you did not write — every such message carries the expansion. That is
the design's one real fragility, and the answer to it is a short list
of functors whose lifts are **guaranteed**, checked once rather than
per use:

| functor | what it is | checked by |
|---|---|---|
| a quotation transformer `Fn⟨a ⇒ b⟩ ⇒ Fn⟨…⟩` (`lift`, `logged`, `compose`) | level 1: never leaves the typed world | ordinary inference, at the def |
| `with E` for a resource `E` (or the routing inferred without one) | tensoring, `E ⊗ –` — the model `model E in Doctrine` generates, transported in fused form; and a binder's parameter block is the same functor, `P ⋉ –` (§12 above) | the elaborator's routing, which is that model's evaluator |
| `functor F = η ; interpose` | whiskering: `η` after every cut, `η : ρ ⇒ ρ` or `E ρ ⇒ E ρ` | `checkedStage`, by subsumption, inside `interpose` |
| `with Inst` for a model | a model of the theory: every generator replaced by a typed image | `checkInstance` (§8) |
| a model of `Base`, `model Opt in Base = p = q, …` | a typed generator image, applied atomwise | `subsumes`, once per binding at the declaration (§8) |
| an **object-mapped** model of `Base`, `model Mod in Base(Int ↦ Mod7 via reduce)` | the same, with the OBJECT half written: a substitution on types, `via` on literals, unfolding on defs — so it changes the arrow and not just the words | `subsumes` at the generator's arrow **with the substitution applied**, once per binding; and a word that mentions the mapped type with no image is refused by name at the scope (§8) |
| a **transport** `with Circuits` on a model whose theory is declared `in Doctrine` | a model applied to COMPOSITION: a stage ↦ the embedding, `;` ↦ the composition | `checkInstance` on the slots, once, plus the doctrine's claim checked at the `theory` line (§8) |
| `lift2 [m]` on any `Code ⇒ Code` `m` | the runtime lift | per program, at run time; never fails — it falls back |

Everything not in the table — delete a stage, reorder, reverse,
choose by neighbour — is re-inferred and may fail. Such functors are
not wrong; they are **audited** rather than **guaranteed** (laws over
`Code`, `sameCode` on expansions, §12).

**The closure gate is lifted** *(2026-09-12; it read "one limit is on
the floor, not on any row").* `reflect` used to refuse a binder
parameter captured in a quotation or a row component, and a knot (§8)
arrives as exactly such a parameter — so a `with F` scope
containing a knot *itself* was refused before any functor ran
(*`with Traced`: Unknown primitive: self*). Abstraction elimination now
has wiring to translate a capture into: `capture` under a quote,
`dist2` over a row (§6, §10). That is table row 2 (`P ⋉ –`) over the
cartesian **closed** structure rather than the cartesian one, and it is
a derivation, not three new primitives —
`design-macros.md`, the 2026-09-12 amendment. The two corners it left
open — a **residual** row `(p | q | ---)`, and a flat row of three or
more tracks — closed the same day with the generator `#dist:K` (§6), so
`reflect` is now total on binder code, full stop.
`sameCode` caught up on 2026-09-13: it now runs
elimination first, so two spellings of a capturing binder are
*decided*, and it agrees with `sameCodeC` on every program (§12.9).

**Why `interpose` checks what it checks.** The stage it inserts must
type at *every* cut, and the cuts have different widths. A stage that
touches no wire is `∀ρ. ρ ⇒ ρ` — an endomorphism of the unit, whiskered
by whatever the cut carries; with a resource routed deepest, `E ρ ⇒ E
ρ` (`burn : • =Fuel> •` is literally one). The check is **subsumption**
against `ρ ⇒ ρ` with `ρ` rigid, not unification: unifying would bless
`Int ρ ⇒ Int ρ` at `ρ := Int ρ'`, a stage that needs a wire and dies
at the first empty cut. Refusals name the stage and its real type:

```text
interpose: `dup pass >> print pass` is a0 ρ0 =IO> a0 ρ0, which reads a
wire; a stage inserted at every cut must be ρ ⇒ ρ, or E ρ ⇒ E ρ for
resource wires E routed beneath the whole scope
```

And that refusal is the whole story of the tracer: the tempting trace
`dup ... ; print ...` reads a wire, so it cannot go everywhere (and on
a binder body it prints the parameter block, which is the true deepest
wire). The tracer that lifts at every cut reads nothing — `"after dup"
pass ; print pass` — and gets its content from the functor, which has
the stage in hand (`examples/traced.braid`). This is possible because
`Code` carries **names**, not closures: `.burn` re-instantiates its
scheme at each splice site, which is where width-polymorphism comes
from; a `Fn⟨ρ ⇒ ρ⟩` value would be fixed at one `ρ`.

**The ladder, from the user's side.** Every functor is `Fn⟨a ⇒ b⟩ ⇒
something better` (`examples/lifting.braid`), and a functor's
`Code ⇒ Code` extension becomes one of those two ways: `with F` at
elaboration (the
expansion is re-inferred, and its arrow is the receipt) or `lift2 [F]`
at run time, where the program is its own witness — the result has the
program's arrow *by construction* and a rewrite the witness refuses
leaves the original running (`examples/metered.braid`). The type
system blesses exactly that and nothing weaker: it cannot say "this
rewrite preserves every program's type" as a rank-1 `Fn` type, because
*unification blesses a call; subsumption blesses a rule* — and a rule
is a declaration, checked once. That declaration is `model … in Base`
(§8): the
rung of the ladder where a rewrite stops being audited and becomes
guaranteed, at the cost of saying *which* rewrites, by name, up front.

`stagewise`/`atomwise` are `flatMap` on the spine, and `stagewise` is
the EXTENSION a `functor` declaration computes: functorial by the
universal property (a stage's image depends on that stage alone), which
is a law that comes free, not a promise that the result types.

**The receipt.** `with F` mints `F` onto the manifest of everything it
elaborated (§3), so a rewrite that changes no requirement — a tracer,
an optimizer — is still recorded, and the record travels to every
caller by composition. Mechanically the receipt is a *word*: `with@F :
∀ρ. ρ =F> ρ`, `pass` with a label, prepended to the expansion — the
same unit endomorphism `interpose` inserts, doing nothing but being
typed. Three consequences, in rising order of usefulness:

- it is a stage, so it survives `reflect`: a reflected traced program
  reads `with@Traced >> dup >> …`, and splicing it somewhere else
  carries the label rather than losing it;
- it cannot be forged. Writing `with@Traced` yourself is an error — *a
  label is minted by a scope, never written by hand* — which is the
  difference between provenance and a comment. The rule is the
  character, not the word: **`@` is the compiler's**, so a model's
  generated slot def is refused in source the same way and points at
  the scope that reaches it — *`Loud@emit` is the compiler's spelling
  of a slot: reach it with `with Loud`* (§8);
- it is part of the type, so every place that compares a written type
  to code checks it: an `evalAs` witness, a theory's declared slot, a
  `Fn⟨…⟩` in a declaration. `Fn⟨Int ⇒ Int⟩` refuses instrumented code
  with *Cannot unify effects: IO Traced vs pure*. An unlabelled type
  is a claim that no functor touched the code.

What a label does *not* say: that every stage of the word is in the
functor's image. Labels union along composition, so adding one
unmetered stage to a `=Metered>` word keeps the label; "wholly in the
image" is the dual (intersecting) question, and Braid does not answer
it yet (`design-macros.md`, the coeffect section).

### Deciding a law: `sameCode`

`sameCode : Fn⟨Σ ⇒ Θ⟩ Fn⟨Σ ⇒ Θ⟩ ⇒ Bool` answers whether two programs
are the **same morphism**, by normalizing rather than testing.
`sameCodeC : Code Code ⇒ Bool` asks the same question of two `Code`
values — the form a law about a *functor* has to take, since a functor
returns `Code`. Since 2026-09-13 they are **one procedure**: `sameCode`
runs abstraction elimination first (the path `reflect` already took), so
the two words agree on every program.

The fragment they decide is the free **bicartesian closed** category
over the words a program mentions: wiring (`id`/`_`/`dup`/`drop`/`swap`/
`pass`), composition and juxtaposition; literals as nullary constants;
quotations with `capture` and `ev` — β *and* η, and `ev` of a function
that arrived as a **wire** whenever its arrow is closed; the coproduct's structure maps
(`alt1`…`altN`, a code row, `merge`, `into`, `dist2`); and every word
with a closed arity, treated as **uninterpreted**. Defs inside the
fragment are inlined (so `sameCode` sees through your own words); a def
already being expanded is recursive and stays opaque.

The normal form is a **case tree**: follow an injection you know (β for
the coproduct), run a quotation you hold (β for the exponential), and
where a sum's injection is unknown, *split* — one branch per track,
with the scrutinee refined for **both** programs at once. Leaves are
tuples of symbolic terms; two programs are equal when they consume the
same wires and agree at every leaf. The design record is
`design-macros.md`, "the normal form for sums" (2026-09-13); the
references are Cockett on distributive categories, Carboni–Lack–Walters
on extensivity (which is what makes a split a partition), and Lafont on
presentations with canonical forms.

```text
[dup ; _ dup] [dup ; dup _]       ; sameCode   # true  — coassociativity
[dup ; toStr toStr] [toStr ; dup] ; sameCode   # true  — copy is natural
[toStr ; dup] [dup ; toStr _]     ; sameCode   # false
[(x -> x x)] [dup]                ; sameCode   # true  — binders decided
[[dup ; swap]] [[dup]]            ; sameCode   # true  — inside a quote
[[dup] ... ; ev] [dup]            ; sameCode   # true  — β for ⇒
```

The third line is the point: a law about *an arbitrary word* is proved
for every input, which no amount of sampling can do.

**Read the two answers asymmetrically.** `true` means the programs agree
under **every** interpretation of the words — a theorem. `false` means
they are not the same morphism of the *free* category, which is **not** a
counterexample at any particular type: `2 _ ; *` and `dup ; +` agree on
every `Int`, and `sameCode` still says false, because `*` and `+` are
only words to it. Laws that need `+` to be commutative, or need `Int`
arithmetic, belong with the sampled laws — deciding those means
normalizing modulo an equational theory (AC, ACU, a field) instead of a
free one.

Outside the fragment `sameCode` **errors** rather than answering,
because "I cannot tell" is not "they differ". Every refusal names what
stopped it — **everywhere**, since 2026-09-14. Until that date one
corner leaked: comparing two quotations whose captures are not pairwise
equal (and the two eta comparisons beside it) wrapped the extensional
answer in a fallback that turned a refusal into `false`, so that no
verdict standing before the extensional route arrived would be
withdrawn. That made `false` mean *could not decide* in that one place
and *provably different* in every other, which is a verdict nothing
downstream can trust. The fallback is gone; the refusal propagates.

**What is decided, exactly** *(2026-09-13)*:

| stated over | decided? |
|---|---|
| wiring, composition, juxtaposition, uninterpreted words with closed arity | **yes** — a theorem for every input and every interpretation |
| binders, with or without capture | **yes** — `sameCode` eliminates them first, so it and `sameCodeC` agree |
| a quotation: `[p] ; ev = p`, `capture ; ev` as substitution, two quotes compared by their bodies' normal forms | **yes** |
| the coproduct's β and η, the track swap, `dist2`/`undist2`, `into`'s two equations, `case2`…`case4`, `cond`, `otherwise` | **yes** — `examples/distributive.braid` has seven of them as audited laws |
| a row over an **arbitrary** sum, residual or closed, when the row's tracks are closed stacks | **yes** — by case split; the residual is compared *semantically*, so `(f \| ---)` and `(f \| pass)` at a closed two-track sum are the same morphism |
| `[b] ; fix` — two `fix` bodies compared in normal form | **yes**, provided the body does not apply the self wire. A def written under `with Recursive` is held **opaque** for the same reason `fix` is: inlining a knot can only trade a verdict for a refusal |
| `ev` of a wire whose **arrow is closed** — a hom-object's `Fn⟨a ⇒ b⟩`, anything the type pins to a width | **yes** *(2026-09-13)* — a neutral application, like any uninterpreted word; `capture` of such a wire is the partial application it denotes, and η holds (a quotation against the wire itself) |
| `ev` of a wire whose **arrow is open** (`self ... ; ev` in a knot body, a handler slot, a bare `Fn` inference left unpinned) | **no**: its segment is an open stack variable, so there is no arity to give it |
| `loop`, and the Elgot identity `loop f = f ; [loop f] into` | **no**: a fixpoint equation is an axiom of an iteration theory, not an equation of the free category — `examples/into.braid` runs it at sample points |
| a sum whose injection is unknown and whose row has **no closed tracks** (an open row variable σ) | **no**: unnamed tracks have no widths, so there is no partition |
| anything needing `+` to be commutative, or `Int` arithmetic | **no** — sampled laws; the free category cannot see it |

The two bounds — a tick budget per run, and 16 nested case splits — are
also reported as *outside the structural fragment*. Running out of room
is not a verdict.

**Two kinds of claim, kept apart.** *Idempotence* — `F(F p) = F p` — is
a **functor law**: it is about `F`, at every program, and it belongs in
a `theory` that models are audited against. *Image membership* —
`F(p) = p` — is a **program assertion**: it is about one particular
program, so it is written where that program is. The second is only
*meaningful* because the first holds, which is why a theory offering
image assertions must declare idempotence. And image membership
inherits the boundary above exactly: `twice = dup ; +` and `double =
2 _ ; *` agree on every `Int`, so a binding `twice = double` changes no
meaning — but it is visible in the free category, and `twice` is
therefore reported outside the image. Both kinds are shown, side by
side, in `examples/optimizer.braid`.

### Reflected types *(2026-09-16)*

`Code` reflects a **program**. These reflect its **type**, and a
**declaration**. They are not a new layer: every one of them answers
with a fact the checker already holds, so they are pure, they are cheap,
and they may be called at **elaboration** — a functor's graph morphism
is an ordinary pure word, and so is a declaration-time program, so a
derivation that reads a declaration is an ordinary Braid word too.

```text
typeOfWord : Str      ⇒ (TypeRep | Str)     a word's principal scheme
typeOfCode : Code     ⇒ (TypeRep | Str)     a Code value's, inferred here
declOf     : Str      ⇒ (Decl | Str)        a data/type/theory declaration
showType   : TypeRep  ⇒ Str                 the display `:t` prints
envOf      : • ⇒ List(Box(Str TypeRep))     every word in scope
```

In the REPL, `:tc <prog>` runs a line and asks `typeOfCode` about the
one value it left. It is a different question from `:t`, not a second
spelling of it — `:t [dup ; +] ; getCode` is `• ⇒ Code`, and what you
wanted to know is `Int ⇒ Int`.

They are **prims** (§9), not declarations: they read the checker's own
tables, which is exactly the criterion the kernel uses (`README`).

**The rep.** `data TypeRep` mirrors the checker's `Ty`, `SType`,
`EffRow` and `Arrow` in **nine** alternatives — a base type by name, a
type **variable** by name, a declared type at its argument stacks, `Fn`
around an arrow, a sum (its alternatives and the row tail), a stack's
**open end**, an **arrow** (in, out, the grade's labels, the effect
tail), a repeated closed **segment** with its width (`Aⁿ`), and **`Fin`**
at a width. A stack is `type StackRep = List(TypeRep)`, front wire
first; the open end and the repeated segment are the two alternatives
that are **not wires** — each stands in a stack and nowhere else, the
open end last and the segment for however many wires its width says.
`foldTypeRep` is the nine-way eliminator, and `baseOf`, `wire?`,
`stackWidth`, `widthOf` and `firstAlt` (the prelude) are the small
vocabulary written on it.

**Equality is `eq?` — after normalization.** `typeOfWord` normalizes
before it answers (`normalizeArrow`: variables become `a0`, `ρ0`, `σ0`,
`ε0` in order of first appearance), so two schemes are the same scheme
exactly when their reps are `eq?`. A rep you assembled by hand carries
no such guarantee: `eq?` on an unnormalized rep compares variable
*names*, which is a different question.

**The width tier** *(2026-09-16)*. A width is a **second sort** — an
exponent is not a type — so it has a rep of its own rather than a
`TypeRep` alternative:

```text
data WidthRep = (Int | Sym Int)      lit k | var n at offset k
```

`Aⁿ` is a **stack segment** repeated `n` times, which is why its rep
stands in a `StackRep` beside the open end and `wire?` says false for
it; `Fin(n)` *is* a wire and carries the same `WidthRep`. The rule the
rep must not break is one sentence: **never flatten a variable width
into a type.** A concrete width may reflect expanded, because the
checker itself expands it (`sexp` leaves no `Aⁿ` for `Int³` — it *is*
three wires); a variable one comes back with its variable and its
offset, so `typeOfWord "weaken"` is `Fin(n0) ⇒ Fin(n0+1)` and not
`Fin(n0) ⇒ Fin(n0)`. `typeOfWord "pack"`, `"zipN"`, `"mapN"`,
`"checkedAt"` and `"indicesN"` all answer now; nothing in the prelude
misses for want of a rep, and the differential check
(`typeOfWord w` = `typeOfCode [w]`) went from 182 words to 210.

**What is not admitted, on its own merits.** There is no
`∀a. a ⇒ TypeRep`. Nothing above takes a **wire** and answers its type:
the inputs are a *name* and (§below) *code*, both static. Such a word
could not be written even if it were wanted — no atom produces a
`TypeRep` from a value — and that is what keeps the free theorems:
`∀a. a ⇒ a` is still the identity, because nothing inside it can ask
what `a` is.

**No type families.** A type-level function is an ordinary Braid word
on `TypeRep` values, run at elaboration, producing a declaration or a
program. It never enters unification, where a non-injective function
would break principal types. That is the whole rule, and
`examples/typerep.braid` is where it is exercised: `colsOf : TypeRep ⇒
TypeRep` is the column store's object map, `P(x, y) ↦ P(Cols x, Cols
y)` with `t ↦ List(t)` at the base — non-injective, and living entirely
outside the type system.

**`typeOfCode` and elaboration.** Inferring a Code value's type in the
prefix scope is sound on a closed spine, and every def is one: since
5a½ `with Recursive` rewrites to a closed spine over `#fix`, so there
is no `.recurse` atom to loop on. It cannot see the def it is inside,
either — **elaboration precedes inference**, so when a `functor` runs,
the word it is building has no type yet. The types available are the
prefix scope's, fixed before this declaration was reached.

Three things `examples/typerep.braid` does with it:

- **diagram cuts.** `cuts : Code ⇒ List(Code)` splits a spine into its
  connected components — atoms as nodes, wires as edges, each atom's
  arity read off `typeOfCode` of the one-atom spine that calls it. So
  `1 2 3 4 ; + _ _ ; _ *` comes back as `1 2 ; + ; _` and `3 4 ; _ _ ;
  *`: two halves with no wire between them, and nothing in the *text*
  said so. Analysis, not runtime parallelism — what it licenses is the
  reading that a component whose grade is ∅ is **central** (interchange
  holds) and may be reordered or run anywhere, while one carrying a
  label may not, because the label is the claim that its order is
  observable.
- **the bootstrap seed.** `envOf` is every word in scope with its
  scheme, and for each there are two ways to ask its type: look the word
  up, or hand the checker the one-atom program that calls it. They
  agree — pinned as a test over all 182 prelude words that have a rep,
  **up to the effect tail**: a prim's scheme is written with a closed
  pure row, an inferred one's row is open. The display hides effect
  tails, so it hides exactly this; the test closes both sides and
  compares. This is the first rung of the type-system bootstrap
  (`design-macros.md`, 2026-09-16).
- **deriving at declaration time.** A declaration-time program may call
  the reflection words, so `(.Row ; cellsOfSym) "rowCells" ; defW`
  declares the printer a declaration implies. `rowCells` is
  `Row ⇒ List(Str)` and wears no receipt, because no scope ran: the gap
  below closed on 2026-09-18.

### Deriving: a printer nobody wrote

`declOf` hands back a declaration as data, so a word that is a function
*of the declaration* can be derived rather than written. The first
customer is a data frame's row printer:

```braid
cellsFor : Decl ⇒ Code
```

— the prelude word that turns a `data` declaration with named fields
into the `Code` of `(r -> (r ; f₁) (r ; f₂ ; toStr) … ; pack)`, reading
the field names and their types off the rep (`toStr` on every field
that is not already a `Str`). `examples/frame.braid` uses it:

```braid
def cellsWitness = (r -> (r ; sym) ; single)
def tradesCode   = "Trades" ; declOf ; ((d -> d ; cellsFor) | drop ; nil) ; merge
def tradeCells   =
    t -> [cellsWitness] (tradesCode) (t) ; evalAs ; ((c -> c) | (e x -> e ; single)) ; merge
```

and prints byte for byte what the hand-written line printed. The
**witness** is the expectation: `Trades ⇒ List(Str)`, spelled as a
program because Braid has no type syntax inside terms (§12, the splice
check).

**Why this one still pays for `evalAs`.** Deriving at *declaration
time* is the general answer, and stage 8's substrate is it: a top-level
`• =Dict> •` program calling `defW` declares a def whose body was
computed, with no scope to mint a receipt, and
`examples/typerep.braid`'s `rowCells` is derived that way at
`Row ⇒ List(Str)`. `tradeCells` cannot be, and the reason is the
LOADER's: `Trades` is declared by a `table`, which reads a CSV at check
time, and a declaration line may do no IO. So this derivation happens
later, at run time, against a witness. The gap that used to be stated
here — "a declaration form whose body is computed" — closed on
2026-09-18; this is a different one, and it is about when a file is
read.

One consequence worth stating: because `cellsFor` must stay **pure**
(an `=Recursive>` printer would not fit `embed` either), it is written
as a fold over the field names carrying the remaining types, not as
`zip` — the prelude's `zip` ties a knot.

## 13. Open arity and exponents (summary)

Words whose input has an open region (`ρ` tail or `aⁿ` exponent) work
at every width. Rules (full version: `guide-open-arity.md`):

1. Open words go **last** in their stage; non-final they are closed to
   zero width (an `… vs •` error means "not last").
2. Fixed arguments slide **under** the bundle via `X ...`.
3. Widths are **erased**: no runtime tags — the final segment's actual
   extent is the witness. Consequences: no width-producing words from
   nothing, no branching on width (elimination is the fold), one open
   region per input.
4. A def whose inferred input is open is itself an open word
   (`def total = [+] 0 ... >> foldExp : Intⁿ ⇒ Int` — one body, every
   width, including n = 0).

The index words `at` and `indicesN` are exponent-shaped, so rule 1
holds for them too: final atom of their stage (§9).

The **base** of an exponent may be the terminal object *(2026-09-20)*:
`•^n` — equivalently `one^n` or `(•)^n` — is the zero-wide bundle, and
`•^k` is `•` for every literal k. The parenthesized form always parsed;
the bare one does now, which is what makes `•` an exponent base like
any other segment (§5, `design-exponents.md`).

### 13.1 One catamorphism, four motives *(2026-09-21)*

`Aⁿ` is a stack SEGMENT repeated n times, and the family `n ↦ Aⁿ` is
the **initial algebra** in `[ℕ, C]` — the functor category of
width-indexed objects. A catamorphism out of an initial algebra is
determined by its **motive** (its carrier), and every fold-shaped word
over a bundle is the same catamorphism at a different one:

| word | motive `n ↦ …` | what that makes it |
|---|---|---|
| `foldExp` | `r` (constant) | collapse to one wire |
| `mapN` | `bⁿ` | rebuild the container |
| `mapAccumN` | `r ⇒ r bⁿ` | thread state while rebuilding |
| `unzipN` | `aⁿ bⁿ` | split into two containers |

The family was plural because **Braid cannot write a width-indexed
motive** — there is no way to say "the carrier at n is `bⁿ`" in a
scheme. One prim that carries the accumulator explicitly writes all of
them anyway, because traversal in the State applicative is all of
traversability for a finitary container (READING, Gibbons & Oliveira;
Jaskelioff & Rypáček). So `mapAccumN` is the prim and `foldExp`,
`foldExp2`, `mapN` and `mapN2` are prelude defs with the same schemes.

`unzipN` is the one motive that is NOT reachable that way: its carrier
is two containers, and a catamorphism whose step returns one wire per
element cannot produce two bundles. `dupN` is not a catamorphism at
all — it is the diagonal of the **Naperian** reading, `Aⁿ ≅ A^Fin(n)`
(READING, Gibbons), which is a second structure on the same object and
the one `zipN`/`unzipN` come from. The two structures are independent:
the initial algebra gives the fold, the Naperian view gives the zip.

### 13.2 The one-wire-element discipline

**`mapAccumN`'s accumulator is a WIRE, and so is its element.** That is
forced by erasure, not taste. The runtime is handed one number — the
final segment's length — and with a wire accumulator `n = total − 1`,
so the split is determined. A stack accumulator would leave
`|ρ| + n = total` with nothing to fix it, and a k-wire element would
leave `k · n = total` with nothing to fix k. Both are the erasure
argument that rules out segment variables (`design-segments.md` §6.1).

A wider element therefore **boxes**: `Box : ρ0 ⇒ Box(ρ0)` turns any
segment into one wire, and `Box(a b)ⁿ` is a bundle of pairs whose
elements a one-wire word can read (`unBox` inside the step). `zipN`
merges two lanes straight into that form; `unzipN` splits the flat,
stack-native `(a b)ⁿ`; so `unzipN >> zipN` is the flat → boxed
normalizer, and the two-wire twins are one line each over it:

```braid
def mapN2 = (f ... -> unzipN >> zipN >> [(p -> f (p >> unBox) >> ev)] ... >> mapN)
```

Two consequences worth knowing. **`b := •` is not reachable**: the
output element is a WIRE variable and `•` is not a wire, so `foldExp`
is not `mapAccumN` at an empty output. It emits a copy of the
accumulator instead and throws the bundle away — and the only idiom
that can drop a segment of unknown width from under a wire is a group
that forgets it, `(r ... -> r (... >> forget))`; a binder that simply
omits `...` closes the segment to `•` rather than discarding it.
**`at` and `indicesN` stay prims**: `indicesN` introduces a `Fin(n)`
naming the bundle's own width, which no user quotation can write, and
`at` would need an accumulator inhabited before the first element —
there is no `a` to start from. Both are index introductions, fenced by
the witness rule above (§9, `design-indices.md`).

## 14. Sharp edges (things the checker will teach you)

**Every refusal says where, and most say which rule** *(2026-09-15)*. A
refusal from a file reads `path:line`, and `, in def X` when it is
inside one; a main program names the line of the **stage** that failed,
not the line main starts on; an imported file names **its own** path.

```text
examples/frame.braid:212, in def notional: Cannot unify stacks: • vs Str
examples/frame.braid:376: Cannot unify stacks: • vs Str
```

Checked without a file — a REPL session, a string — the line is still
the line of the text that was handed over (`line 3, in def f: …`);
with only one line of it there is nothing to name and nothing is said.
A stage carried onto the next line by `\`, `;` or `>>` reports the line
it **started** on, which is the only honest answer for a stage that
spans lines. Seven shapes also carry a one-line **hint** naming the rule
and the fix; each fires only on something the checker can see in the
source, and says "usually" where it is a guess. They are marked ✦ below.

This section is a **catalogue**: it is kept as reference, so entries are
corrected in place rather than dated one by one.

### The message classes

- **`Cannot unify stacks: Γ vs Δ`** — two stages met and the wires did
  not line up. The two sides are what was LEFT where the match ran out,
  the left-hand stage's output first and the right-hand stage's input
  second, so `• vs Int` reads "nothing left to give, one Int still
  wanted". Count wires. Step over the ones this stage does not touch with `_`, pass
  the rest along with `...`, or split the stage. This is also what
  `one` refuses with: `1 ; one` is *Cannot unify stacks: Int vs •*,
  because there are no implicit remainders — a bare `; one ;` in a
  spine asserts the stack is **empty**. `one ...` is the whiskered
  reading, and beside other atoms in a tensor stage `one` constrains
  nothing (§5). ✦ If the failing line
  begins with `(` or `[` and the line above did not say it was
  unfinished, the hint says so: *a new line is a new stage, so this `(`
  does not continue the line above* — end that line with `\`, or write
  `;` at either end (§4). ✦ If the failing line holds a group that is
  **not** the last atom of its stage, the hint says the group is
  instantiated **closed**, so pin its width with `id` or move it last.
- **`Cannot unify stacks (exponent base | exponent split | open tail
  after exponent): …`** — the same failure inside a segment with an
  exponent (`Intⁿ`). The width could not be split where the other side
  needed it. Write the width you mean, or keep the two sides' exponents
  on the same variable (§13).
- **`Cannot unify types: A vs B`** — one wire, two types. The stack
  lined up and a wire did not. ✦ If the failing line begins with `|`,
  the hint says what it usually is: a row arm on its own line is a
  **stage**, so the arms compose at `>>` instead of standing side by
  side — carry each line of the row on with `\`, or put the row on one
  line (§4).
- **`Cannot unify types: Int vs Float. …`** — the same, with the
  reason spelled out: Braid has no numeric tower and no overloading.
  `+ - * div mod lt?` are Int words, `fadd fsub fmul fdiv flt?` are
  Float words, and no word is shared. Cross with `toFloat` or `floor`,
  written where you mean it (§9).
- **`Cannot unify types: (A | σ) vs T`** ✦ — an **open injection** met
  a written type. `alt1` says "at least this alternative"; a written
  type says exactly these. Close the row with `(pass | pass)`, which is
  the idiom for "and nothing more" (§5).
- **`Cannot unify exponents: e vs f`** — two widths that must be equal
  are not. A literal width and a variable one unify; two different
  literals do not.
- **`Cannot unify effects: L vs M (…)`** — the **sandbox**. Composition
  joins grades, so a composite carries every label its parts do; a
  **written** manifest is exact and absorbs nothing. The parenthesis
  names the fix, and there are two of them: *write `=L>` on that arrow*
  (you meant it) or *keep this code label-free* (you did not). Two
  written manifests inside a `Fn⟨…⟩` are unified rather than ordered —
  a `Fn` type is invariant in its arrow (§3). ✦ When one of the
  labels is a **resource** the module declares, the hint says the other
  thing instead — **you forgot to install**: seed the wire at the call
  site (`("" ; Log)`) or wrap the program in a handler that seeds and
  unwraps, rather than writing the label. It fires on the wire shape
  (`Cannot unify types: Int vs Log`) too, which is where a missing
  install more often lands, because the carrier stays a wire.
- **`Occurs check failed[ on stack | on exponent | on effect | on sum
  row]: v in T`** — the only solution is an infinite type. ✦ Under
  `with Recursive`, with the variable inside a sum, the hint says what it
  almost always is: *a recursive call inside a row usually wants
  `merge` after the row* — the row leaves the alternatives open and the
  knot cannot close them.
- **`'v' is universally quantified in the expected type but this code
  requires it to be …`** — a **written** type promised to work for
  every choice of `v` and the code pins it. Either the code is less
  general than the signature claims, or the signature meant a concrete
  type. (This is the rigid half of `subsumes`: a model slot against its
  theory, a `model … in Base` binding, a witness against an `evalAs`.)
- **`An open-arity atom must be the final atom of its tensor stage`** —
  an open binder, a `...`, or a word whose arrow has an open tail, with
  atoms to its right. Move it last, or give it a group of its own
  (§4, §13).
- **`Expected a tensor stage, got: T`** — the parser wanted an atom and
  found punctuation. Usually a doubled operator (`; ;`), or a `|` where
  a stage was due.
- **`Unclosed group (expected ')')` / `Unclosed quotation (expected
  ']')`** — a bracket that no line closes. A bracket may span lines;
  the def body ends when the brackets balance.
- **``A `\` continues a tensor stage onto the next line, so …``** —
  two of them: a `\` that is not the last thing on its line, and a `\`
  with no line after it (§4).
- **``` `| ...` used to mean the residual; write `| ---` … ```** — `...`
  continues **wires**, `---` continues **alternatives**. An old row is
  one of the two and the compiler will not guess (§5).
- **`Unknown primitive: n`** — a name nothing in scope defines, named
  at the stage that writes it. A def is in scope from its own line
  down, so a call above its definition is this message.
- **``` `X` refers to itself: write `with Recursive` in its header ```**
  — recursion is a **marker**. The same message with *(`recurse` named
  the definition being written)* is the word `recurse` used outside any
  `with Recursive` (§8).
- **``` Type T: `T` occurs to the LEFT of an arrow in its own
  declaration ```** — **strict positivity**. A `data` (or `model … in
  Doctrine`) body may name itself in an arrow's **output**, which is
  codata (`data Stream(a) = (a Fn⟨• =Recursive> Stream(a)⟩)`), or under
  no arrow at all (`List`, `Tree`); in an arrow's **input** it is
  refused, at any depth, because that type is the typed Z combinator's
  and makes general recursion type pure. Recursion enters through
  `with Recursive` and nowhere else (§5, §8). The check follows
  polarity through other declared types by their parameters' variance,
  so the indirection `data Neg(a) = Fn⟨a ⇒ Int⟩` then
  `data Bad = Neg(Bad)` is refused too, and through a `type` alias,
  which is expanded before the body is checked. If what you want is a
  self-applying value, it is not expressible.
- **`Duplicate definition: n` / `Duplicate parameter: p` / `Duplicate
  type declaration: T` / `Duplicate resource in `with`: R`** — objects
  are added, never merged. Rename one. A **prim's** name is taken the
  same way: `def one = …` is this message, and `type one = …` is
  *Malformed type declaration*, because `one` is a word and a built-in
  type name since 2026-09-20 (§5, §9).
- **``` `X` leaves M; call it outside `with M` ```** — an **exit** inside
  a transported scope. Not a type error: a scope error, by slot. Call
  it outside, or write the def's header `in M`, which opens the same
  vocabulary and transports nothing (§8).
- **``` `with …` / `in …` ends its scope ```**, and **`… must be
  followed by its body (a newline, ';' or '->')`** — a header word
  takes the rest of the scope as its body, so there has to be a rest.
- **``` `with`: a stage may contain at most one resource operation, and
  it must be alone ```** — and **``` X threads Log, but this scope is
  with Log Counter ```**. The elaborator brings one resource wire up,
  acts, and puts it back; a subset at once would need a permutation it
  will not guess. A word threading **exactly** the scope's resources,
  in order, applies with no routing at all.
- **``` n is the receipt of `with F`, not a word ```**, **``` `T@cellAt`
  is the compiler's spelling of a table's insides ```**, **``` `I@op` is
  the compiler's spelling of a slot ```** — three names source may not
  write. A label is minted by a scope, never written by hand; a `table`
  puts exactly `loadT` and `headerT` in scope; a slot is reached with
  `with I`.
- **``` functor F: w must be a GRAPH MORPHISM — `• ⇒ Fn⟨Stage ⇒ Code⟩`
  … but is … ```** / **``` functor F: w is Code ⇒ Code — an ENDOMAP OF
  THE OBJECT OF MORPHISMS, not a functor ```** *(2026-09-18)* — a
  functor is determined by ONE IMAGE PER GENERATOR, and a `Code ⇒ Code`
  word gives no such thing: no object map, no generator images, no
  laws, and nothing that makes it commute with `;`. The second message
  names the two homes such a word does have — `lift2 [w]` at run time,
  checked against the program's own type with the original as the
  fallback, and a declaration program (`[code] "name" ; defW`) for code
  that is generated rather than rewritten. Nothing is lost (§8).
- **``` functor F: w — <error> (a functor's graph morphism must be
  defined before the functor line) ```** — the ordering rule: a functor
  is runnable before its first use, which is the one place source order
  is semantic (§8).
- **``` interpose: `dup pass >> print pass` is a0 ρ0 =IO> a0 ρ0, which
  reads a wire ```** — a stage inserted at every cut must be `ρ ⇒ ρ`, or
  `E ρ ⇒ E ρ` over resource wires routed beneath the whole scope. A
  stage that reads a wire fails at an empty cut, so it is refused by
  name *before* it is inserted anywhere (§12).
- **``` `resource` is gone since 2026-09-18: a resource IS the model of
  the Doctrine its declaration generates — write `model Log in Doctrine
  = Str` ```** — the keyword was a second spelling for a thing the
  language has one spelling for. `:doc Log` prints the carrier, the
  theory and the model, exactly as it did (§8). Like every retired
  form, it is refused **by name** with the rewrite spelled out, rather
  than failing as an unknown word.
- **``` `defW` is a declaration word: the keyword `def` is parsed into a
  call of it ```** / **``` `Dict` is the dictionary's own wire and may not
  be declared ```** — the names the **declaration layer** owns (§8). A
  keyword line becomes a call of its word, so a module that could shadow
  one could change what `def` means halfway down a file; and `Dict` is
  the wire every declaration word acts on, with no `Dict` and no
  `unDict` anywhere, which is what keeps a program from discharging it.
  Rename yours.
- **``` a DECLARATION LINE is run at check time, above main, so it must
  take nothing and leave nothing (`• =Dict> •`) ```** / **``` a
  DECLARATION LINE runs at check time, before main, so it may not touch
  the world ```** / **``` `theoryW` is a declaration word, and a program
  may not call this one yet ```** — the three rules a **program's** own
  declaration line obeys (§8). It is lifted out of main and run above
  it, so it must leave main's stack as it found it and may not print
  before main does; and of the eleven words `defW` is the one a program may
  call, the other nine declaring things the module's defs are checked
  against. Write the keyword line.
- **``` `div` has no image under model Mod ```** — an **object-mapped**
  model of `Base` (§8) is a functor whose action on objects is a
  substitution, and a word whose scheme mentions the mapped type must
  have an image, a body to unfold, or a retraction to be conjugated
  with. The message names the word, its arrow, the map, and the three
  fixes. A word whose scheme does not mention the type is never in this
  message: the functor is the identity off it.
- **``` model M in Base: `+ = +` is refused: + is used at Mod7 Mod7 ⇒
  Mod7 but + is Int Int ⇒ Int ```** — the same subsumption every
  binding gets, at the generator's arrow **with the object map
  applied**. And **``` `via dup` is refused ```**, the image of the
  literal family checked at `A ⇒ B`; **``` a RETRACTION of c ```**,
  checked the other way.
- **``` `List(Int)` is not a NOMINAL type ```**, **``` is the identity
  object map, which every model already has ```**, **``` an object map
  needs `via` ```**, **``` is an OBJECT MAP, and an object map is a
  `Base` model's clause ```** — the four ways a head's object-map
  clause can say nothing (§8).
- **`main requires a nonempty input stack: …`** — the main program is
  run on nothing, so it may not ask for a wire.

### Sharp edges

- `1 >> 2` — the incoming wire is uncovered (constants don't thread;
  write `2 id` or `2 ...`).
- Binder bodies are input-closed — a `(x -> …)` stage consumes exactly
  its parameters; thread extra wires with `_` beside the binder atom.
- Quotes are points (`• ⇒ Fn`): pushing one beside live wires needs
  `_` or `...` — the same frame discipline as every constant.
- Row arms must fit on one line; arms must agree in type to `merge`.
  `|` never absorbs a line break, so an arm written on its own line is
  a **stage**, and the arms then compose at `>>` instead of standing
  side by side. Carry the row on with `\` if it will not fit. A
  unification failure on a `|`-led line says this. ✦
- Ladder lanes are juxtapositions — a `;`/`>>` inside a lane needs a group.
- `def name = x -> …` ends at the line — unless it leaves a bracket
  open, or says it is unfinished with a trailing `\`, `;` or `>>`, in
  which case the lines that finish it belong to the body. For
  multi-line bodies generally, use the block form (`def name =` newline
  `x ->`). A line that begins with `(` after an ordinary line is a new
  **stage**, not a continuation of it, and a stack failure there says
  so. ✦
- `f >> x y -> …` is not a cutting binder — that form is recognized at
  the start of a scope or after a newline. The naming form `-> x` has no
  such restriction; it ends whatever stage it follows.
- A binder with nothing after it is an error: its body is the rest of
  the scope, so there has to be a rest.
- A binder pattern un-constructs ONE alternative, so it wants a
  single-alternative `data` type: `Shape(a)` where `data Shape = (Int |
  Int Int | Int Int Int)` is *`Shape` has 3 alternatives and a pattern
  un-constructs ONE — use a row, `(… | … | …)`* *(2026-09-14)*.
- A pattern's arity is the constructor's: `Dual(a, b, c)` against `data
  Dual = Float Float` is *names 3 fields, but `Dual` has 2*. A name the
  module never declared is *`Nope` is not a `data` type in scope, and a
  pattern un-constructs one* — patterns are read against the types in
  scope, so a `parse` of a string at runtime (which has none) refuses
  every pattern by that message *(2026-09-14)*.
- **Named fields refuse five things**, each naming the fix
  *(2026-09-14)*. Fields name the positions of ONE constructor, so
  `data Bad = (a: Int | b: Str)` is *field names name the positions of
  ONE constructor, and this declaration has more than one alternative*.
  A field name becomes an ordinary definition, so a name already in
  scope — a def, a prim, another type's field, this type's own
  `unT`/`foldT` — is *field name `px` is already a word in scope …
  rename `T2`'s field, or rename the existing `px`*, and a name that is
  not a word (`2x`) is *not a word, so it cannot name a field*. A
  duplicate within one declaration is *one name per position*. Every
  position is named or none is (*`Str` has no name. Write `name:
  type`*), and a named position is **one wire**: `data W = (x: Int Str,
  y: Int)` is *2 field names for 3 field positions*. Finally, the form
  is `data`'s alone — a `type` alias is transparent and a resource is
  threaded, so neither has a wire to project from.
- A binder's body only sees what the parameter list gives it. Need the
  remainder inside the body? Use an open binder (`x ... -> …`), not
  `(x -> …) ...` — the latter routes the rest *around* the binder.
- Sums never flatten; use `assocL`/`assocR`/`caseN` to manage
  nesting, and one `merge` per level to collapse.
- Open-arity words, open binders and `...`: final atom of their
  stage (§4, §13). Recursion is no longer on that list — the
  recursive call is `self ... >> ev`, an ordinary quoted call,
  and it is `...` and `ev` that carry the rule.
- Short names are yours: `f`, `g`, `x`, `succ`, `double` are all free
  (there are no placeholder prims — every primitive earns its name).
- Shadowing is lexical and safe: name resolution is EARLY-bound. A def
  (and a quote) resolves its free names against the environment as it
  stood where it was written, so shadowing `equals` later cannot change
  the behaviour of the prelude's `odd?` — nor of a quote you already
  built. The checker and the runtime agree on which definition a name
  means. (The one dynamic exception is `evalAs`, which resolves
  spliced code against the live environment — priced by its railway.)
- Exponents: two independent open regions in one segment are rejected;
  same-variable regions (`Intⁿ Intⁿ`) are fine.
- Effects **do** sub-effect, in exactly one direction, and the precise
  statement is worth memorizing *(2026-09-12; this bullet used to say
  "effects don't sub-effect", which composition made false and written
  types make half-true)*:
  - **composition joins** — a pure part in an io composite stays pure,
    and nothing pushes the composite's labels back into it (§3);
  - **a written pure VALUE flows into any expectation** — `∅` is the
    bottom of the lattice, so a pure quotation fills an `=IO>` slot,
    an `=IO>` witness, an `=Recursive>` codata field;
  - **a written pure EXPECTATION refuses labelled code** — that is the
    sandbox, and it is the next three bullets;
  - **where a written type meets another written type the rows are
    EXACT** — inside a `Fn⟨…⟩` two written manifests are unified, not
    ordered, because a `Fn` type is invariant in its arrow. `Fn⟨Int
    =IO> Int⟩` and `Fn⟨Int ⇒ Int⟩` are different types, and neither
    stands for the other.
- **An exit is refused inside a transported scope.** `def x with Circuits = f
  ; observe` is *`observe` leaves Circuits; call it outside `with
  Circuits`* — not a type error, a scope error, and deliberate: it is
  what makes the category's word table exact without consulting
  inference (§8). Call it under `in Circuits`, which opens the same
  vocabulary and transports nothing. The rule is by *slot*, so the
  model's own underlying def (`probe`, say) is an ordinary word and
  stays callable anywhere — the model seals its vocabulary, not the
  module's.
- **Two carriers side by side outside the scope are not an error.**
  `f g` for two words of `Circuits` is `• =Circuits> Circuit(a, b)
  Circuit(b, c)`: two values, well-typed, and honestly not composition.
  The display fold wants exactly one carrier, so it does not fire and
  you see the two. If you meant composition, say so under the marker —
  `def x with Circuits = f ; g`. (`f ; g` is a different thing again and
  usually a stack error: the second word takes `•` and there is already
  a carrier there.)  Related: a module def that merely *happens* to
  produce a carrier is not a word of the category — only a def written
  under `with M`, a def whose own header is `in M` and whose arrow is
  `• ⇒ K(a, b)` (§8), or one of the theory's declared entry slots, is
  left alone inside the scope. Everything else is a stage, and the
  embedding will refuse it. Membership is *written*, never read off an
  inferred type.
- **Applying a family, four ways to get it wrong** *(2026-09-15)*. A
  model whose head declares a parameter is a **family**, not a model,
  and each mistake is refused with the spelling that is right: `with
  Fwd` is *`Fwd` is a model PARAMETERIZED by a model, so it is a family
  and not a model — apply it, `with Fwd(<model of Smooth>)`*; `with
  Floats(Fwd)` is *`Floats` is not a parameterized model at this point —
  a model is applied to another model only when its own head declares a
  parameter*; `with Fwd(Nope)` is *`Nope` is not a model declared at this
  point*; and `with Fwd(IntSum)` is *the parameter 'R' of model `Fwd`
  takes a model of `Smooth`, and `IntSum` models `Monoid`*. A head with
  two parameters is refused where it is written — *two would give one
  slot name two meanings inside a body* — since a family's bodies are
  written in the parameter's vocabulary. And a **false** family is
  refused at its first instantiation, by the theory's own laws run at
  that member's evidence, naming the member: `law 'mulAssoc' fails for
  model Fwd(Floats)` names the family and the argument at once (§8).
- **`in` is not `with`** *(2026-09-13)*. `in X` declares that a def
  is a morphism of X; `with X` applies X to a block. So `in` takes a
  theory (the def is a template) or a model with a carrier (the def is
  written in that category's vocabulary) and nothing else — a model
  with no carrier, a functor, a resource and an unknown name are each
  refused by kind, with the word to write instead. It may only be a
  def's **own header**, it names exactly one thing, and it **mints
  nothing**: a hand-built morphism prints as the carrier it is,
  `sum0 : • =Recursive> Circuit(Int, Int)`, unfolded, because `=Circuits>`
  would say the code went through the functor and it did not.
- **Every `with` that CHANGED something mints — models included**
  *(2026-09-13; the qualification is 2026-09-18)*. `with IntSum ;
  fold1` leaves `=IntSum>` on the arrow, exactly as `with Traced`
  leaves `=Traced>`, because renaming `fold1`'s slots to that model's
  words is a change. A scope that leaves the code exactly as it found
  it mints nothing: the identity functor, a model whose slot names do
  not occur in the body, an object-mapped model over a word whose
  scheme never mentions the mapped type, a `with Recursive` on a body
  that never names the def. The consequence is the sharp edge below,
  now uniform: **a theory slot declared without the label refuses a
  body written under another model.**

  ```text
  model Weird in slot 'op' is Int Int =IntProd> Int but theory Monoid
  declares Int Int ⇒ Int (Cannot unify effects: IntProd vs pure
  (composition joins grades, and this arrow's manifest is written and
  fixed: write =IntProd> on that arrow, or keep this code label-free))
  ```

  Write the label in the theory if you mean it (`op : a a =IntProd> a`
  is rarely what you want), or — much more often — say which model you
  meant at the call rather than inside another model.
  A model's **own** slot bodies are exempt by a rule of their own, and
  need to be: the `with I` that resolves their slot names *does* change
  a body that names a sibling slot (`add` → `Fwd@add`), so image
  membership alone would mint there and the slot's own declared arrow
  would then refuse it. A model does not apply itself.
- The same goes for a functor's receipt, and it surprises people once:
  a *written* type with no labels refuses labelled code. An `evalAs`
  witness `Fn⟨Int ⇒ Int⟩`, or a theory slot declared `a ⇒ a`, will not
  take a word elaborated under `with Traced` — *Cannot unify effects:
  Traced vs pure*. Write the label where you mean it
  (`with Traced ; […]` as the witness), or elaborate the word outside
  the functor. Inferred types never hit this: they just carry the
  label onward.
- **And a written type with no `Recursive` refuses recursive code.** This is
  the same rule a third time, and it is the one you will meet without
  ever writing a functor: `Fn⟨Int ⇒ Int⟩` will not take a quotation
  that uses `while` (or `until`, or `fix`, or **any word whose header
  says `with Recursive`**, or anything built from them). Write
  `Fn⟨Int =Recursive> Int⟩`. Since 2026-09-14 the marker is what mints
  the label, so the rule reads off the header: a def you wrote under
  `with Recursive` will not fit an unlabelled written arrow, and the
  refusal names the label to add.

  ```text
  data Sink = (Fn⟨Int ⇒ Int⟩)
  [[_ 100 >> less?] [2 _ >> *] ... >> while] >> Sink >> drop

  error: Cannot unify effects: Recursive vs pure (composition joins grades,
  and this arrow's manifest is written and fixed: write =Recursive> on that
  arrow, or keep this code label-free)
  ```

  It reaches three places in particular: a codata declaration's thunk
  (`data Stream(a) = (a Fn⟨• =Recursive> Stream(a)⟩)` — §8), a theory slot a
  marked body will fill (`examples/circuits.braid`), and an
  `evalAs` witness over runtime-loaded code that loops. A `=Recursive>`
  arrow still accepts *non*-recursive code — an inferred row is open
  and absorbs the label — so the labelled spelling is the permissive
  one, and the bare spelling is the promise.

  What it does **not** reach *(2026-09-12)*: the argument of a
  higher-order word. `loop`, `while`, `until` and every derived word
  built from them recurse in their OWN arrow, not in the quotation
  they run, so `Fn⟨Int ⇒ (Int | Int)⟩` is what `loop` asks for. While
  composition unified grades instead of joining them, they asked for
  `=Recursive>` bodies and a written pure `Fn` could not reach them at all —
  that was a bug, and it is fixed (`design-effects.md`, "composition
  JOINS"). The same correction removed `=Recursive>` from two of the eight
  declarations §8 and §12 said it had cost.
- **`reflect` is total on binder code** *(2026-09-12)*. It had three
  corners that morning and has none by evening: a `with F` scope over a
  knot, a parameter inside a **residual** row, and a parameter
  inside a flat row of **three or more tracks**. The first two were
  wiring that did not exist yet (`capture`, `dist2`); the third was a
  real coproduct limit — `case2`/`merge` are binary — and the generator
  `#dist:K` (§6) is what lifts it, being a generator rather than a
  derivation precisely because no handler can be written for the tracks
  a residual hides. What `reflect` still refuses is not about binders:
  a `...` before the end of a stage in a binder body, and a name the
  body does not resolve.
- **A binding may only generalize** *(2026-09-13)*. `model Opt :
  Base = p = q` is refused unless `scheme(q) ≥ scheme(p)` — and the
  refusal that
  surprises people is the one that would have *run*: with `two : a ⇒
  Int Int`, `two = dup` fires happily on an `Int` and silently narrows
  `a ⇒ Int Int` to `Int ⇒ Int Int` everywhere else. The type check is
  about every OTHER program, not about the one in front of you. Grades
  obey the same asymmetry in the direction people expect backwards: a
  **pure** image for an **io** generator is fine (the reinterpretation
  removes an effect), an io image for a pure generator is not.
- **A binding's two sides must be WORDS with schemes** *(2026-09-13)*.
  Not
  a theory slot (*a slot is not a word outside `with`*), not a template
  (it has no type until a model supplies one), not a name with `@`
  in it. And v1 bindings are single words — `dup ; * = square` is *a v1
  binding sends one WORD to one word*.
- **`sameCode` and `sameCodeC` are one procedure** *(2026-09-13)*.
  `sameCode` runs abstraction elimination before normalizing, so it
  decides the binders it used to refuse and never disagrees with
  `sameCodeC`. Both enter quotations and rows. What is left outside is
  narrow and specific — `ev` of a WIRE, a knot's own equation, a
  sum whose row is a bare tail — and each refusal names itself (§12.9).
  If a law you want is refused, read the message: it says which of
  those it is.
- **A sampled square compares carriers with `eq?`, and a carrier may
  hold a closure** *(2026-09-14)*. When a theory's parameter is a
  **wire** (rather than a hom-object), the square a `transformation`
  generates is sampled by comparing the two carrier values directly —
  the theory's exit is not applied, on the reasoning that `eq?` reaches
  an ordinary type. It does; but `eq?` on a quotation is **syntactic**,
  so a carrier whose payload is an `Fn` — reverse-mode AD's
  `data Rev = Float Fn⟨Float ⇒ Grad⟩` is the case that found this — is
  weighed by spelling. Two extensionally equal continuations built by
  different code answer `false`, and the square is reported as not
  commuting at the samples when it does commute. `examples/autodiff.braid`
  §7 shows the comparison failing next to the same square passing
  through the exits, and states the one-line fix (apply the exit for a
  wire parameter too) that is deliberately not made yet.
  *(Resolved 2026-09-14: the exit is applied whatever the parameter's
  kind, `transformation Transpose in Fwd ⇒ Rev` is declared, and `:transformations`
  prints what each square was decided by — §8. A theory that declares
  no exit still compares carriers directly, and says so when one
  fails. So does a result at a parameter the theory declares no exit
  FOR: with `Smooth(a, g)`, `observe : a ⇒ Float` is an exit for `a`
  and not for `g`, and a `Grad` is weighed directly — sound here,
  because a `Grad` is two Floats and not a closure.)*
  *(Amended 2026-09-15: the refusal used to say the theory declares
  **no** exit, which is false of a theory that declares one the slot's
  result does not FIT. `examples/prob.braid` is that case —
  `observe : k(Int, Int) ⇒ Int` is an exit, and its own strength
  `under` leaves the hom-object at a **wider pair of stacks**, which
  that exit does not reach — and a second exit there cannot help,
  because the square *that* exit would need is fed by the theory's
  first entry, whose object is one `Int` wire. The message now says
  `no exit whose input FITS this slot's result`. The general shape,
  which is the standing limit: a transformation's component is generic
  in the hom-object's arguments, so it can never **run** the carrier; a
  square between two function-carrier models is therefore decidable
  only when the normalizer proves it, which needs the component to pass
  the witness through untouched — `transformations.braid`'s
  `Forget : Names ⇒ Funcs` drops a `Str` field, and proves the two
  squares that only pass the witness on. A component that *transforms*
  the witness is out of reach, and since 2026-09-16 so is a square that
  *applies* one: a hom-object over stacks makes that `ev` open.)* Two riders came out of the same investigation and are worth
  keeping:
  - **`sameCode` says `false`, not a refusal, for "spelled
    differently"** — two quotations that build the same function out of
    different code, closing over different captures. Everywhere else a
    verdict the normalizer cannot reach is a refusal, and `false` means
    *different morphism*; here it means *different spelling*. It is why
    a square over a closure-holding carrier goes to the samples rather
    than proving.
    *(Resolved 2026-09-14: the wart was a wrapper called
    `fallbackFalse`, which turned the refusal a quotation comparison
    raised into `Right False` so that no verdict standing before the
    extensional comparison arrived would be withdrawn. It is gone. **A
    refusal stays a refusal**, in that corner as everywhere else, so
    `false` now means one thing in the whole tree: different as programs
    of the free category. `sameCode` and `sameCodeC` therefore error
    where they used to answer `false` — over quotations whose captures
    are not pairwise equal, and over the two eta comparisons beside it —
    and the message names the case (§12.9). No example's printed output
    changed: nothing was relying on the fallback. What the
    transformation checker does with the two answers is in §8: both send
    the square to the theory's evidence, because a `false` about the
    FREE category is not a `false` about a model whose words satisfy the
    theory's laws, and the verdict records which answer it was —
    `sampled (2 points; differ in the free category)` against
    `sampled (2 points; ev of an open wire)`.)*
  - **A slot whose input is not the parameter can never be sampled.**
    `lit : Float ⇒ a` takes a `Float`, and `sample : • ⇒ a` supplies
    only the carrier, so no evidence reaches that square: it must
    PROVE or the module is refused. That is a real constraint on how a
    model is written — `examples/autodiff.braid`'s `rlit` builds the
    zero linear map as `(0.0 ; scaleK)` rather than `[(d -> gzero)]`
    precisely so the `lit` square is the same CODE and not merely the
    same map.
- **`| ...` no longer means the residual** *(2026-09-12)*. It is
  refused, for one release, with the message *"`| ...` used to mean the
  residual; write `| ---` for more alternatives, or `| pass` for a
  third track that passes"*. `...` continues wires, `---` continues
  alternatives (§5); an old row is one of the two and the compiler
  cannot guess which, so it asks.
- Several effectful atoms in one tensor stage are **legal**, and run
  left to right — deepest wire first, the order they are written in
  (`print print : a0 a1 =IO> •`). That order is decreed, not checked, so
  a mis-ordered pair is a wrong behaviour, not a type error.
- Inside a `with` scope, a stage may contain **at most one resource
  operation, and it must be alone in that stage** — otherwise *"a stage
  may contain at most one resource operation, and it must be alone —
  put X on its own line"*, naming the operation it found. An operation
  touching *some* of the scope's resources is rejected (*"X threads Log,
  but this scope is over Log Counter"*): the elaborator brings one
  resource wire up, acts, and puts it back, and a subset at once would
  need a permutation it will not guess. The exception is the one that
  matters: a word threading **exactly** the scope's resources, in
  order, is already shaped like the stack, so it applies with no
  routing at all. That is what makes `with` scopes **compose** — a word
  written under `with Log Counter` is callable under `with Log Counter`,
  and without it a multi-resource word could be written with `with` and
  then never called from one. Both limits are the elaborator's,
  not the type system's — by hand, `_`/`...` still do anything, and
  since 2026-09-17 writing them is also how you tell inference to leave
  a stage alone: routing is inferred for a resource word that is
  **alone in its stage**, so a stage with its own `_` and `...` around
  the word is threading by hand and is never auto-routed (§6).
- **In the REPL, `with` is a session-wide scope.** A file's `with` takes
  the rest of the block as its body; a session has no rest yet, so a
  bare `with Log Counter` line opens a scope over every LATER line and
  every subsequent line is elaborated inside it. A bare `with` (or
  `:clear`) leaves; `:s` shows the ambient scope alongside the stack.
  `:t` is elaborated the same way, so under `with IntSum` it answers
  `:t op`. A session cannot *declare* a theory, a model or a
  functor, but `:import` brings them in and then they may be named —
  a theory itself may not, since only a def's header may name one.
  A template defined in a session is reported as one (*template trip
  in Monoid*) and listed by `:defs`. This is selection, not sugar:
  it is what ML's `open` does — and it is the ONE place `with` stands
  on a line of its own, because a session has no `def` to hang it on.
- A `with` clause with nothing after the `=` is an error (*"Empty
  definition body"*): a clause applies to something, so there has to be
  a body.
- A model's argument for a **wire** parameter is a full type
  **expression**, so a theory may be instantiated at a parameterized
  type (`Wrap(List(Int))`, `Wrap(Fn⟨Int ⇒ Int⟩)`) — which is what every
  structure worth having a theory of actually looks like. Its argument
  for a **constructor** parameter is a bare declared name instead
  (`Arrow(Circuit)`), because that name is substituted into the slots
  rather than being a type. Theory and model heads are read against
  every type in scope, the prelude's included.
- A slot body may call **the module's own defs**, and a def may call the
  slot: a theory declaration is a signature, so slots are
  forward-declared at their declared types and neither direction has to
  come first. At runtime a module's own defs are mutually visible for
  the same reason (the prelude keeps sequential capture, so shadowing a
  prelude name cannot reach back into the prelude's own calls).
- A **law body must fit on one line** — the block parser reads one
  entry per line, so a law is a single program, `;`-chained if it needs
  to be.
- A law over a **parametric** theory cannot invent a value of `a`:
  there is no way to write a literal at an unknown type. A theory that
  wants sampled laws declares a witness slot (`sample : • ⇒ a`) and
  each model supplies it — not a workaround, but an audited model
  supplying the evidence its audit runs on.
- Laws are checked by **running**, on whatever samples the program
  names — property testing's poor cousin next to QuickCheck (no
  generation, no shrinking). What is different is that the check is
  part of *being a model*, not a separate test suite.
- `theory` and `model` are file declarations; the REPL takes
  programs, and says so. So is `table` — it reads a CSV, and a CSV
  needs a file to resolve against; `:import` the `.braid` file that
  declares it *(2026-09-15)*.
- **A `table` refuses seven things**, each naming the fix
  *(2026-09-15)*. The file must be there (*table `Gone`: no such file …
  looked in … and in the current directory*, the import rule's own
  message) and must have a header and at least one row (*a column's
  type is read from the data, and there is none*). A header cell that
  is not a word after sanitizing — spaces, tabs and `-` to `_`, first
  letter lowercased — is *column 1's header `"1st"` is not a word after
  sanitizing …*, and one that collides with a word already in scope is
  the named-field refusal above with a table's fix: *rename the column
  with the schema form*. Two columns of one name is the same refusal.
  A **blank cell** is refused naming line and column: *the cell is
  blank … a column has ONE type and a blank is not a value of it*, and
  so is a row that is not the header's width. Under a written schema,
  the arity must match (*the schema writes 2 columns but the header has
  3*) and every cell must read at the type written (*`"1.5"` does not
  read as Int — the schema writes `qty: Int`*). Finally the generated
  helpers are the compiler's spelling: `Trades@cellAt` in source is
  *the compiler's spelling of a table's insides: a `table` generates
  `loadTrades` and `headerTrades`, and those are the only words it puts
  in scope*.
- A resource is **nominal**: structural shapes never fold into one.
  `model GameState in Doctrine = Int Int` leaves `swap : a0 a1 ⇒ a1 a0` exactly
  as it was, and only a genuine rolled `GameState` wire ever displays
  as one. The ceremony (`unLog` before you touch the contents, `Log`
  after) is what buys the arrow fold its meaning.
- A `Fin` prints as a bare integer. Erasure is honest — a `Fin` *is* an
  `Int` at runtime — but output does not distinguish an index from an
  ordinary `Int`; only the type does.

## 15. Extending Braid — what to reach for

Braid has **one arrow**. `⇒` is composition in a single cartesian
category, and there is no class over categories to instantiate: no
higher kinds, no `Arrow`, no `Monad`. So "I want a new kind of
computation" never means "define a new arrow". It means one of five
ordinary things, and which one is decided by *what the new thing is
made of*, not by how exotic it feels.

| You want | You write | Because |
|---|---|---|
| a new kind of **value** | `data` (codata: recurse through `Fn`) | carriers are declared sums; `foldX` is generated |
| **state** threaded through a region | `model … in Doctrine` + `with` | a threaded wire, with the `_`/`...` written for you |
| a new **combinator** or control form | an ordinary `def` | loops are values, guards are words, `...` accumulates |
| a swappable **interface with laws** | `theory` + `model` | models selected by name, audited by running the laws |
| one body over **every** model of a theory | a `def` headed `in <theory>` (a *template*) | expanded and re-inferred per model — its own principal type each time |
| a model built **out of another model** | `model F(T(a)) in T(C(a))` — a *family*, applied by `with F(M)` | a functor Mod(T) → Mod(T); the carrier is a substitution, and `with F(F(M))` iterates |
| the **same program at another type** | `model M in Base(A ↦ B via c)` — an *object map* | a functor on the ambient presentation: literals go through `c`, defs are unfolded, and a word with no image is refused by name |
| a category of **processes** | `data` + your own composition word | then present it as a `theory` if it has laws |

Worked examples, in that order: `lifting.braid` first (every functor
is a function `Fn⟨a ⇒ b⟩ ⇒ something better` — the logged version of a
function, game rules as lifted moves), then `examples/tree.braid` and
`stream.braid` (data and codata), `resources.braid` and `payroll.braid`
(a resource, and a whole program using one), `ladder.braid` (control
flow that is all ordinary defs), `theories.braid` (theories and
models), `circuits.braid` (a stream transducer — a genuinely
different category — as data plus a composition word plus
`theory Arrow(k(..., ...))`, the Arrow interface stated once over a
constructor parameter and audited against two models),
`autodiff.braid` (below), `frame.braid` (a data frame as a second
model of the same doctrine — row programs lifted by `with Frame`, the
`data` declaration's field words as the columns, §12) and
`prob.braid` (a third: probability as a **Markov category**, where the
model is what makes copying stop being natural), and
`modular.braid` (an **object map**: one polynomial, read over `Int` and
over Z/7, with `div` and `lt?` refused by name because Z/7 has no image
for them).

**An object map is not a homomorphism** *(2026-09-17)* — and
`examples/modular.braid` is the file that says so twice. `model Mod in
Base(Int ↦ Mod7 via reduce)` makes reduction a functor on the *ambient
presentation*: it types, it runs, and it says nothing about rings.
That `reduce` is a **ring** homomorphism is a further and stronger
claim, made by `transformation Reduce in Ints ⇒ Mods` and audited
square by square. The contrast is in the same file: floor-halving is a
perfectly good object map — every generator it names has an image at
the substituted type — and its transformation is **refused at the `add`
square**, because ⌊(7+7)/2⌋ = 7 and ⌊7/2⌋ + ⌊7/2⌋ = 6. Two
declarations, two different questions, and you need both.

**Differentiation is a model** *(2026-09-14)* — the worked example
that ties every row of the table together, and the one to read after
`theories.braid`. `examples/autodiff.braid` declares `theory
Smooth(a)`, three `data` carriers, three models (evaluation, forward
mode, reverse mode), three programs written `in Smooth` and read by
all three, two `transformation`s — one with every square proved, one
decided three ways proved and five at the samples — Newton's method
under `with Recursive`, and a fourth model in which the adjoint is
threaded through a resource instead of summed. It contains no
`Code`, no `functor` and no chain rule: the chain rule is what a model
*is*. Since *(2026-09-15)* forward mode is a **family** — `model
Fwd(Smooth(a, _)) in Smooth(Dual(a), a)`, applied by `with
Fwd(Floats)` — the file also prints **second derivatives**, by applying
that family to a member of itself (`with Fwd(Fwd(Floats))`), and the
three templates it reads are untouched. And, since the sampled square
over a closure-holding carrier was fixed *(2026-09-14, §14)*, it
records what a sampled square costs: it establishes its claim at the
theory's exit.

**What a family still cannot be built over** *(2026-09-15)*. The other
motivating example, `model Kleisli(Monad(m)) in Arrow(Kl(m))`, does
**not** type, and the two refusals say precisely what is missing —
both of them the same missing thing, a type constructor that can be
applied to a *variable* and applied *partially*:

- `data Kl(m(_), a, b) = Fn⟨a ⇒ m(b)⟩` — `Malformed type parameter
  list`. A `data` declaration's parameters are wires, stacks, widths and
  rows; a **constructor** parameter is a theory's alone. For the body to
  hold `m(b)` a type would have to have a *variable in head position*,
  and `Ty` has `TData String [SType]` — a name. That is type-level
  application, which the substitution discipline above exists to avoid.
- `model Kleisli(Monad(m)) in Arrow(Kl(m))` — `theory Arrow declares
  'k' as a type constructor of arity 2, so its argument must be a bare
  constructor name, not 'Kl(m)'`. An `InstArg` at a constructor
  parameter is a **name**; there is no partial application to write.

A family whose carrier is `C(a)` for a *wire* parameter — the
dual-number construction — needs neither, which is why it is the one
that shipped.

**Probability is a model** *(2026-09-15)* — and it is the example that
says what the `theory`/`model` row of the table *buys*, because the
thing it buys is a distinction the language cannot otherwise draw.
`examples/prob.braid` declares `theory Prob(k(..., ...), d(...)) in
Doctrine` — the doctrine's two structure slots and its evidence, a
strength of its own (`under : k(a, b) ⇒ k(c a, c b)`, because a
generator is a carrier at a fixed width), plus `flip`, `uniform` and
`condition` as **entries** (`• ⇒ k(…, …)`: a distribution is written as
the kernel it is, the bias arriving on the wire the kernel consumes)
and `report` as an **exit** whose result is a constructor parameter.
Three models (exact enumeration, a threaded seed, the support), the
doctrine's five laws over each, and then the two Markov axioms stated
as programs: copy
is **not** natural, which is the law that must *fail* and is shown
failing by running both sides; discard **is** natural, stated at the
mass, which `condition` is exactly what breaks (an affine category, not
a Markov one — and Bayes' rule is the renormalizing that puts the mass
back). It also records what cannot be checked and why: a transformation
between two function-carrier models of a doctrine is decidable only
when the normalizer proves it, because a component is generic in the
hom-object's arguments and so can never run the carrier (§14).

**An effectful arrow is a resource + a macro + a theory**: the resource
carries the state, the macro installs and discharges it, and the theory
says what the operations must satisfy. Declaring and *entering* have
been ordinary since `with`; **discharging** is the third, and it needs
no construct either — a wrapping macro seeds the wire, applies the
program, and unrolls it, and the arrow loses the label across it:

```braid
model Log in Doctrine = Str
def note      = unLog _ ; cat ; Log
def collectLog = (f -> [f ("" ; Log) ... ; ev ; unLog ...])
-- collectLog : Fn⟨ρ0 =Log> ρ1⟩ ⇒ Fn⟨ρ0 ⇒ Str ρ1⟩
```

That is Plotkin–Pretnar's *handler is a model*, read in a language
whose models already are models: discharge is a wrapping functor,
not a form. It is per-resource **by name**; the generic one is a
template (§8) over a theory naming the two operations a handler needs
(`seed : • ⇒ e`, `unwrap : e ⇒ a`), which then reads
`Fn⟨ρ0 =Log> ρ1⟩ =Logs> Fn⟨ρ0 ⇒ Str ρ1⟩` under `with Logs` and
`Fn⟨ρ0 =Counter> ρ1⟩ =Counts> Fn⟨ρ0 ⇒ Int ρ1⟩` under `with Counts` —
`examples/resources.braid` writes both halves. (The outer label is the
scope's receipt: a `with` that changed the code mints, models
included.)

**What not to reach for.** Effects do not need new machinery: state is a
a resource, failure is the railway sum track, writer is a resource,
nondeterminism is `List`, reader is a resource you only read. Only IO
is irreducible, and it is a *grade* on the existing arrow (`=IO>`), not an
arrow of its own. `examples/arrows.braid` shows that `Control.Arrow`'s
whole interface — `arr`, `>>>`, `first`, `***`, `&&&`, `|||`, `app` —
is already the syntax rather than a library: `first f` is `f _`, which
is why the Doctrine needs no slot for it.

**The trade, stated once.** Because models are selected by name and
nothing is inferred or dispatched, you cannot write code generic over
"any monoid" and have the right one found for you; you write `with
IntSum`. What you *can* write once is the body — a template over the
theory (§8) — and the scope that instantiates it is the one line you
still have to say. What you get back is annotation-freeness, coherence in a
structural type system, and no higher kinds to explain. That is the same
trade `theory` makes everywhere, and it is deliberate.

## 16. Further reading

- `CONSTRUCTS.md` — the declaration layer as a **reference**: every
  construct (theory, the four kinds of model, template, hand-built
  morphism, transformation, the Doctrine, `with`, `in`, `table`,
  receipts), what it is, its syntax, what the checker does with it,
  which example file uses it, and its refusals — plus what is *not* a
  construct and why.
- `design-control-flow.md` — the control-flow design record (idiom
  inventory, deferral theorem, the guard-syntax history).
- `design-exponents.md` — exponents: theory, unification, erasure,
  the mapN open question (Fn-in-declarations has since shipped, §8).
- `design-indices.md` — `Fin(n)` and witnessed introductions: why
  `Aⁿ` is `Fin(n) → A`, and why there is no `tabulate`.
- `design-effects.md` — the effects position (effects are wires, IO is
  a linear wire, the placement ladder as a PCM); **stages 1, 2, 3 and 4
  — the io grade, resource declarations, `with`, and
  theories/models with runnable laws — have shipped**, including the
  amendment that flipped the resource wires from the top of the stack
  to the bottom. Stage 5's **mark** shipped 2026-09-17 (`with R` mints,
  and routing is inferred), and so did the `World` **statement** —
  `IO`'s carrier is declared abstract and linear; only the explicit and
  split zoom levels, a `World` wire you can name, are position only.
  The 2026-09-17 amendment records it.
- `design-7b.md` — stage 7b in full: a resource is a model of the
  Doctrine, labels carry their carriers, and routing is transport at a
  representable fibre.
- `design-8.md` — the surface proposal of 2026-09-17, kept as written.
  Its **`resource` half shipped** on 2026-09-18 (`model R in Doctrine =
  Ty`), and its **`functor` half was REJECTED**: a model is a functor
  out of a *presented* category and a `Code ⇒ Code` word is not one, so
  `functor` was retyped to take a graph morphism instead of being
  folded away. Read it with the 2026-09-18 amendment of
  `design-macros.md` beside it, which records the argument.
- `design-macros.md` — elaboration as a library: functors over `Code`,
  the five invariants, the fibration picture and the functors known to
  type, the manifest stated once, and the 2026-09-09 amendment
  "recursion at a typed boundary" (why `fix` replaced self-reference,
  what `Recursive` does and does not promise, and what it cost), and the
  2026-09-14 amendment "recursion is a marker" (why `with Recursive` gave
  the name back, and why the spine stayed closed anyway), and the
  2026-09-18 amendment "`functor` takes a graph morphism; `resource` is
  a model" (the foundations argument, the evidence that the whole-spine
  escape hatch had no user, and why `lift2` and the declaration
  substrate cover what it dropped).
- `design-metaprogramming.md` — typed code as the free category
  (`Path`), Forth's compiler lifted from a monoid; position taken.
- `guide-open-arity.md` — practical rules for open words.
- `spec-sums.md`, `expanded-spec.md`, `spec-code.md` — the deeper
  design records.
- `examples/` — every feature running, and CI-guarded; start with
  `registrar.braid` (most of the language in forty lines), then
  `ladder.braid`, `cuts.braid`, `stream.braid`, `arrows.braid`,
  `functors.braid`, `resources.braid`, `theories.braid` (theories,
  models, and laws that run), `modular.braid` (a model that maps the
  TYPES: one polynomial over `Int` and over Z/7), `gla.braid`.
