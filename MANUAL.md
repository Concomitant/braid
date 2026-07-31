# The Braid Manual

A reference for every language feature. Types shown are the checker's
actual output (`:t`), not paraphrases. Companion docs:
`guide-open-arity.md` (width-polymorphic words), `design-*.md` (why
each feature is the way it is), `examples/` (everything running).

---

## 1. Running Braid

```sh
# run a file (no local GHC needed)
docker run --rm -v "$PWD":/w -w /w haskell:9.4-slim \
  sh -c "cabal run -v0 braid -- examples/registrar.braid"

# REPL: add -it, drop the file
docker run --rm -it -v "$PWD":/w -w /w haskell:9.4-slim \
  sh -c "cabal run -v0 braid"
```

REPL commands: `:t <prog>` type · `:t! <prog>` raw (no alias folding) ·
`:doc <name>` doc comment · `:defs` whole prelude with types · `:s`
show stack · `:clear` reset stack · `:q` quit. Every REPL line runs
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
| `[` `]` | quotation |
| `(` `)` | grouping / rows / list & case arguments / binders |
| `\|` , `\|\|` | row separator; vertical list literal |
| `,` | separator in `list(…)`, `case(…)`, type arguments |
| `->` | binder arrow |
| `>=>` `>?>` `>!>` | railway operators (§7) |
| `^` | exponent in type position (`Int^3`); superscripts `Int³`, `ℝⁿ` also lex |

Identifiers are any run of characters not in the punctuation set —
`odd?`, `f'`, `+`, `*` are all ordinary names. Blank lines collapse.
**A newline is a strict `>>`** — there is no line-continuation for `>>`
or `|`; only `>=>`/`>?>`/`>!>`/`||` may absorb a line break.

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

**Placement rules** (one family, one logic — the open thing must come
last so the runtime segment can be its witness):
- an open-arity word must be the final atom of its stage (§13);
- a recursive call must be the final atom of its stage;
- `...` must be the final atom of its stage.

## 5. Types

Inferred, principal, never annotated. Four variable sorts:

| sort | display | ranges over |
|---|---|---|
| type | `a0, a1…` | one wire's element type |
| stack | `ρ0…` | a stack segment (tails, splices) |
| row | `σ0…` | the tail of a sum's alternative list |
| exponent | `n0…` (shown superscript: `Intⁿ⁰`) | a width (unary natural) |

Type formers:

- **Base**: `Int`, `Str`, `Sym`.
- **`•`** — the empty stack; the terminal object. Constants are points
  `• ⇒ A`; `forget : ρ ⇒ •` is the unique map to it.
- **Products** are juxtaposition: `Int Str` is two wires. No pair type
  — the stack is the pair.
- **Sums**: `(Δ₁ | … | Δₙ [| σ])` — one wire carrying alternative
  *stacks*. Rigid nesting: `(A | (B | C))` never flattens.
  `Bool = (• | •)`, `Maybe(a) = (• | a)` are prelude aliases.
- **`Fn⟨Σ ⇒ Θ⟩`** — a reified program (quotation type). The internal
  hom: `apply` is modus ponens.
- **Named types**: `type` aliases and `data` declarations (§8).
  Display folds structural types back to their alias names when they
  match exactly (`:t!` shows raw).
- **Exponents**: `A^n` (input `Int^3`, `R^n`; display `Int³`, `ℝⁿ`) — a
  segment repeated n times. `n` is erased at runtime; concrete
  exponents expand away. See §13 and `design-exponents.md`.

## 6. Program forms

### Quotation `[p]`
`[p] : • ⇒ Fn⟨…⟩` — pushes the program as a value; a **pure point**
even when `p` does real work. Run with `apply : Fn⟨ρ0 ⇒ ρ1⟩ ρ0 ⇒ ρ1`
(the `Fn` sits *below* its arguments). Quotes capture in-scope binder
names (closures).

### Grouping `(p)`
The enclosed program becomes one atom. Grouped compounds in non-final
tensor position are typed closed (their outer tails become `•`).

### Binders
```braid
(x y -> body)      # inline: an atom consuming two wires
def w =
    x y ->         # postfix: names the top wires; the REST of the
    body           # scope is the body
```
Parameters bind top-of-stack wires (leftmost name = deepest of those
taken) and are in scope as constants — including inside quotes
(closure capture). **The body is input-closed**: all input arrives
through the parameters; a binder cannot take some wires and leave
others flowing underneath. Bound names shadow prims/defs. Duplicate
parameters are rejected.

### Rows `(p₁ | p₂ | …)`
The sum functor's action: one wire in carrying `(Δ₁|Δ₂|…)`, component
i runs on alternative i, results re-tagged in place. Arms are **bare**
programs (the delay law: a row is the one context where bare code is
conditional). Sugar:

| form | means |
|---|---|
| `(f \|)` | `(f \| pass)` — trailing bar passes the last track |
| `(\| f)` | `(pass \| f)` — leading bar passes the first track |
| `(f \| ...)` | open row: identity on all remaining alternatives (row residual σ) |

Rows are **line-scoped**: bare rows work without parens (`ok | guard`
on its own line), and a row cannot span a line break. Each arm lives
on one line.

`merge : (ρ0 | ρ0) ⇒ ρ0` rejoins agreeing tracks (the codiagonal).
Arms must agree on the result type to merge.

### Injections
`in1 : ρ0 ⇒ (ρ0 | σ0)`, `in2`, … `inN` — tag the whole input segment
at position N (open row tail). Aliases: `ok`/`here`/`again` ≡ `in1`,
`miss`/`done` ≡ `in2`. `there : (σ0) ⇒ (ρ0 | σ0)` shifts tags by one
(`here >> there ≡ in2`).

### List literals
`list(e1, e2, …)` — comma-separated elements, each a **juxtaposition
of atoms** (no top-level `>>`/`;` — wrap in a group: `list((1 2 ; +))`).
Elements may be multi-wire: `list(1 "a", 2 "b") : List(Int Str)`
(stack-kinded type parameters). Desugars to `nil`/`cons`.

`|| e1 || e2 || …` — the vertical list literal: same value as
`list(…)`, each lane an arbitrary bracketed program, may span lines.

### `case(b1, …, bn)`
The coproduct eliminator for a right-nested sum:
`case(a, b, c) ≡ (a | (b | c) >> merge) >> merge`, eliminating
`(A | (B | C)) ⇒ R`. Branches are full programs, spliced bare;
heterogeneous domains, one shared result.

## 7. Railway operators

Parse-time sugar, all one shape — next stage on one track, a default
injector on the other:

```
t1 >=> t2   ≡  t1 >> (t2   | in2) >> merge     -- Kleisli: thread the hit track
t1 >?> t2   ≡  t1 >> (in1  | t2)  >> merge     -- elif: thread the miss track
t1 >!> t2   ≡  t1 >> (pass | t2)  >> merge     -- close with a total default
```

They bind looser than `>>` (each side is a whole `>>`-chain) and may
span line breaks (the only operators besides `||` that do). They are
deliberately thin: the row form on the right is always available.

## 8. Definitions, types, modules

```braid
def name = program            # inline body — ends at the line
def name =                    # block body — `=` ends the line,
    program                   # body on the following (indented) lines
    continues
```

- `## doc` lines immediately before a `def`/`type`/`data` attach to it.
- Defs may **shadow** prims and prelude words; duplicate defs of the
  same name are an error.
- **Recursion**: a def may call itself by name, or as `recurse`
  (def-local alias). Self-reference is monomorphic; the recursive call
  must be the final atom of its tensor stage.
- Let-polymorphism: defs generalize over all four variable sorts.
- The prelude is auto-loaded user code; `:defs` lists it.

```braid
type YN = Bool                        # alias (display folds to it)
type Result(a, e) = (a | e)           # parameterized; params are stacks
data List(a) = (• | a List(a))        # recursive nominal type
data Tree(a) = (a | Tree(a) Tree(a))
```

A `data Name(...)` declaration generates:
- `Name` — the constructor (roll): body stack ⇒ `Name(…)`;
- `unName` — the unroll: `Name(…)` ⇒ body sum;
- `foldName` — the structural eliminator, one quoted case per
  alternative, recursive slots pre-folded (e.g. `foldList :
  Fn⟨• ⇒ b⟩ Fn⟨b ρ ⇒ b⟩ List(ρ) ⇒ b`).

Roll/unroll are free at runtime. Type parameters must occur in the
body; a product of two bare parameters (`a b`) is rejected as an
ambiguous split. Literal exponents are allowed in declarations
(`type T3 = (Int^3 | Str)`); exponent *variables* are not yet.
**Known limit**: `Fn⟨…⟩` cannot appear in type declarations — so
function-carrier types (State, streams/codata) are usable structurally
but not nameable (see `design-exponents.md` notes / open questions).

## 9. Primitive reference

Wiring (cartesian structure):

| word | type | note |
|---|---|---|
| `id`, `_` | `a0 ⇒ a0` | `_` is the section hole |
| `swap` | `a0 a1 ⇒ a1 a0` | |
| `dup` | `a0 ⇒ a0 a0` | Δ |
| `drop` | `a0 ⇒ •` | |
| `pass` | `ρ0 ⇒ ρ0` | identity on the whole segment |
| `forget` | `ρ0 ⇒ •` | terminal morphism |
| `rotLast` | `ρ0 a ⇒ a ρ0` | move the top wire to the bottom |

Arithmetic & strings (all exact; `-`, `div`, `mod` are bottom-op-top):

| word | type |
|---|---|
| `+` `-` `*` `div` `mod` | `Int Int ⇒ Int` |
| `f` / `g` | `Int ⇒ Int` — sample successor / double (test words) |
| `cat` | `Str Str ⇒ Str` |
| `toStr` | `a0 ⇒ Str` |
| `asInt?` | `Str ⇒ (Int \| Str)` |
| `symStr` | `Sym ⇒ Str` |
| `print` | `a0 ⇒ •` |
| `true` / `false` | `• ⇒ Bool` |

Routers (predicates that keep and route; hit = track 1):

| word | type |
|---|---|
| `odd?` `even?` `zero?` `negative?` | `Int ⇒ (Int \| Int)` |
| `eq?` | `a0 a0 ⇒ (a0 a0 \| a0 a0)` |
| `lt?` | `Int Int ⇒ (Int Int \| Int Int)` |

Sums & control:

| word | type |
|---|---|
| `in1`…`inN`, `ok`/`here`/`again`, `miss`/`done` | `ρ0 ⇒ (… \| ρ0 \| σ0)` |
| `there` | `(σ0) ⇒ (ρ0 \| σ0)` |
| `merge` | `(ρ0 \| ρ0) ⇒ ρ0` |
| `apply` | `Fn⟨ρ0 ⇒ ρ1⟩ ρ0 ⇒ ρ1` |
| `loop` | `Fn⟨Σ ⇒ (Σ\|Θ)⟩ Σ ⇒ Θ` — Elgot iteration (`again`/`done`) |

Metaprogramming & IO (railway-typed edges):

| word | type |
|---|---|
| `reflect` | `Fn⟨ρ0 ⇒ ρ1⟩ ⇒ (Code \| Str)` |
| `evalCode` | `Code ρ0 ⇒ (ρ1 \| Str ρ0)` — dynamically checked |
| `unparse` | `Code ⇒ Str` |
| `parse` | `Str ⇒ (Code \| Str)` |
| `readFile` | `Str ⇒ (Str \| Str)` |
| `writeFile` | `Str Str ⇒ Maybe(Str)` |

Exponent tier (widths erased; see §13):

| word | type |
|---|---|
| `foldExp` | `Fn⟨a0 a1 ⇒ a0⟩ a0 a1ⁿ ⇒ a0` |
| `foldExp2` | `Fn⟨a0 a1 a2 ⇒ a0⟩ a0 (a1 a2)ⁿ ⇒ a0` |
| `dupN` | `a0ⁿ ⇒ a0ⁿ a0ⁿ` |
| `addN` | `Intⁿ Intⁿ ⇒ Intⁿ` |
| `zipN` | `a0ⁿ a1ⁿ ⇒ (a0 a1)ⁿ` |
| `scaleN` | `Int Intⁿ ⇒ Intⁿ` |

## 10. Prelude reference (all derived user code — `:defs` for types)

**Lists**: `nil` `cons` `uncons` `fold` (left fold) `foldList`
(structural) `map` `filter` `reverse` `append` `concat` `single`
`flatMap` `len` `sum` `product` `range` `downFrom` `take` `skip` `zip`
(`List(a) List(b) ⇒ List(a b)`) `all` `any` `partitionSum` `sequence`
(List over the sum monad) `printAll`.

**Router algebra** (quoted predicates as values): `not` (track swap)
`negate` `both` `either` `equals?` `less?` `equalsTo` `lessThan`
`else?` (always-hit) `assocL`/`assocR` (re-nest a sum).

**Verdict tier** (forget the data, keep the decision): `verdict :
(ρ0|ρ1) ⇒ Bool`, and long forms `equals` `less` `odd` `even` `zero`
`negative`. Bool connectives: `and` `or` `xor` `implies`; muxes
`select` `swapIf`; `condFn`/`cond`, `whenFn`/`when`,
`unlessFn`/`unless`.

**Guard ladders** (§11): `if` `elif` `else` `otherwise` `decide`
`firstTrue` `matchWith` `choose` `ifRoute` `elifRoute`.

**Loops**: `while` `until` (+ `whileFn`/`untilFn`) — three-line defs
over `loop`.

**Bundles**: `sumN : Intⁿ ⇒ Int`.

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

# deferred peel: the sum deepens; case() folds the tree
negative? >> (drop ; "neg" | pass) >> (pass | zero?)
    >> case(pass, drop ; "zero", toStr)

# guards as data: || clause lists, probed by choose / matchWith
x [default] list([p?] [action], …) >> matchWith

# loops
7 >> [_ 100 >> less?] [2 _ >> *] ... >> while      # → 112
```

There is **no guard syntax in the parser** — every idiom above is
prelude defs plus core forms. See `examples/ladder.braid` and
`design-control-flow.md` for the full inventory and the reasoning.

## 12. Metaprogramming

`reflect` turns a quotation into its **spine**: `Code = List(Stage)`,
`Stage = List(Atom)`, `data Atom = (prim | int | str | sym | quote |
row | group)`. Lambdas reflect as pure wiring (abstraction
elimination); true closures are gated onto the miss track with an
explanation. Code is an ordinary list — slice with `take`, transform
with `map`, reverse for the GLA transpose (`examples/transpose.braid`,
`code.braid`). `evalCode` re-checks dynamically and runs; failures
ride the miss track *with the untouched segment as evidence*.
`unparse`/`parse` + `readFile`/`writeFile` round-trip code through
disk (`examples/io.braid`).

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

## 14. Sharp edges (things the checker will teach you)

- `1 >> 2` — the incoming wire is uncovered (constants don't thread;
  write `2 id` or `2 ...`).
- Binder bodies are input-closed — a `(x -> …)` stage consumes exactly
  its parameters; thread extra wires with `_` beside the binder atom.
- Quotes are points (`• ⇒ Fn`): pushing one beside live wires needs
  `_` or `...` — the same frame discipline as every constant.
- Row arms must fit on one line; arms must agree in type to `merge`.
- `list(…)` elements are juxtapositions — group any `;`/`>>`.
- `def name = x -> …` ends at the line; use the block form (`def name =`
  newline `x ->`) for multi-line bodies.
- Sums never flatten; use `assocL`/`assocR`/`case(…)` to manage
  nesting, and one `merge` per level to collapse.
- Recursive calls and open-arity words: final atom of their stage.
- `f` and `g` are (sample) prims — shadowing them in examples is a
  classic accidental collision.
- Exponents: two independent open regions in one segment are rejected;
  same-variable regions (`Intⁿ Intⁿ`) are fine.

## 15. Further reading

- `design-control-flow.md` — the control-flow design record (idiom
  inventory, deferral theorem, the guard-syntax history).
- `design-exponents.md` — exponents: theory, unification, erasure,
  the mapN / Fn-in-declarations open questions.
- `guide-open-arity.md` — practical rules for open words.
- `spec-sums.md`, `expanded-spec.md`, `spec-code.md` — the deeper
  design records.
- `examples/` — every feature running; start with `registrar.braid`
  (most of the language in forty lines), then `ladder.braid`,
  `arrows.braid`, `functors.braid`, `gla.braid`.
