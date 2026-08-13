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
| `(` `)` | grouping / rows / type arguments / binders |
| `\|` | row separator (rows / sum types) |
| `,` | separator in type arguments |
| `->` | binder arrow |
| `>=>` `>?>` `>!>` | railway operators (§7) |
| `^` | exponent in type position (`Int^3`); superscripts `Int³`, `ℝⁿ` also lex |
| `⟨` `⟩` `⇒` | `Fn` type brackets and arrow (type position): `Fn⟨Σ ⇒ Θ⟩` |

Identifiers are any run of characters not in the punctuation set —
`odd?`, `f'`, `+`, `*` are all ordinary names. Blank lines collapse.
**A newline is a strict `>>`** — there is no line-continuation for `>>`
or `|`; only `>=>`/`>?>`/`>!>` may absorb a line break.

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
- an open binder (`x ... -> …`) must be the final atom of its stage;
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
[x y -> body]      # quoted: an Fn value (a closure)
def w =
    x y ->         # postfix: names the top wires; the REST of the
    body           # scope is the body
```
Parameters bind wires **leftmost = deepest**, exactly as atoms align in
a tensor stage, and are in scope as constants — including inside quotes
(closure capture). Bound names shadow prims/defs; duplicate parameters
are rejected.

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
unused). A `...` binder cannot be `reflect`ed (its passthrough width is
erased); `_` binders reflect fine, compiling to ordinary wiring.

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
| `(f \| ...)` | open row: identity on all remaining alternatives (row residual σ) |

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
`negative? >> (in1 | zero? >> (in2 | in3) >> merge) >> merge`.

`merge : (ρ0 | ρ0) ⇒ ρ0` rejoins agreeing tracks (the codiagonal).
Arms must agree on the result type to merge.

### Injections
`in1 : ρ0 ⇒ (ρ0 | σ0)`, `in2`, … `inN` — tag the whole input segment
at position N (open row tail). Aliases: `ok`/`here`/`again` ≡ `in1`,
`miss`/`done` ≡ `in2`. `there : (σ0) ⇒ (ρ0 | σ0)` shifts tags by one
(`here >> there ≡ in2`).

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

`case3 ≡ (f g h s -> s >> (f ... >> apply | (g ... >> apply |
h ... >> apply) >> merge) >> merge)` — heterogeneous handler domains,
one shared result; to sums what `foldList` is to lists. Handlers are
quoted (the `[]` tax), unlike bare row arms — write the nested rows by
hand when bareness matters.

## 7. Railway operators

Parse-time sugar, all one shape — next stage on one track, a default
injector on the other:

```
t1 >=> t2   ≡  t1 >> (t2   | in2) >> merge     -- Kleisli: thread the hit track
t1 >?> t2   ≡  t1 >> (in1  | t2)  >> merge     -- elif: thread the miss track
t1 >!> t2   ≡  t1 >> (pass | t2)  >> merge     -- close with a total default
```

They bind looser than `>>` (each side is a whole `>>`-chain) and may
span line breaks (the only operators that do). They are
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
type Endo(a) = Fn⟨a ⇒ a⟩              # a reified program as a type…
type Pred(a) = Fn(a -> (a | a))       # …Unicode Fn⟨Σ ⇒ Θ⟩ or ASCII Fn(Σ -> Θ)
data List(a) = (• | a List(a))        # recursive nominal type
data Tree(a) = (a | Tree(a) Tree(a))
data Stream(a) = (a Fn⟨• ⇒ Stream(a)⟩)   # codata: recursion THROUGH a Fn
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

**`Fn` in declarations** — write a reified program as `Fn⟨Σ ⇒ Θ⟩`
(Unicode, mirrors `:t`) or `Fn(Σ -> Θ)` (ASCII); the inner stacks parse
like any type stack (params splice, `•` is empty, `Fn` nests). This
names function-carrier types — `Endo`, `Pred`, State-style monad
carriers — and, when the recursion runs *through* the `Fn`, gives
**codata**:

```braid
data Stream(a) = (a Fn⟨• ⇒ Stream(a)⟩)   # head + a THUNKED tail
```

A codata type gets constructor/unroll as usual but **no `foldName`** —
a structural fold through the thunk would diverge, so it is withheld by
construction; you observe instead (`unStream`, then `apply` to force
one cell). Productive corecursion guards its self-call under a quote
(`def from = (n -> n [n 1 >> + >> from] >> Stream)`). See
`examples/stream.braid`. Caveat: a `Fn` type whose stacks carry two
open stack-params (`Fn⟨s ⇒ s a⟩`) parses and expands, but won't
display-fold back (the leading-splice match is ambiguous — pin one
arity if you need the fold).

## 9. Primitive reference

**The kernel admits three presentations** (each derives the others,
verified): the single-wire generators `{id, dup, swap, drop}`; binders
(`dup = (x -> x x)` …), which abstraction elimination compiles back
into the generators; and the segment tier (`dup = (x -> x >> dupN)`,
`drop = (x -> x >> forget)`, `swap = (x y -> x y >> rotLast)` — the
generators are the width-1 shadows of the open-width words). The
single-wire basis stays primitive because it is the normal-form
alphabet reflected `Code` is written in. `pass` is not merely
equivalent to `...` — the remainder marker *denotes* `pass`; they are
one term with two spellings. Derived-but-primitive-looking words
(`odd?`-family, `pack`/`pack2`, `sumN`, `true`-almost) live in the
prelude — the design bet ("primitives span everything else in the
language itself") is proven in both directions.

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
| `cat` | `Str Str ⇒ Str` |
| `toStr` | `a0 ⇒ Str` |
| `asInt?` | `Str ⇒ (Int \| Str)` |
| `symStr` | `Sym ⇒ Str` |
| `print` | `a0 ⇒ •` |
| `true` / `false` | `• ⇒ Bool` |

Routers (the primitive comparators; hit = track 1 — the predicate
routers `odd?` `even?` `zero?` `negative?` are DERIVED prelude words
now, via `mod`/`equals`/`less` and the `(n | n)` re-routing pattern):

| word | type |
|---|---|
| `eq?` | `a0 a0 ⇒ (a0 a0 \| a0 a0)` — structural equality, any value |
| `lt?` `lte?` `gt?` `gte?` | `Int Int ⇒ (Int Int \| Int Int)` |

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

**Bundles**: `sumN : Intⁿ ⇒ Int`; `pack : aⁿ ⇒ List(a)` and `pack2`
(derived from their own eliminators — `foldExp` + `cons`/`reverse`,
Church-style for `pack2`).

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
ride the miss track *with the untouched segment as evidence*. Its
hit-track type `ρ1` is chosen by the *context*, not the code — the one
place checker and value can disagree. A top-level **width backstop**
catches the mismatch: a program whose result stack width differs from
its (determinate) output type fails with a clean `result desync` error
instead of silently desyncing. Backstop, not a type-level fix — the
typed design is `design-metaprogramming.md`.
`unparse`/`parse` + `readFile`/`writeFile` round-trip code through
disk (`examples/io.braid`). `box : Code ⇒ Fn⟨ρ ⇒ (r | Str ρ)⟩` defers
instead of running — the other half of `reflect`'s round trip.

**Cut soundness** (`examples/cuts.braid`): Braid is not
token-concatenative, but at spine granularity the concatenative
property is a runnable theorem — every stage-boundary cut yields two
runnable pieces with `run(prefix) ; run(suffix) = run(whole)`, atom
slices within a stage are runnable sub-tensors, and any slice boxes.

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
- Ladder lanes are juxtapositions — a `;`/`>>` inside a lane needs a group.
- `def name = x -> …` ends at the line; use the block form (`def name =`
  newline `x ->`) for multi-line bodies.
- A binder's body only sees what the parameter list gives it. Need the
  remainder inside the body? Use an open binder (`x ... -> …`), not
  `(x -> …) ...` — the latter routes the rest *around* the binder.
- Sums never flatten; use `assocL`/`assocR`/`caseN` to manage
  nesting, and one `merge` per level to collapse.
- Recursive calls and open-arity words: final atom of their stage.
- Short names are yours: `f`, `g`, `x`, `succ`, `double` are all free
  (there are no placeholder prims — every primitive earns its name).
- Shadowing is lexical and safe: name resolution is EARLY-bound. A def
  (and a quote) resolves its free names against the environment as it
  stood where it was written, so shadowing `equals` later cannot change
  the behaviour of the prelude's `odd?` — nor of a quote you already
  built. The checker and the runtime agree on which definition a name
  means. (The one dynamic exception is `evalCode`, which resolves
  spliced code against the live environment — priced by its railway.)
- Exponents: two independent open regions in one segment are rejected;
  same-variable regions (`Intⁿ Intⁿ`) are fine.

## 15. Further reading

- `design-control-flow.md` — the control-flow design record (idiom
  inventory, deferral theorem, the guard-syntax history).
- `design-exponents.md` — exponents: theory, unification, erasure,
  the mapN open question (Fn-in-declarations has since shipped, §8).
- `design-effects.md` — the effects position (effects are wires, IO is
  a linear wire, the placement ladder as a PCM); converged, not
  scheduled.
- `design-metaprogramming.md` — typed code as the free category
  (`Path`), Forth's compiler lifted from a monoid; position taken.
- `guide-open-arity.md` — practical rules for open words.
- `spec-sums.md`, `expanded-spec.md`, `spec-code.md` — the deeper
  design records.
- `examples/` — every feature running, and CI-guarded; start with
  `registrar.braid` (most of the language in forty lines), then
  `ladder.braid`, `cuts.braid`, `stream.braid`, `arrows.braid`,
  `functors.braid`, `gla.braid`.
