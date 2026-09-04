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
| `⇒!` , `->!` | the effectful arrow — an arrow carrying the `io` grade (§3) |
| `=Log>` , `=IO Log Counter>` | display only: an arrow threading resource wires, grade included (§3, §8) |

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

**Every arrow carries a grade** — the set of resource wires it touches.
There is one label today, `io`: a pure arrow prints `⇒`, an effectful
one prints `⇒!`.

```braid
1 >> print                  # • ⇒! •            composition propagates it
def shout = toStr >> print  # a0 ⇒! •           inferred through defs
def quiet = toStr >> drop   # a0 ⇒ •            pure stays bare
[print]                     # • ⇒ Fn⟨a0 ⇒! •⟩   pushing an action is pure
[print] 5 >> apply          # • ⇒! •            apply transfers it out
[dup >> *] 5 >> apply       # • ⇒ Int           same apply, pure quote
```

Grades are **inferred, never annotated**: five prims are marked io
(`print`, `readLine`, `readFile`, `writeFile`, `evalCode` — §9) and
every other arrow's grade follows from composition. Higher-order words
(`apply`, `loop`, `map`, `foldExp`, `mapN`) share the grade of the
quotation they run, so one `apply` serves pure and effectful quotes
alike. Effect tails are invisible in display, the same hiding a `ρ`
tail already gets inside `Fn⟨…⟩`. Writing a grade in a type: §5 and
§8. The two edges: §14.

**A threaded resource folds onto the arrow too.** A `resource` (§8) is
a nominal wire you thread rather than consume; resource wires ride
**deepest**, and when both sides of an arrow begin with the same run of
them, that run moves onto the arrow — which is exactly what "threaded
through" means. The io grade rides on the same arrow, because it says
the same kind of thing:

```text
note  : Str =Log> •                       -- Str in, Log threaded
bump  : • =Counter> •
score : Int ρ0 =Log Counter> Int ρ0       -- two resources, in `use` order
peek  : • =IO Log> •                      -- grade and resources, one arrow
```

The fold is display, not inference: it fires when the prefixes match
exactly, and a resource anywhere but the bottom prints as an ordinary
wire (`_ bump ... : a0 Counter ρ0 ⇒ a0 Counter ρ0`). Threading them by
hand is `_`/`...` as usual; `use` (§6) writes that padding for you.

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
- `...` must be the final atom of its stage;
- the naming binder `-> x y z` ends the stage it follows, and its body
  is the rest of the scope;
- `use R1 R2` (§6) is the same shape: the resource names end it, and
  the rest of the scope is its body.

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

- **Base**: `Int`, `Str`, `Sym`.
- **`•`** — the empty stack; the terminal object. Constants are points
  `• ⇒ A`; `forget : ρ ⇒ •` is the unique map to it.
- **Products** are juxtaposition: `Int Str` is two wires. There is no
  *built-in* pair type — the stack is the pair — but you can declare
  one (`data Pair(a, b) = (a b)`), and `Box(...)` carries a whole stack
  as a single wire, which is how multi-wire aggregates go inside a
  `List` (§8).
- **Sums**: `(Δ₁ | … | Δₙ [| σ])` — one wire carrying alternative
  *stacks*. Rigid nesting: `(A | (B | C))` never flattens.
  `Bool = (• | •)`, `Maybe(...) = (... | •)` are prelude aliases.
  **`Maybe` is payload-FIRST**, unlike Haskell's `Nothing | Just a`.
  That order is arbitrary in Haskell but load-bearing here: `in1` is the
  track `ok` builds and `>=>` threads, so a payload-second `Maybe`
  could not ride the railway at all (§7).
- **`Fn⟨Σ ⇒ Θ⟩`** — a reified program (quotation type). The internal
  hom: `apply` is modus ponens. The arrow inside carries its grade, and
  a declared one MEANS it: `Fn⟨Str ⇒ •⟩` refuses an io quotation
  (*Cannot unify effects: io vs pure*); `Fn⟨Str ⇒! •⟩` is the io form
  (§8).
- **Named types**: `type` aliases and `data` declarations (§8).
  Display folds structural types back to their alias names when they
  match exactly (`:t!` shows raw).
- **Resources**: `resource Name = <stack>` (§8) — a `data` declaration
  under another keyword. One nominal wire, carrying its contents boxed,
  meant to be threaded rather than consumed; a run of them shared by
  both sides of an arrow folds onto the arrow as `=Log Counter>` (§3).
- **Exponents**: `A^n` (input `Int^3`, `R^n`; display `Int³`, `ℝⁿ`) — a
  segment repeated n times. `n` is erased at runtime; concrete
  exponents expand away. See §13 and `design-exponents.md`.
- **`Fin(n)`** — an index into a bundle of width n. `Aⁿ` *is* the
  function space `Fin(n) ⇒ A`, stored tabulated and flat. The bound is
  a type, erased exactly as every other width: at runtime a `Fin` is a
  bare `Int`. See §9 and `design-indices.md`.

## 6. Program forms

### Quotation `[p]`
`[p] : • ⇒ Fn⟨…⟩` — pushes the program as a value; a **pure point**
even when `p` does real work, and even when that work is io
(`[print] : • ⇒ Fn⟨a0 ⇒! •⟩` — the grade rides inside, and `apply`
transfers it out). Run with `apply : Fn⟨ρ0 ⇒ ρ1⟩ ρ0 ⇒ ρ1`
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
-> x y             # naming: LABELS two wires without consuming them
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

### Ambient scopes `use R1 R2`

One header may name **both**, freely mixed — they are two kinds of
scoped selection, not two features:

```braid
resource Log = Str
theory Sink(a)   = emit : a ⇒ a
instance Loud : Sink(Int) = emit = dup ; print ...

def run =
    use Log Loud        # a resource AND an instance
    dup ; *
    emit                # resolves to Loud's; the Log threads past it
```

A resource contributes a wire the elaborator threads; an instance
contributes no wire at all and disappears at elaboration, leaving its
slots renamed.

`use` names resources and instances (§8) and opens a scope over them,
taking the **rest of the enclosing scope as its body** — the same scope-taking
shape as the binders `x y ->` and `-> x y`, and the same rule about
needing a rest to reach. An elaborator running between parse and
inference writes every `_` and `...` the threading needs, from the
resource declarations alone:

```braid
resource Log     = Str
resource Counter = Int
def note = unLog _ ; cat ; Log                  # Str =Log> •
def bump = unCounter ; 1 ... ; + ; Counter      # • =Counter> •

def score =
    use Log Counter
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
at statically known offsets (resources ride deepest, in `use` order),
and the ordinary type checker verifies the result.

**`use` asserts its claim.** The incoming wires must really be those
resources, even when the body never touches one:

```braid
def f = use Log >> dup          # a0 ρ0 =Log> a0 a0 ρ0 — Log is claimed,
                                #   though the body never mentions it
```

**`use` also selects instances**, and may mix them with resources in
one header — it is the same word for both kinds of scoped selection:

```braid
def total = use IntSum ; [op] unit ... ; foldExp   # Intⁿ⁰ ⇒ Int
```

A header may name both kinds at once — `use Log Counter IntSum` opens
a scope over two resources and one instance, in one line.

An instance name binds the theory's slots to that instance's programs
for the rest of the scope. Unlike a resource, an instance claims no
wire and asserts nothing about the incoming stack: the selection is a
renaming at elaboration (§8), so it disappears before inference.

**What `use` does to a pure stage is `lift`** (§10), an ordinary
prelude word: `lift : Fn⟨ρ0 ⇒ ρ1⟩ ⇒ Fn⟨a0 ρ0 ⇒ a0 ρ1⟩` runs a program
one wire deeper, composable once per context wire. Nothing about
ambient threading is machinery you cannot write yourself; `use` only
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
type Result(a, e) = (a | e)           # parameterized; each param is ONE WIRE
type Box(...) = (...)                 # `...` — a whole STACK, as one wire
type Tagged(t, ...) = (t ...)         # mixed: a wire, then the stack
type T = Int^3                        # an RHS is a STACK — exponents fine
type Mat(n, m) = Fn⟨Int^n ⇒ Int^m⟩    # n, m are WIDTHS: used under `^`
type Sq(n) = Mat(n, n)                # widths pass on to another alias
type Endo(a) = Fn⟨a ⇒ a⟩              # a reified program as a type…
type Pred(a) = Fn(a -> (a | a))       # …Unicode Fn⟨Σ ⇒ Θ⟩ or ASCII Fn(Σ -> Θ)
type Sink(a) = Fn⟨a ⇒! •⟩             # an io program: ⇒! (ASCII `->!`)
data List(a) = (• | a List(a))        # recursive nominal type
data Tree(a) = (a | Tree(a) Tree(a))
data Stream(a) = (a Fn⟨• ⇒ Stream(a)⟩)   # codata: recursion THROUGH a Fn
```

**Parameters are kinded**, three ways. A bare name stands for exactly
**one wire**; `...` stands for a whole **stack**, and may only be the
last parameter (at most one); a name used under `^` in the body is a
**width**. The `...`-last rule is what keeps every stack variable in
tail position, so no declaration can spell a stack variable with wires
after it:

```braid
data Pair(a, b) = (a b)        # two wires — inexpressible before kinds
data Box(...)   = (...)        # a whole stack in one wire
data Bad(...)   = (... Int)    # rejected: '...' must be last in its stack
type L = List(Int Str)         # rejected: List's cell takes one wire
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

**`resource Name = <stack>`** declares a threaded wire — a `data`
declaration under another keyword, and nominal for the same reason
`data` is:

```braid
resource Log     = Str
resource Counter = Int
resource GameState = Int Int
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
  the order a `use` names them, which is what puts every offset a known
  distance from the deepest wire (§6). Operations are ordinary defs
  that unroll, work, and roll back:

```braid
def note = unLog _ ; cat ; Log                  # Str =Log> •
def bump = unCounter ; 1 ... ; + ; Counter      # • =Counter> •
```

Threading a resource by hand is `_` and `...` like anything else; `use`
(§6) writes that padding. See `examples/resources.braid` and
`design-effects.md`.

**`theory` / `instance`** — named slots, models, and laws that run.
Both are **block** declarations: a header line ending in `=`, then
indented lines, the same shape as `def name =` with an indented body. A
theory's entries are `slot : Σ ⇒ Θ` and `law name = <program>`; an
instance's are `slot = <program>`. Theory parameters are kinded exactly
like a type declaration's (a bare name is one wire, `...` a stack).

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

def total  = use IntSum ; [op] unit ... ; foldExp     # Intⁿ⁰ ⇒ Int
def joined = use StrCat ; [op] unit ... ; foldExp     # Strⁿ⁰ ⇒ Str
```

**These are not typeclasses.** Nothing is inferred and nothing is
dispatched: `use IntSum` (§6) selects an instance **by name**, and the
selection is a *renaming at elaboration* — each slot resolves to a
generated def, so resolution costs nothing per call, once per scope.
The trade is deliberate (`design-effects.md`): you give up inferring
*which* instance, and get annotation-freeness, coherence in a
structural type system, and no need for higher kinds.

**An instance is audited, three ways**, each with its own message:

| check | example message |
|---|---|
| slot signatures, read at the instance's argument | `instance Bad: slot 'unit' is • ⇒ Str but theory Monoid declares • ⇒ Int` |
| completeness, and no extras | `instance Partial: no binding for 'op' (declared by theory Monoid)` · `instance Extra: 'huh' is not an operation of theory Monoid` |
| a law is a program `• ⇒ Bool` | `law 'silly' of I must be a program with type '• ⇒ Bool', but is • ⇒ Int` |

**Laws run.** They are ordinary Braid programs, and they execute **at
module start, before main**. A failing one rejects the module:

```text
law 'leftUnit' fails for instance BadUnit: an instance must be an
audited model of its theory
```

`theory` and `instance` are file declarations, not REPL lines (the
REPL says so). See `examples/theories.braid`, §14 for the limits, and
`design-effects.md` for the position.

**`Fn` in declarations** — write a reified program as `Fn⟨Σ ⇒ Θ⟩`
(Unicode, mirrors `:t`) or `Fn(Σ -> Θ)` (ASCII); the inner stacks parse
like any type stack (params splice, `•` is empty, `Fn` nests). The
arrow's shape is part of the type: `⇒` declares a **pure** program and
rejects an io quotation, `Fn⟨Σ ⇒! Θ⟩` (ASCII `Fn(Σ ->! Θ)`) declares an
io one and demands it (§3, §14). This
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
`drop = (x -> x >> forget)` — the
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

Arithmetic & strings (all exact; `-`, `div`, `mod` are bottom-op-top):

| word | type |
|---|---|
| `+` `-` `*` `div` `mod` | `Int Int ⇒ Int` |
| `cat` | `Str Str ⇒ Str` |
| `toStr` | `a0 ⇒ Str` |
| `asInt?` | `Str ⇒ (Int \| Str)` |
| `symStr` | `Sym ⇒ Str` |
| `print` | `a0 ⇒! •` — io (§3) |
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
| `evalCode` | `Code ρ0 ⇒! (ρ1 \| Str ρ0)` — io, dynamically checked |
| `unparse` | `Code ⇒ Str` |
| `parse` | `Str ⇒ (Code \| Str)` |
| `readLine` | `• ⇒! (Str \| Str)` — io; one line from stdin, EOF misses |
| `readFile` | `Str ⇒! (Str \| Str)` — io |
| `writeFile` | `Str Str ⇒! (• \| Str)` — io; hit is the empty success, miss carries the error |

These four and `print` are the **whole** io surface: nothing else is
marked, every other grade is inferred (§3). `reflect` and `parse` stay
pure — `reflect` READS a quotation, it never runs it — while
`evalCode` is io unconditionally, because what it will run is not
known until it runs.

Exponent tier (widths erased; see §13):

| word | type |
|---|---|
| `foldExp` | `Fn⟨a0 a1 ⇒ a0⟩ a0 a1ⁿ ⇒ a0` |
| `foldExp2` | `Fn⟨a0 a1 a2 ⇒ a0⟩ a0 (a1 a2)ⁿ ⇒ a0` |
| `dupN` | `a0ⁿ ⇒ a0ⁿ a0ⁿ` |
| `zipN` | `a0ⁿ a1ⁿ ⇒ (a0 a1)ⁿ` |
| `unzipN` | `(a0 a1)ⁿ ⇒ a0ⁿ a1ⁿ` |
| `mapN` | `Fn⟨a0 ⇒ a1⟩ a0ⁿ ⇒ a1ⁿ` |
| `mapN2` | `Fn⟨a0 a1 ⇒ a2⟩ (a0 a1)ⁿ ⇒ a2ⁿ` |
| `at` | `Fin(n) a0ⁿ ⇒ a0` — index the bundle; 0 is the DEEPEST wire |
| `indicesN` | `a0ⁿ ⇒ (Fin(n) a0)ⁿ` — tag every wire with its own index |

Folds collapse a bundle; `mapN`/`mapN2` rebuild one, which is what lets
you **lift an ordinary word pointwise**. `addN` and `scaleN` are
therefore prelude defs, not primitives — and so is any lift you need:

```braid
def addN  = zipN >> [+] ... >> mapN2        # the bundle monoid ∇
def mulN  = zipN >> [*] ... >> mapN2        # NOT linear — outside the GLA set
def maxN  = zipN >> [(x y -> (x y >> less) [y] [x] ... >> cond)] ... >> mapN2
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
| `fin0`, `fin1`, `fin2`, … | `• ⇒ Fin(n+k+1)` — index literals, like `inN` |

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
(`List(a) List(b) ⇒ List(a b)`) `all` `any` `partitionSum` `sequence`
(List over the sum monad) `printAll`.

**Router algebra** (quoted predicates as values): `not` (track swap)
`negate` `both` `either` `equals?` `less?` `equalsTo` `lessThan`
`else?` (always-hit) `assocL`/`assocR` (re-nest a sum);
`splice : (ρ0 | (σ0)) ⇒ (ρ0 | σ0)` (flatten one level of nesting into
the parent row, any inner arity); the ladder steps `settle :
(ρ0 | (ρ0 | ρ1)) ⇒ (ρ0 | ρ1)` (guard ladder — fold an agreeing answer
into the pile) and `settleR : ((ρ0 | ρ1) | ρ1) ⇒ (ρ0 | ρ1)` (its
validation mirror). See `examples/settle.braid`.

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

**Strength**: `lift : Fn⟨ρ0 ⇒ ρ1⟩ ⇒ Fn⟨a0 ρ0 ⇒ a0 ρ1⟩` — run a program
one wire deeper, the wire beneath untouched; compose it once per
context wire (`[dup >> *] >> lift >> lift : • ⇒ Fn⟨a0 a1 Int ⇒ a0 a1
Int⟩`). This is tensorial strength, the action of `(A ⊗ −)` on a
morphism, and it is exactly what threads a resource past a pure stage —
so ambient threading (§6) needs no machinery for the pure case, only
the counting. `def lift = (f -> [_ (f ... >> apply)])`.

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
elimination) — **every** binder, open ones and the naming form
included, since the erased passthrough is the stack's *tail* and so
rides above the parameter block inside each stage's `pass`, while
parameters are fetched by depth from the deepest wire and never cross
it. True closures, and parameters used inside a quotation or a row
component, are still gated onto the miss track with an explanation. Code is an ordinary list — slice with `take`, transform
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
disk (`examples/io.braid`). `box : Code ⇒ Fn⟨ρ ⇒! (r | Str ρ)⟩` defers
instead of running — the other half of `reflect`'s round trip.

**Cut soundness** (`examples/cuts.braid`): Braid is not
token-concatenative, but at spine granularity the concatenative
property is a runnable theorem — every stage-boundary cut yields two
runnable pieces with `run(prefix) ; run(suffix) = run(whole)`, atom
slices within a stage are runnable sub-tensors, and any slice boxes.

### The splice check

Every `evalCode` site is checked against the type its context imposes.
The checker stamps each invocation during elaboration with the output
type that constraint solving settles on. When the splice runs, its
inferred result type is unified against that stamp. A mismatch rides the
miss track with the untouched input segment as evidence — no crash, same
error path as `parse` or `readFile`.

Splices that generalize — those whose stamp would become part of a
definition's polymorphic scheme — freeze their result type into
existential constants (`∃0`, `∃1`, …), because a caller's argument type
must not determine the splice's output. Callers must consume the hit
track parametrically (`forget`, `drop`, `pass`), never `print` (which
demands exactly one wire of a known type). The cost is transparent:

```braid
box : Code ⇒ Fn⟨ρ0 ⇒! (∃0 | Str ρ0)⟩
```

Deferring the *run* costs the result's *type*: what boxed code returns
is only discovered when it runs. To use a splice's result at a known
type, splice it where that type is statically known.
Splices nested inside spliced code share the same discipline. A stamp
variable that also appears in the definition's input is rejected outright
— *"a splice's result type shares a0 with this definition's input"* — to
prevent a caller from choosing the runtime-built code's type by choosing
an argument.

See `examples/cuts.braid` for splices in context.

### Deciding a law: `sameCode`

`sameCode : Fn⟨Σ ⇒ Θ⟩ Fn⟨Σ ⇒ Θ⟩ ⇒ Bool` answers whether two programs
are the **same morphism**, by normalizing rather than testing.

A program built from wiring (`id`/`_`/`dup`/`drop`/`swap`/`pass`),
composition and juxtaposition, over words treated as *uninterpreted*, is
a morphism of the free cartesian category on those words. Its word
problem is solvable: run the program on distinct symbolic inputs and
read off the tuple of terms it returns. Two programs are equal exactly
when they consume the same number of wires and return the same tuple.
Defs inside the fragment are inlined (so `sameCode` sees through your
own words); a def already being expanded is recursive and stays opaque.

```text
[dup ; _ dup] [dup ; dup _]       ; sameCode   # true  — coassociativity
[dup ; toStr toStr] [toStr ; dup] ; sameCode   # true  — copy is natural
[toStr ; dup] [dup ; toStr _]     ; sameCode   # false
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

Outside the fragment — a quotation, a row, a binder, a word with no
closed arity, a quote that captured a bound name — `sameCode` **errors**
rather than answering, because "I cannot tell" is not "they differ".
`examples/laws.braid` shows decided and sampled laws side by side.

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

## 14. Sharp edges (things the checker will teach you)

- `1 >> 2` — the incoming wire is uncovered (constants don't thread;
  write `2 id` or `2 ...`).
- Binder bodies are input-closed — a `(x -> …)` stage consumes exactly
  its parameters; thread extra wires with `_` beside the binder atom.
- Quotes are points (`• ⇒ Fn`): pushing one beside live wires needs
  `_` or `...` — the same frame discipline as every constant.
- Row arms must fit on one line; arms must agree in type to `merge`.
- Ladder lanes are juxtapositions — a `;`/`>>` inside a lane needs a group.
- `def name = x -> …` ends at the line — unless it leaves a bracket
  open, in which case the lines that close it belong to the body. For
  multi-line bodies generally, use the block form (`def name =` newline
  `x ->`).
- `f >> x y -> …` is not a cutting binder — that form is recognized at
  the start of a scope or after a newline. The naming form `-> x` has no
  such restriction; it ends whatever stage it follows.
- A binder with nothing after it is an error: its body is the rest of
  the scope, so there has to be a rest.
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
- Effects don't sub-effect: composing forces two arrows' grades EQUAL
  (the join you expect comes from absorption into an open tail), so a
  pure quote unified into an io context types as io for that use.
  Let-generalization at a `def` boundary restores per-use freshness;
  inside one expression nothing does.
- Several effectful atoms in one tensor stage are **legal**, and run
  left to right — deepest wire first, the order they are written in
  (`print print : a0 a1 ⇒! •`). That order is decreed, not checked, so
  a mis-ordered pair is a wrong behaviour, not a type error.
- Inside a `use` scope, a stage may contain **at most one resource
  operation, and it must be alone in that stage** — otherwise *"a stage
  may contain at most one resource operation, and it must be alone —
  put X on its own line"*, naming the operation it found. An operation
  touching *some* of the scope's resources is rejected (*"X threads Log,
  but this scope is over Log Counter"*): the elaborator brings one
  resource wire up, acts, and puts it back, and a subset at once would
  need a permutation it will not guess. The exception is the one that
  matters: a word threading **exactly** the scope's resources, in
  order, is already shaped like the stack, so it applies with no
  routing at all. That is what makes `use` scopes **compose** — a word
  written under `use Log Counter` is callable under `use Log Counter`,
  and without it a multi-resource word could be written with `use` and
  then never called from one. Both limits are the elaborator's,
  not the type system's — by hand, `_`/`...` still do anything.
- **In the REPL, `use` is a session-wide scope.** A file's `use` takes
  the rest of the block as its body; a session has no rest yet, so a
  bare `use Log Counter` line opens a scope over every LATER line and
  every subsequent line is elaborated inside it. A bare `use` (or
  `:clear`) leaves; `:s` shows the ambient scope alongside the stack.
  Only resources can be named there — a session cannot declare a
  theory, so instances stay file-only. This is selection, not sugar:
  it is what ML's `open` does.
- A `use` with nothing after it **in a file** is an error (*"`use …`
  ends its scope"*)
  — like a binder, its body is the rest of the scope, so there has to
  be a rest.
- An instance's carrier is a full type **expression**, so a theory may
  be instantiated at a parameterized type (`Pipeline(Circuit(Int,
  Int))`, `Wrap(List(Int))`, `Wrap(Fn⟨Int ⇒ Int⟩)`) — which is what
  every structure worth having a theory of actually looks like. Theory
  and instance heads are read against every type in scope, the
  prelude's included.
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
  each instance supplies it — not a workaround, but an audited model
  supplying the evidence its audit runs on.
- Laws are checked by **running**, on whatever samples the program
  names — property testing's poor cousin next to QuickCheck (no
  generation, no shrinking). What is different is that the check is
  part of *being an instance*, not a separate test suite.
- `theory` and `instance` are file declarations; the REPL takes
  programs, and says so.
- A resource is **nominal**: structural shapes never fold into one.
  `resource GameState = Int Int` leaves `swap : a0 a1 ⇒ a1 a0` exactly
  as it was, and only a genuine rolled `GameState` wire ever displays
  as one. The ceremony (`unLog` before you touch the contents, `Log`
  after) is what buys the arrow fold its meaning.
- A `Fin` prints as a bare integer. Erasure is honest — a `Fin` *is* an
  `Int` at runtime — but output does not distinguish an index from an
  ordinary `Int`; only the type does.
- An `∃` in a displayed type marks an **existential**: a type the
  definition cannot know, because it is whatever code built at runtime
  turns out to return (§12). It is frozen rather than generalized —
  unifying with nothing but itself — so callers consume it
  parametrically (`forget`, `drop`, `pass`) and never at a specific
  type like `print`, which would be assuming the answer.

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
| **state** threaded through a region | `resource` + `use` | a threaded wire, with the `_`/`...` written for you |
| a new **combinator** or control form | an ordinary `def` | loops are values, guards are words, `...` accumulates |
| a swappable **interface with laws** | `theory` + `instance` | models selected by name, audited by running the laws |
| a category of **processes** | `data` + your own composition word | then present it as a `theory` if it has laws |

Worked examples, in that order: `lifting.braid` first (every functor
is a function `Fn⟨a ⇒ b⟩ ⇒ something better` — the logged version of a
function, game rules as lifted moves), then `examples/tree.braid` and
`stream.braid` (data and codata), `resources.braid` and `payroll.braid`
(a resource, and a whole program using one), `ladder.braid` (control
flow that is all ordinary defs), `theories.braid` (theories and
instances), `circuits.braid` (a stream transducer — a genuinely
different category — as data plus a composition word plus a theory).

**What not to reach for.** Effects do not need new machinery: state is a
`resource`, failure is the railway sum track, writer is a `resource`,
nondeterminism is `List`, reader is a `resource` you only read. Only IO
is irreducible, and it is a *grade* on the existing arrow (`⇒!`), not an
arrow of its own. `examples/arrows.braid` shows that `Control.Arrow`'s
whole interface — `arr`, `>>>`, `first`, `***`, `&&&`, `|||`, `app` —
is already the syntax rather than a library.

**The trade, stated once.** Because instances are selected by name and
nothing is inferred or dispatched, you cannot write code generic over
"any monoid" and have the right one found for you; you write `use
IntSum`. What you get back is annotation-freeness, coherence in a
structural type system, and no higher kinds to explain. That is the same
trade `theory` makes everywhere, and it is deliberate.

## 16. Further reading

- `design-control-flow.md` — the control-flow design record (idiom
  inventory, deferral theorem, the guard-syntax history).
- `design-exponents.md` — exponents: theory, unification, erasure,
  the mapN open question (Fn-in-declarations has since shipped, §8).
- `design-indices.md` — `Fin(n)` and witnessed introductions: why
  `Aⁿ` is `Fin(n) → A`, and why there is no `tabulate`.
- `design-effects.md` — the effects position (effects are wires, IO is
  a linear wire, the placement ladder as a PCM); **stages 1, 2, 3 and 4
  — the io grade, `resource` declarations, `use`, and
  theories/instances with runnable laws — have shipped**, including the
  amendment that flipped the resource wires from the top of the stack
  to the bottom. Only stage 5 (the linear `World`) is position only.
- `design-metaprogramming.md` — typed code as the free category
  (`Path`), Forth's compiler lifted from a monoid; position taken.
- `guide-open-arity.md` — practical rules for open words.
- `spec-sums.md`, `expanded-spec.md`, `spec-code.md` — the deeper
  design records.
- `examples/` — every feature running, and CI-guarded; start with
  `registrar.braid` (most of the language in forty lines), then
  `ladder.braid`, `cuts.braid`, `stream.braid`, `arrows.braid`,
  `functors.braid`, `resources.braid`, `theories.braid` (theories,
  instances, and laws that run), `gla.braid`.
