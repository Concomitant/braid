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
| `---` | the row tail (§5): the last alternative of a sum or a code row, and the fifth parameter kind |
| `[` `]` | quotation |
| `(` `)` | grouping / rows / type arguments / binders |
| `\|` | row separator (rows / sum types) |
| `,` | separator in type arguments |
| `->` | binder arrow |
| `>=>` `>?>` `>!>` | railway operators (§7) |
| `^` | exponent in type position (`Int^3`); superscripts `Int³`, `ℝⁿ` also lex |
| `⟨` `⟩` `⇒` | `Fn` type brackets and arrow (type position): `Fn⟨Σ ⇒ Θ⟩` |
| `=IO>` , `⇒!` , `->!` | the io manifest label on an arrow (§3); the last two are legacy spellings |
| `=Rec>` , `=IO Rec>` | any written label set, in any order — displayed sorted (§3) |
| `=Log>` , `=IO Log Counter>` | display only: an arrow threading resource wires, manifest included (§3, §8) |
| `=Traced>` | a functor's receipt: minted by `use Traced`, never written (§3, §12) |
| `import "f.braid"` | include another file's declarations (§8) |

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
alike. Effect tails are invisible in display, the same hiding a `ρ`
tail already gets inside `Fn⟨…⟩`. Writing a grade in a type: §5 and
§8. The two edges: §14. A label set is **writable** wherever a type is
written — `=IO>`, `=Rec>`, `=IO Rec>`, in any order, displayed sorted;
the older `⇒!` and `->!` spellings still lex for old source and mean
`=IO>`.

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

**And a functor leaves a receipt.** `use F` for a functor (§6, §12)
rewrites the code under it, and mints `F` onto the manifest of what it
rewrote — so the arrow records not only what a word touches but what
built it, and every caller inherits the label by composition:

```text
poly    : Int =Traced> Int          -- elaborated under `use Traced`
caller  : Int =Traced> Int          -- calls poly; the receipt travels
report  : Int =IO Traced> •         -- and unions with any other label
```

Only a `use` mints. The label is not written, cannot be written
(`use@Traced` in your own source is an error), and does not have to be
threaded — which is what makes it evidence rather than a comment. It
is also part of the type: a declaration that says `Fn⟨Int ⇒ Int⟩`
refuses instrumented code exactly as it refuses io (§12, §14).

**And recursion leaves one too — `Rec`** (2026-09-09). `Rec` says *may
recurse without bound*, not *diverges*: it records that the word went
through the one operator that can iterate forever, which is a fact
about provenance and not a termination proof. A definition is not in
scope in its own body (§8), so `fix` and `loop` are the only two words
that can run unbounded — and they are the only two that mint `Rec`:

```text
fac    : Int =Rec> Int              -- built with `fix`
while  : Fn⟨ρ0 ⇒ (ρ1 | ρ2)⟩ Fn⟨ρ1 ⇒ ρ0⟩ ρ0 =Rec> ρ2
fold   : Fn⟨a0 a1 ⇒ a0⟩ a0 List(a1) ⇒ a0    -- a structural recursor: bare
map    : Fn⟨a0 ⇒ a1⟩ List(a0) ⇒ List(a1)    -- derived from it: bare
report : Int =IO Rec> •             -- unions like any other label
```

The generated structural recursors (`foldList`, `foldTree`, `foldNat`,
§8) descend on a smaller value and mint nothing, so the whole derived
library — `fold`, `map`, `filter`, `reverse`, `append`, `concat` —
stays bare. The reading that buys: **an unlabelled word is `fix`-free,
and therefore terminates by construction.** Two honest edges on that
sentence: it is *run-time* code it speaks about — a functor word runs
in the other phase, where a step budget rather than `Rec` is the bound
(§8) — and "fix-free ⟹ terminates" rests on the primitive set holding
no other unbounded construct, which is believed and has not been
audited end to end.

The built-in labels, then:

| label | minted by | says |
|---|---|---|
| `IO` | the four io prims (`print`, `readLine`, `readFile`, `writeFile`) | touched the world |
| `Rec` | `fix` and `loop` | may recurse without bound |
| `F` (any functor) | `use F` on a `functor` (§12) | was rewritten by `F` |
| `R` (any resource) | `use R` on a `resource` (§8) | threads the `R` wire |

One mechanism, four readings; union along composition for all of them.

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
  a quotation that uses `while` or `fix`; write `Fn⟨Int =Rec> Int⟩`
  (§14).
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
(`[print] : • ⇒ Fn⟨a0 =IO> •⟩` — the grade rides inside, and `ev`
transfers it out). Run with `ev : Fn⟨ρ0 ⇒ ρ1⟩ ρ0 ⇒ ρ1`
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

`use` names resources, instances, functors and — in a def's own
header — theories (§8), and opens a scope over them,
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

**The fourth kind of name is a theory** (§8) — and it may appear only
in a *def's own header*, where it makes the def a **template**: a body
that waits for an instance. `use Monoid` inside a body, or in a REPL
session, is refused, because there is no def for it to be the header
of.

**The third kind of name is a functor** (§8, §12): `use Fuel Metered`
threads the resource and then hands the routed, renamed body — as
`Code` — to the word `Metered` names, splicing back what it returns.
One header, four kinds, applied in a fixed order: templates expand,
instances rename, resources route, functors rewrite (left to right),
so a functor always sees finished wiring — and an expanded template
body is routed by every scope it landed in, exactly as if it had been
written there. `functor Both = metered ; traced` then `use Both`
is the recommended spelling whenever the order carries meaning:
functor composition IS `;`.  A functor scope also leaves its RECEIPT —
the label `Metered` on the manifest of everything it rewrote (§3, §12).

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

`>=>` is `[q, alt2]` — a *closed* copairing, and not an instance of
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

```braid
def name = program            # inline body — ends at the line
def name =                    # block body — `=` ends the line,
    program                   # body on the following (indented) lines
    continues
```

- `## doc` lines immediately before a `def`/`type`/`data` attach to it.
- Defs may **shadow** prims and prelude words; duplicate defs of the
  same name are an error.
- **No self-reference**: a definition is **not in scope in its own
  body**. `def f = … f …` is refused — "`f` refers to itself: a
  definition is not in scope in its own body — write the recursion with
  `fix` (MANUAL §8)" — and so is the old `recurse` spelling, which is
  gone. Every def is a closed spine over its prefix scope.
- **Recursion is `fix`**, a word with a type:

  ```braid
  fix : Fn⟨Fn⟨ρ0 =Rec> ρ1⟩ ρ0 ⇒ ρ1⟩ ⇒ Fn⟨ρ0 =Rec> ρ1⟩
  ```

  Tying the knot is itself pure — `fix` runs nothing — so the `Rec`
  label (§3) sits on the knot it hands *out* and on the `self` it hands
  *in*, never on `fix`'s own arrow. The body is asked for no grade of
  its own; it acquires `Rec` the moment it calls `self`.

  The body receives the knotted function **deepest**, then its own
  arguments, so the recursive call is an ordinary quoted call —
  `… >> self ... >> ev`. Three stages: quote the body, tie the knot,
  `ev` it.

  ```braid
  def fac =
      [(self n -> n >> zero? >> ((z -> 1) | (m -> m (m 1 >> - >> self ... >> ev) >> *)) >> merge)] ...
      fix ...
      ev
  # fac : Int =Rec> Int      5 >> fac  →  120
  ```

  `... ` carries the arguments over the quote (a stage's leftmost atom
  is its deepest wire, so `[body] ...` pushes the quote *under* them).
  An **open** binder (`self ... -> …`) names only the knot and lets the
  wire flow through, which keeps a point-free body point-free:

  ```braid
  def until100 =
    [(self ... -> lt100? >> (double >> self ... >> ev | _) >> merge)] ...
    fix ...
    ev
  ```

  `fix` is to recursion what `loop` (§10, a prelude def built on `fix`
  itself since 2026-09-12) is to iteration: an operator
  with laws, at a typed boundary. Prefer `loop`/`while`/`until` when the
  recursion is a tail call — it is one word and needs no knot — and
  prefer the **generated structural recursor** (`foldTree`, `foldNat`,
  the prelude's `fold`) when the recursion is structural, since those
  descend on a smaller value and terminate by construction — and, being
  bounded, mint no `Rec`.
- **The limit is gone** *(2026-09-12)*: the knot still arrives as a
  binder parameter, but a self-call inside a row component or a
  quotation now reflects (§6, §12), so `use F` over the `fix` idiom
  itself works — `use Traced` over a `fix`ed factorial traces every
  stage and prints `24`.
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
data Stream(a) = (a Fn⟨• =Rec> Stream(a)⟩)  # codata: recursion THROUGH a Fn
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
instance's are `slot = <program>`. Theory parameters are kinded: a bare
name is one wire, `...` a stack, and `k(_, _)` a type **constructor**
(below).

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

**Slot-local variables** (2026-09-09). A slot may name type variables
the theory does not declare, and each slot is **generalized over its
own**: they are quantified per slot, not shared between slots, and the
instance's body must be at least as general as the result. Any
lowercase name that is neither a theory parameter nor a type in scope
is such a variable, and a `...` in a slot of a theory with no stack
parameter is a slot-local *stack*. So `box : b ⇒ a` in `theory
Wrap(a)` declares `∀b. b ⇒ a`, and an instance filling it with
`_ 1 ; + ; toStr` is refused:

```text
instance W: slot 'box' is Int ⇒ Str but theory Wrap declares a0 ⇒ Str
('b' is universally quantified in the expected type but this code
requires it to be Int — the expected type promises the code works for
every choice of 'b', so it must stay parametric in it)
```

Nothing in the checker changed for this: `declaredSlots` already
generalized a slot's arrow and `checkInstance` already compared bodies
to it by **subsumption**, so the variables only had to survive the
parser.

**Constructor parameters** (2026-09-09). A theory parameter may be a
type constructor, written with its arity visible as underscores —
`theory Arrow(k(_, _))`. The kind must be visible because the two bare
readings are already taken (a name is a wire, `...` is a stack), and a
kind that is invisible is a kind that is guessed. Slots then apply it:

```braid
data Circuit(a, b) = Fn⟨a =Rec> b Circuit(a, b)⟩
data Pair(a, b) = a b

theory Arrow(k(_, _)) =
    arrP    : Fn⟨a =Rec> b⟩ =Rec> k(a, b)
    thenP   : k(a, b) k(b, c) =Rec> k(a, c)
    firstP  : k(a, b) =Rec> k(Pair(a, c), Pair(b, c))
    …

instance Circuits : Arrow(Circuit) =
    arrP    = arrC
    …
```

The instance head names a **declared data type**, not a type
expression, and that name is substituted for `k` before any slot is
forward-declared or checked. So `k` is not a higher-kinded type
variable and inference never meets one — this is the ML-functor move,
and `Ty` still has no constructor variable. The slots come out as
ordinary types:

```text
braid> use Circuits
ambient: use Circuits   (:clear or a bare `use` to leave)
braid> :t arrP
arrP : Fn⟨a0 =Rec> a1⟩ =Rec> Circuit(a0, a1)
braid> :t thenP
thenP : Circuit(a0, a1) Circuit(a1, a2) =Rec> Circuit(a0, a2)
braid> :t firstP
firstP : Circuit(a0, a1) =Rec> Circuit(Pair(a0, a2), Pair(a1, a2))
braid> use Funcs
ambient: use Funcs   (:clear or a bare `use` to leave)
braid> :t firstP
firstP : Arr(a0, a1) ⇒ Arr(Pair(a0, a2), Pair(a1, a2))
```

The slots carry `=Rec>` because the `Circuit` model builds every
circuit with `fix`; the function model does not, and a pure body under
a `=Rec>` slot passes by absorption — which is why `Funcs`'s `firstP`
comes back bare. A slot declares the *most* a model may do, as ever.

A slot is reached **through its scope, or not at all**: the compiler's
own spelling for the generated def is `Circuits@arrP`, and writing an
`@` yourself is an elaboration error (§12).


Four things are refused, each naming what is wrong:

```text
theory T(k(_, _)) =  op : k ⇒ k
  Type parameter k is a type constructor of arity 2: it is not a wire,
  write it applied — k(_, _)

theory T(k(_, _)) =  op : k(a) ⇒ k(a)
  Type constructor parameter 'k' takes 2 argument(s), but was given 1

instance Bad : Arrow(Nope)
  instance Bad: theory Arrow declares 'k' as a type constructor of
  arity 2, so its argument names a declared data type; 'Nope' is not one

instance Bad : Arrow(One)          # data One(a) = a
  instance Bad: theory Arrow declares 'k' with arity 2, but One takes
  1 argument(s)
```

`Fn` cannot fill a constructor parameter: it is built in and takes an
arrow rather than wires, and the refusal says so and suggests the
one-line wrapper (`data Arr(a, b) = Fn⟨a ⇒ b⟩`) that makes plain
functions an instance. `examples/circuits.braid` declares the Arrow
interface once and audits both models — circuits and functions —
against five runnable laws.

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

### Templates: a def written over a theory

A def whose `use` header names a **theory** is a *template*: its body
waits for an instance, and it is not a def at all until one arrives. A
def whose `use` header names an **instance** supplies one — every
template it calls is expanded there, renamed by that instance, and
**re-inferred there**:

```braid
def fold1 = use Monoid ; [op] unit ... ; foldExp   # a template over Monoid

def total  = use IntSum  ; fold1                   # instantiates it
def joined = use StrCat  ; fold1                   # and again, elsewhere
```

Because each instantiation is inferred on its own, each gets its own
**principal type** — there is no rank-1 wall, and nothing is passed at
run time:

```text
braid> :t total
total : Intⁿ⁰ ⇒ Int
braid> :t joined
joined : Strⁿ⁰ ⇒ Str
braid> use IntSum
ambient: use IntSum   (:clear or a bare `use` to leave)
braid> :t fold1
fold1 : Intⁿ⁰ ⇒ Int
braid> use StrCat
ambient: use StrCat   (:clear or a bare `use` to leave)
braid> :t fold1
fold1 : Strⁿ⁰ ⇒ Str
```

This is ML's functor application performed by the mechanism that
already existed: `use Inst` is a renaming, and a template is a body
that waits for one. There is no new syntax, no parameter list, and no
`@`.

**The rules, each with its message.** A template is *recorded*, not
defined: it never enters the environment or the runtime scope, because
it has no body that runs before an instance says what its slots mean.
So calling one outside every instance scope of its theory is an
elaboration error that names the **theory**, not a missing word:

```text
fold1 needs an instance of Monoid in scope (`use <instance>` before
calling it)
```

An instance of the *wrong* theory in scope gives the same message —
scope selection is by theory, and nothing is searched for. Templates
may call templates (`examples/build.braid`), and the instantiating
scope instantiates the whole chain. Nested scopes resolve
**innermost-first**, which is what renaming already did. Three more
refusals:

```text
def f = 1 ; use Monoid ; op
  `use Monoid` names a theory, and only a def's own header may: that is
  what makes the def a template, waiting for an instance

def f = use Monoid Pointed ; op
  a `use` header may name at most one theory (a template waits for one
  instance), but this one names Monoid Pointed

def loopy = use Monoid ; dup ; op ; loopy
  template loopy calls itself: a template is expanded at the call, so it
  cannot recurse
```

The last of those is reported where the template is *instantiated*, not
where it is written: a template's body is stored unexpanded, so the
no-self-reference rule above meets it only when a `use <instance>`
scope inlines it.

The rest of the header survives, so `use Monoid Log` is a template that
also threads a resource; the resource is routed where the template
*lands*, not where it was written.

**A template is over a theory, never over a resource name.** A resource
scope is *routing* — the offsets come from the header's arity — so a
body waiting for a resource would be waiting for an arity rather than
for a name; and the operations a generic handler needs (a seed, an
unroller) are per-carrier words, which is exactly what a theory names.
`examples/resources.braid` writes the generic handler that way, and it
is two lines per resource.

**Not "functors".** Templates are instance-parameterized *defs*;
`functor` (below) is the macro keyword, and for Haskell readers neither
is `Functor`/`fmap`.

**`functor Name = word`** names a **functor**: any def whose type is
`Code ⇒ Code` at pure grade. There is no `macro` keyword and nothing
to register — `functor Traced = marked` records that `use Traced`
means "run `marked` on this scope's wiring, at elaboration, and splice
the result". The word is checked at the first `use` (declarations are
hoisted, so that is where the prefix scope is what it will be at run
time): *must be Code ⇒ Code*, *must be pure* (it runs while the module
is being checked, so it cannot do IO — the `IO` label IS the phase
distinction; other labels on it are harmless), *not defined at this point* (a functor is runnable
before its first use: the one place source order is semantic), and a
looping functor exhausts a step budget rather than hanging the
compiler. Not Haskell's `Functor`: nothing is dispatched on a type;
this is a functor out of the free category of programs, selected by
name. §12 has what a functor may and may not do; `examples/traced.braid`
and `metered.braid` are the two idioms.

**`Fn` in declarations** — write a reified program as `Fn⟨Σ ⇒ Θ⟩`
(Unicode, mirrors `:t`) or `Fn(Σ -> Θ)` (ASCII); the inner stacks parse
like any type stack (params splice, `•` is empty, `Fn` nests). The
arrow's shape is part of the type: `⇒` declares a **pure** program and
rejects an io quotation, `Fn⟨Σ =IO> Θ⟩` (ASCII `Fn(Σ ->! Θ)`) declares an
io one and demands it (§3, §14). This
names function-carrier types — `Endo`, `Pred`, State-style monad
carriers — and, when the recursion runs *through* the `Fn`, gives
**codata**:

```braid
data Stream(a) = (a Fn⟨• =Rec> Stream(a)⟩)   # head + a THUNKED tail
```

The thunk is declared `=Rec>` because a stream producer is built with
`fix` (below), and a written arrow means what it says: an unlabelled
`Fn⟨• ⇒ Stream(a)⟩` refuses the very thunk the producer makes. `Rec`
is the honest word for it — the object is **productive** (every force
returns one cell) but **unbounded** (there is no last cell), and `Rec`
claims exactly the second thing.

A codata type gets constructor/unroll as usual but **no `foldName`** —
a structural fold through the thunk would diverge, so it is withheld by
construction; you observe instead (`unStream`, then `ev` to force
one cell). Productive corecursion guards its self-call under a quote —
`def from = [(self n -> n [n 1 >> + >> self ... >> ev] >> Stream)] ... >> fix ... >> ev`,
whose self-call still sits under the thunk. See
`examples/stream.braid`. Caveat: a `Fn` type whose stacks carry two
open stack-params (`Fn⟨s ⇒ s a⟩`) parses and expands, but won't
display-fold back (the leading-splice match is ambiguous — pin one
arity if you need the fold).

### Modules: `import "path.braid"`

One file's declarations in another file's scope, written as a
declaration line and resolved before anything is checked:

```braid
import "geometry.braid"
import "lib/shapes.braid"      # relative to THIS file's directory
```

What travels is **declarations** — defs, `type`/`data`, `resource`,
`theory`, `instance`, `functor`, and their `##` docs. What does not is
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
  ordering rule (a functor is runnable before its first `use`, §6)
  extends across files unchanged.
- **A relative path is relative to the importing file**, which is what
  lets a directory of modules move as one; failing that, the current
  directory is tried, so a program read from a pipe (`braid -`) can
  import too. Found in neither, the error names both places.

Nothing above needed machinery of its own: inclusion is textual, and
the composite is checked as a single module. That is also why a
`theory` declared in one file and its `instance` in another simply
work. See `examples/imports.braid`.

Reading the file is the **loader's** IO, at the same boundary that
reads the program you ran; elaboration still sees only parsed
declarations and stays pure. A module checked without a file context —
a REPL line, an embedded source string — has nothing to resolve an
import against and says so.

In a session, `:import "path.braid"` does the same thing, and is the
only way a session gets a `theory`, an `instance` or a `functor`, since
it cannot declare one:

```text
braid> :import "examples/traced.braid"
imported examples/traced.braid   (9 defs, 2 functors)
braid> def poly2 = use Traced >> dup >> *
def poly2 : ∀ . Int =IO Traced> Int
```

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
(`odd?`-family, `pack`/`pack2`, `sumN`, `id`, `loop`, `gt?`/`gte?`/
`lte?`) live in the prelude — the design bet ("primitives span
everything else in the language itself") is proven in both directions.

**There are 46 primitives** *(2026-09-12)*. A word keeps its place here
only if it is a **structure map** of the doctrine — cartesian
(`_`/`dup`/`swap`/`drop`/`pass`/`forget`), coproduct (`alt1…altN`,
`there`, `merge`), exponential (`ev`), recursion (`fix`), the open
coproduct (`into`), the exponent eliminators over `Aⁿ` — or if it
**touches the implementation**: arithmetic and strings, `eq?`, the four
io edges, reflection (`parse`/`unparse`/`reflect`/`evalAs`/`sameCode`/
`interpose`), and the type-level `weaken`/`finInt`. Everything else is
a prelude def with its derivation visible.

Wiring (cartesian structure):

| word | type | note |
|---|---|---|
| `_` | `a0 ⇒ a0` | the identity: the section hole, marking where the incoming wire goes. `id` is the WORD for the same morphism and is a **prelude def** (`def id = _`) — one morphism, one prim |
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
| `print` | `a0 =IO> •` — io (§3) |
| `true` / `false` | `• ⇒ Bool` |

Routers (the primitive comparators; hit = track 1 — the predicate
routers `odd?` `even?` `zero?` `negative?` are DERIVED prelude words
now, via `mod`/`equals`/`less` and the `(n | n)` re-routing pattern):

| word | type |
|---|---|
| `eq?` | `a0 a0 ⇒ (a0 a0 \| a0 a0)` — structural equality, any value |
| `lt?` | `Int Int ⇒ (Int Int \| Int Int)` — the only primitive order. `gt?` `gte?` `lte?` are **prelude defs** derived from it (§10), with identical schemes |

Sums & control:

| word | type |
|---|---|
| `alt1`…`altN`, `ok`/`here`/`again`, `miss`/`done` | `ρ0 ⇒ (… \| ρ0 \| σ0)` — spelled `in1`…`inN` before 2026-09-12; renamed (one spelling, **no `inN` alias**) because `[h >> alt1] into` read badly and `in` is the prefix `into` lives beside |
| `there` | `(σ0) ⇒ (ρ0 \| σ0)` |
| `merge` | `(ρ0 \| ρ0) ⇒ ρ0` |
| `into` | `Fn⟨ρ0 ⇒ (σ0)⟩ (ρ0 \| σ0) ⇒ (σ0)` — the **open** eliminator (§6): the copairing `[h, id]`, handling the first alternative into the remaining row and shifting the rest. Not derivable: over a residual it is the only copairing there is. |
| `ev` | `Fn⟨ρ0 ⇒ ρ1⟩ ρ0 ⇒ ρ1` — the exponential's **counit**; spelled `apply` before 2026-09-12, renamed to match `curry` (§10). The only word that consumes an `Fn`, and not derivable: naming a value never runs it. |
| `fix` | `Fn⟨Fn⟨ρ0 =Rec> ρ1⟩ ρ0 ⇒ ρ1⟩ ⇒ Fn⟨ρ0 =Rec> ρ1⟩` — the knot; body takes it deepest, and the knot carries `Rec` (§8) |

Metaprogramming & IO (railway-typed edges):

| word | type |
|---|---|
| `reflect` | `Fn⟨ρ0 ⇒ ρ1⟩ ⇒ (Code \| Str)` |
| `evalAs` | `Fn⟨ρ0 ⇒ ρ1⟩ Code ρ0 ⇒ (ρ1 \| Str ρ0)` — witness-checked |
| `unparse` | `Code ⇒ Str` |
| `parse` | `Str ⇒ (Code \| Str)` |
| `interpose` | `Code Code ⇒ Code` — `η c`: insert η after every stage of c; η must be `ρ ⇒ ρ` or `E ρ ⇒ E ρ`, checked (§12) |
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

**Loops** *(all derived since 2026-09-12)*: `loop :
Fn⟨ρ0 =Rec> (ρ0 | ρ1)⟩ ρ0 =Rec> ρ1` is the **Elgot dagger**, and it is
a prelude def over `fix`:

```braid
def loop = (f ... -> [(self ... -> f ... >> ev >> (self ... >> ev | pass) >> merge)] ... >> fix ... >> ev)
```

`f† = ∇ ∘ (f† + id) ∘ f`, written out: the body routes into
`(continue | done)`, the continue track re-enters through the knot, the
done track falls out, and `merge` — the codiagonal ∇ — joins them. Note
it needs **no `into`**: the row is closed and two-track, so the
copairing `[f†, id]` is just `(f† | pass) >> merge`; `into` (§6) is for
the open case. `Rec` is *inherited* from `fix` rather than declared,
which is why `loop`'s body type now reads `=Rec>` where the prim said
`⇒` — the body genuinely does run inside an unbounded knot. An
*inferred* quote absorbs the label, so every existing use still types;
a *written* pure `Fn⟨Σ ⇒ (Σ|Θ)⟩` handed to `loop` is now refused, which
is the honest reading. Cost measured: 100 000 iterations in 3.2 s
against 1.9 s for the builtin, and no growth in memory.

`while` `until` (+ `whileFn`/`untilFn`) are three-line defs over it:
`while : Fn⟨ρ0 =Rec> (ρ1 | ρ2)⟩ Fn⟨ρ1 =Rec> ρ0⟩ ρ0 =Rec> ρ2`.

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
when `reflect` misses); the by-generators functors `stagewise : Fn⟨Stage ⇒
Code⟩ Code ⇒ Code` and `atomwise : Fn⟨Atom ⇒ Stage⟩ Code ⇒ Code`
(`flatMap` on the spine, one level down for `atomwise`);
`interposeRaw : Code Code ⇒ Code` (unchecked `interpose`); `lift2 :
Fn⟨Code ⇒ Code⟩ Fn⟨ρ0 ⇒ ρ1⟩ ⇒ Fn⟨ρ0 ⇒ ρ1⟩` — a functor applied at
runtime, the program its own witness and its own fallback; `box`.

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

# general recursion: quote the body, tie the knot, ev (§8)
[(self ... -> _ 100 >> less? >> (2 _ >> * >> self ... >> ev | _) >> merge)] ... >> fix ... >> ev
```

There is **no guard syntax in the parser** — every idiom above is
prelude defs plus core forms. See `examples/ladder.braid` and
`design-control-flow.md` for the full inventory and the reasoning.

## 12. Metaprogramming

`reflect` turns a quotation into its **spine**: `Code = List(Stage)`,
`Stage = List(Atom)`, `data Atom = (prim | int | str | sym | quote |
row | group)`. Lambdas reflect as pure wiring (abstraction
elimination) — **every** binder, open ones and the naming form
included, and whatever the body contains: injections, `merge`, open
groups. The parameter block is treated as a *resource* for the body's
duration — parked as the deepest wires, exactly where `use` parks a
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

See `examples/cuts.braid` for splices in context.

### Functors, and the ones known to type

A **functor** (§8) is a pure `Code ⇒ Code` word applied to a scope's
wiring by `use`. `reflect` forgets types — it goes from typed programs
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
| `use E` for a resource `E` | tensoring, `E ⋉ –` — and a binder's parameter block is the same functor, `P ⋉ –` (§12 above) | the elaborator's routing |
| `interpose [η]` | whiskering: `η` after every cut, `η : ρ ⇒ ρ` or `E ρ ⇒ E ρ` | `interpose` itself, by subsumption |
| `use Inst` for an instance | a model of the theory: every generator replaced by a typed image | `checkInstance` (§8) |
| a local rewrite `p ↦ q` with `scheme(q) ≥ scheme(p)` | a typed generator image | `subsumes` — the `rule` declaration, not yet shipped |
| `lift2 [m]` on any `Code ⇒ Code` `m` | the runtime lift | per program, at run time; never fails — it falls back |

Everything not in the table — delete a stage, reorder, reverse,
choose by neighbour — is re-inferred and may fail. Such functors are
not wrong; they are **audited** rather than **guaranteed** (laws over
`Code`, `sameCode` on expansions, §12).

**The closure gate is lifted** *(2026-09-12; it read "one limit is on
the floor, not on any row").* `reflect` used to refuse a binder
parameter captured in a quotation or a row component, and `fix` (§8)
hands the knot in as exactly such a parameter — so a `use F` scope
containing the `fix` idiom *itself* was refused before any functor ran
(*`use Traced`: Unknown primitive: self*). Abstraction elimination now
has wiring to translate a capture into: `capture` under a quote,
`dist2` over a row (§6, §10). That is table row 2 (`P ⋉ –`) over the
cartesian **closed** structure rather than the cartesian one, and it is
a derivation, not three new primitives —
`design-macros.md`, the 2026-09-12 amendment. The two corners it left
open — a **residual** row `(p | q | ---)`, and a flat row of three or
more tracks — closed the same day with the generator `#dist:K` (§6), so
`reflect` is now total on binder code, full stop.
`sameCode` is unchanged: it normalizes the
term it is handed and never runs elimination, so two spellings of a
capturing binder are still *"outside the structural fragment: a
binder"* — "I cannot tell" is not "they differ".

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
something better` (`examples/lifting.braid`), and a `Code ⇒ Code`
functor becomes one of those two ways: `use F` at elaboration (the
expansion is re-inferred, and its arrow is the receipt) or `lift2 [F]`
at run time, where the program is its own witness — the result has the
program's arrow *by construction* and a rewrite the witness refuses
leaves the original running (`examples/metered.braid`). The type
system blesses exactly that and nothing weaker: it cannot say "this
rewrite preserves every program's type" as a rank-1 `Fn` type, because
*unification blesses a call; subsumption blesses a rule* — and a rule
is a declaration, checked once.

`stagewise`/`atomwise` are `flatMap` on the spine: functorial by
construction (a stage's image depends on that stage alone), which is a
law that comes free, not a promise that the result types.

**The receipt.** `use F` mints `F` onto the manifest of everything it
elaborated (§3), so a rewrite that changes no requirement — a tracer,
an optimizer — is still recorded, and the record travels to every
caller by composition. Mechanically the receipt is a *word*: `use@F :
∀ρ. ρ =F> ρ`, `pass` with a label, prepended to the expansion — the
same unit endomorphism `interpose` inserts, doing nothing but being
typed. Three consequences, in rising order of usefulness:

- it is a stage, so it survives `reflect`: a reflected traced program
  reads `use@Traced >> dup >> …`, and splicing it somewhere else
  carries the label rather than losing it;
- it cannot be forged. Writing `use@Traced` yourself is an error — *a
  label is minted by a scope, never written by hand* — which is the
  difference between provenance and a comment. The rule is the
  character, not the word: **`@` is the compiler's**, so an instance's
  generated slot def is refused in source the same way and points at
  the scope that reaches it — *`Loud@emit` is the compiler's spelling
  of a slot: reach it with `use Loud`* (§8);
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
closed arity — `sameCode` **errors** rather than answering, because "I
cannot tell" is not "they differ". A binder is outside it whether or not
it captures: `sameCode` normalizes the term it is handed and never runs
abstraction elimination, so the closed structure (§6, 2026-09-12)
decided nothing new here. Bringing the normalizer through a row, and
with it `dist ; undist = id` and `capture ; ev = substitution`, is the
next stage's work; `examples/distributive.braid` states those laws and
*runs* them at sample points in the meantime.
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
- Effects don't sub-effect: composing forces two arrows' manifests
  EQUAL (the join you expect comes from absorption into an open tail),
  so a pure quote unified into an io context types as io for that use.
  Let-generalization at a `def` boundary restores per-use freshness;
  inside one expression nothing does.
- The same goes for a functor's receipt, and it surprises people once:
  a *written* type with no labels refuses labelled code. An `evalAs`
  witness `Fn⟨Int ⇒ Int⟩`, or a theory slot declared `a ⇒ a`, will not
  take a word elaborated under `use Traced` — *Cannot unify effects:
  Traced vs pure*. Write the label where you mean it
  (`use Traced ; […]` as the witness), or elaborate the word outside
  the functor. Inferred types never hit this: they just carry the
  label onward.
- **And a written type with no `Rec` refuses recursive code.** This is
  the same rule a third time, and it is the one you will meet without
  ever writing a functor: `Fn⟨Int ⇒ Int⟩` will not take a quotation
  that uses `while` (or `until`, or `fix`, or any word built from
  them). Write `Fn⟨Int =Rec> Int⟩`.

  ```text
  data Sink = (Fn⟨Int ⇒ Int⟩)
  [[_ 100 >> less?] [2 _ >> *] ... >> while] >> Sink >> drop

  error: Cannot unify effects: Rec vs pure (the unlabelled side's
  manifest is written and fixed: write =Rec> on that arrow, or keep
  this code label-free)
  ```

  It reaches three places in particular: a codata declaration's thunk
  (`data Stream(a) = (a Fn⟨• =Rec> Stream(a)⟩)` — §8), a theory slot a
  `fix`-built body will fill (`examples/circuits.braid`), and an
  `evalAs` witness over runtime-loaded code that loops. A `=Rec>`
  arrow still accepts *non*-recursive code — an inferred row is open
  and absorbs the label — so the labelled spelling is the permissive
  one, and the bare spelling is the promise.
- **`reflect` is total on binder code** *(2026-09-12)*. It had three
  corners that morning and has none by evening: a `use F` scope over the
  `fix` idiom, a parameter inside a **residual** row, and a parameter
  inside a flat row of **three or more tracks**. The first two were
  wiring that did not exist yet (`capture`, `dist2`); the third was a
  real coproduct limit — `case2`/`merge` are binary — and the generator
  `#dist:K` (§6) is what lifts it, being a generator rather than a
  derivation precisely because no handler can be written for the tracks
  a residual hides. What `reflect` still refuses is not about binders:
  a `...` before the end of a stage in a binder body, and a name the
  body does not resolve.
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
  `:t` is elaborated the same way, so under `use IntSum` it answers
  `:t op`. A session cannot *declare* a theory, an instance or a
  functor, but `:import` brings them in and then they may be named —
  a theory itself may not, since only a def's header may name one.
  A template defined in a session is reported as one (*template trip
  over Monoid*) and listed by `:defs`. This is selection, not sugar:
  it is what ML's `open` does.
- A `use` with nothing after it **in a file** is an error (*"`use …`
  ends its scope"*)
  — like a binder, its body is the rest of the scope, so there has to
  be a rest.
- An instance's argument for a **wire** parameter is a full type
  **expression**, so a theory may be instantiated at a parameterized
  type (`Wrap(List(Int))`, `Wrap(Fn⟨Int ⇒ Int⟩)`) — which is what every
  structure worth having a theory of actually looks like. Its argument
  for a **constructor** parameter is a bare declared name instead
  (`Arrow(Circuit)`), because that name is substituted into the slots
  rather than being a type. Theory and instance heads are read against
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
| one body over **every** model of a theory | a `def` whose `use` names the theory (a *template*) | expanded and re-inferred per instance — its own principal type each time |
| a category of **processes** | `data` + your own composition word | then present it as a `theory` if it has laws |

Worked examples, in that order: `lifting.braid` first (every functor
is a function `Fn⟨a ⇒ b⟩ ⇒ something better` — the logged version of a
function, game rules as lifted moves), then `examples/tree.braid` and
`stream.braid` (data and codata), `resources.braid` and `payroll.braid`
(a resource, and a whole program using one), `ladder.braid` (control
flow that is all ordinary defs), `theories.braid` (theories and
instances), `circuits.braid` (a stream transducer — a genuinely
different category — as data plus a composition word plus
`theory Arrow(k(_, _))`, the Arrow interface stated once over a
constructor parameter and audited against two models).

**An effectful arrow is a resource + a macro + a theory**: the resource
carries the state, the macro installs and discharges it, and the theory
says what the operations must satisfy. Declaring and *entering* have
been ordinary since `use`; **discharging** is the third, and it needs
no construct either — a wrapping macro seeds the wire, applies the
program, and unrolls it, and the arrow loses the label across it:

```braid
resource Log = Str
def note      = unLog _ ; cat ; Log
def collectLog = (f -> [f ("" ; Log) ... ; ev ; unLog ...])
-- collectLog : Fn⟨ρ0 =Log> ρ1⟩ ⇒ Fn⟨ρ0 ⇒ Str ρ1⟩
```

That is Plotkin–Pretnar's *handler is a model*, read in a language
whose instances already are models: discharge is a wrapping functor,
not a form. It is per-resource **by name**; the generic one is a
template (§8) over a theory naming the two operations a handler needs
(`seed : • ⇒ e`, `unwrap : e ⇒ a`), which then reads
`Fn⟨ρ0 =Log> ρ1⟩ ⇒ Fn⟨ρ0 ⇒ Str ρ1⟩` under `use Logs` and
`Fn⟨ρ0 =Counter> ρ1⟩ ⇒ Fn⟨ρ0 ⇒ Int ρ1⟩` under `use Counts` —
`examples/resources.braid` writes both halves.

**What not to reach for.** Effects do not need new machinery: state is a
`resource`, failure is the railway sum track, writer is a `resource`,
nondeterminism is `List`, reader is a `resource` you only read. Only IO
is irreducible, and it is a *grade* on the existing arrow (`=IO>`), not an
arrow of its own. `examples/arrows.braid` shows that `Control.Arrow`'s
whole interface — `arr`, `>>>`, `first`, `***`, `&&&`, `|||`, `app` —
is already the syntax rather than a library.

**The trade, stated once.** Because instances are selected by name and
nothing is inferred or dispatched, you cannot write code generic over
"any monoid" and have the right one found for you; you write `use
IntSum`. What you *can* write once is the body — a template over the
theory (§8) — and the scope that instantiates it is the one line you
still have to say. What you get back is annotation-freeness, coherence in a
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
- `design-macros.md` — elaboration as a library: functors over `Code`,
  the five invariants, the fibration picture and the functors known to
  type, the manifest stated once, and the 2026-09-09 amendment
  "recursion at a typed boundary" (why `fix` replaced self-reference,
  what `Rec` does and does not promise, and what it cost).
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
