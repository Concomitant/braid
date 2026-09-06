# Braid

A strongly typed, concatenative, stack-based language — a textual
syntax for cartesian string diagrams. Programs are wiring diagrams:
juxtaposition is parallel wires, `>>` (or `;`, or a newline) is
composition, and the type system infers a principal type for every
diagram with no annotations, ever.

The design bet: keep the primitive set tiny (~40 morphisms) and prove
it spans everything else **in the language itself**. The entire
standard library is derived user code: booleans, comparisons, `while`
and `until`, the list type and its library, the sum monad,
conditionals and guard ladders, data-type folds — and the
metaprogramming layer, where reflected code is a list you munge with
the same library.

```text
# scores travel as a bare bundle; the syllabus is a dot product;
# the letter is a decision ladder; fairness is a law you can run
def dot = zipN ; [(acc a b -> (a b ; *) acc ; +)] 0 ... ; foldExp2

def letter =
    p ->
    (89 p ; less) "A" ...
    (79 p ; less) "B" ...
    (69 p ; less) "C" ...
    "F"               ...
    decide

95 90 95 ; weighted ; letter ; print     # A — and dot : Intⁿ Intⁿ ⇒ Int
                                         # was inferred, not written
```

## Install and run

**Prebuilt binary** (Linux x86_64, macOS arm64/x86_64) from
[Releases](https://github.com/Concomitant/braid/releases):

```sh
tar xzf braid-*.tar.gz && ./braid examples/registrar.braid && ./braid
```

**No install at all** — clone and use the `./braid` script, which keeps
the toolchain in a container and the sources here:

```sh
./braid examples/registrar.braid   # run a file
./braid                            # open the REPL
./braid - <<'EOF'                  # run a program on stdin
95 90 95 ; grade ; print
EOF
```

Only the first run pays for compiling. A release binary unpacked over
the script keeps the same interface, so `./braid file.braid` means the
same thing either way.

**From source**: `cabal build exe:braid` with GHC ≥ 9.4.

`braid <file>` runs a file; `braid` alone opens the REPL:

```text
braid> :t true
true : • ⇒ Bool
braid> :t dupN
dupN : a0ⁿ⁰ ⇒ a0ⁿ⁰ a0ⁿ⁰
braid> 7 >> [_ 100 >> less?] [2 _ >> *] ... >> while
stack: 112  :  Int
braid> :doc decide
## fold a product of decisions accumulated line by line with `...`
```

`:t` shows a type (`:t!` raw, un-folded); `:doc` and `:defs` browse
the prelude; every REPL line runs against a persistent typed stack. A
bare `use Log` line opens an ambient scope over the rest of the
session — the resource threads itself through every later line, and a
bare `use` leaves.

## A tour, in thirteen ideas

1. **Everything exact.** Constants are maps from nothing (`1 : • ⇒
   Int`), operations consume exactly their inputs (`+ : Int Int ⇒
   Int`). Passing other wires along is always explicit: `1 ... >> +`
   is increment. No implicit anything — this is what keeps inference
   principal.
2. **Sums are alternate flows.** `(Int | Str)` is one wire carrying
   either. Rows `(f | g)` run one branch; `merge` rejoins; `assocL` /
   `assocR` re-nest; `case(a, b, c)` folds a whole nested sum at once.
   Bool is just `(• | •)`.
3. **Predicates are routers.** `odd? : Int ⇒ (Int | Int)` *routes*
   its input instead of returning a detached boolean — branches
   receive the data. Drop the `?` to forget instead: `odd : Int ⇒
   Bool`.
4. **Failure is a track.** `>=>` composes hit-tracks and lets misses
   fall through; `>?>` chains along the miss track (it *is* elif);
   `readFile` and `parse` are railway stages too. None of them are
   primitive: each is `>> (stage | injector) >> merge`, bundled.
5. **Names label wires; they don't cut them.** `x y ->` consumes the
   wires it names, so the body re-pushes them. `-> x y` instead tags
   them as they go by — identity at runtime, wires flowing on, names in
   scope for the rest of the block, the way a label sits beside a wire
   in a drawn diagram. The arrow's side is the whole rule. It is sugar,
   not machinery: `-> x y z` *is* `x y z ... -> x y z ...`, and
   `reflect` compiles it back to dup/swap/drop to prove it.
6. **Guard ladders are ordinary words.** Bind the subject and a guard
   is a bare Bool beside its answer; `...` accumulates one lane per
   line and `decide` folds the product — first true lane wins:
   ```text
   x ->
   (x >> negative) "neg"  ...
   (x >> zero)     "zero" ...
   (x >> toStr)           ...
   decide
   ```
   Guards-as-data variants (`firstTrue`, clause ladders + `choose`,
   `if`/`elif`/`else` fold-as-you-go) are all prelude defs. No guard
   syntax exists in the parser.
7. **Loops are values.** `loop` is Elgot iteration; `while` and
   `until` are three-line prelude defs; general recursion uses
   `recurse` with a placement discipline.
8. **Data types are declared sums.** `data Tree(a) = (a | Tree(a)
   Tree(a))` — the name rolls, `unTree` unrolls (both free at
   runtime), and `foldTree` is *generated*: elimination by points.
9. **The list defines itself.** `type List(a) = (• | a List(a))` in
   the prelude; literals, `map`, `fold`, `filter` are all derived. A
   cell is one wire — declaration parameters are kinded, a bare name
   being a wire and `...` a whole stack — so a pair-list is
   `List(Box(a b))` and the *whole* library works on it, not just
   `fold`. Keeping stack variables in tail position is what makes the
   type system's tail-only invariant true rather than aspirational.
10. **Widths are exponents.** `Intⁿ` (typed `Int^n`) is n wires — a
    vector with no box, an exponential object with finite base. One
    fold word is variadic over bare stack products (`sumN : Intⁿ ⇒
    Int`); `mapN`/`mapN2` lift any ordinary word pointwise, so the GLA
    generators are *derived* (`def addN = zipN ; [+] ... ; mapN2`); a
    matrix is a value `Fn⟨Intⁿ ⇒ Intᵐ⟩`; and a 3-weight syllabus cannot
    meet a 4-score transcript — dimension errors are type errors. `n`
    is erased: the running stack's width is its own witness. And `Aⁿ`
    *is* the function space `Fin(n) → A` kept tabulated, so indices are
    first-class and bounds-checked by the type (`at`, `indicesN`,
    `checkedAt`) — each one witnessed by a live bundle or a literal's
    own offset (`examples/index.braid`).
11. **Laws are programs.** Associativity, De Morgan, dot-product
    symmetry, the copy/add bialgebra — they run as code
    (`examples/laws.braid`, `gla.braid`, `registrar.braid`), and
    they're operational: a checked law is a license to rewrite
    (contrapose a chain, parallelize a fold, flip a weighting).

    Laws now have a front door. A **theory** declares named slots and
    the laws they must satisfy; an **instance** supplies programs and
    is *audited* by running them — at module start, before main, so a
    failing model is not an instance and the module is rejected:
    ```text
    theory Monoid(a) =
        unit   : • ⇒ a
        op     : a a ⇒ a
        sample : • ⇒ a
        law leftUnit = (sample ; unit ... ; op) sample ; eq? ; (forget ; true | forget ; false) ; merge

    instance IntSum : Monoid(Int) =
        unit   = 0
        op     = +
        sample = 7

    def total = use IntSum ; [op] unit ... ; foldExp     # Intⁿ⁰ ⇒ Int
    ```
    This is not typeclasses: nothing is inferred and nothing is
    dispatched. `use IntSum` picks an instance **by name**, and the
    pick is a renaming at elaboration — once per scope, no dictionary
    per call. The trade is deliberate: you give up inferring *which*
    instance, and keep annotation-freeness, coherence in a structural
    type system, and freedom from higher kinds. The audit is
    signatures, completeness, and laws typed `• ⇒ Bool`; the honest
    limit is that a law runs on the samples it names — property
    testing's poor cousin, minus generation and shrinking, plus being
    part of what it *means* to be an instance
    (`examples/theories.braid`).
12. **Effects are wires.** State, logs, readers, exceptions,
    nondeterminism — the whole effect zoo decomposes into structure
    the language already has: a threaded wire, a captured closure, the
    railway sum, a list. Only IO is irreducible, so `io` is the one
    label a grade ever needs. An arrow marked io prints `=IO>`, a pure one
    `⇒` — the label sits on the arrow just like resource names do — and
    which you get is **inferred, never annotated**: five prims are marked
    (`print`, `readLine`, `readFile`, `writeFile`, `evalCode`) and every
    other grade follows from composition — `def shout = toStr >> print : a0 =IO> •`.
    Quoting stays pure, since pushing an action isn't doing it:
    `[print] : • ⇒ Fn⟨a0 =IO> •⟩`, and `apply` is what transfers the grade out.

    The other wires you can *name*: `resource Log = Str` declares a
    threaded wire — nominal, so `Int Int` is never silently a
    GameState, and one wire however wide its contents. A run of them
    shared by both sides of an arrow folds onto the arrow, grade
    included: `note : Str =Log> •`, `peek : • =IO Log> •`. And `use`
    makes the threading disappear — it opens a scope over its
    resources, taking the rest of the block as its body, and an
    elaborator writes every `_` and `...` for you:
    ```text
    def score =
        use Log Counter
        dup ; *
        bump
        "scored "
        note                # Int ρ0 =Log Counter> Int ρ0
    ```
    Nothing there is compiler magic you couldn't write: what `use` does
    to a pure stage is `lift : Fn⟨ρ0 ⇒ ρ1⟩ ⇒ Fn⟨a0 ρ0 ⇒ a0 ρ1⟩`, an
    ordinary prelude word (tensorial strength — run a program one wire
    deeper). It only saves you the counting (`examples/resources.braid`
    shows both spellings side by side). Scopes compose: a word threading
    exactly its scope's resources is callable from that scope, so a
    resourceful step is an ordinary fold's step function and a whole
    stateful pass over data is `[step] seed ... ; fold`
    (`examples/payroll.braid`).
13. **Code is data.** `reflect` turns a quotation into its spine — a
    list of stages of atoms — so `take`/`map`/`reverse` slice and
    transform *programs*; `evalCode` runs them (dynamically checked,
    splices are type-checked at the site and mismatches ride the miss
    track); `unparse`/`parse` and `readFile`/`writeFile` round-trip code
    through disk. The graphical-linear-algebra transpose is
    `reverse >> map dualize`.

## Examples

`examples/` is the guided tour: start with `fizzbuzz`, `validate`
(railway), `ladder` (every guard idiom), `iterate` (while), then `nat`
and `tree` (data types and folds), `lists`, `conditionals` and `case`
(rows, deferred sums, `case(…)`), `tag` (naming wires in passing),
`resources` (threaded wires and `use`),
`lifting` (every functor is `Fn⟨a ⇒ b⟩ ⇒ something better`:
the logged version of a function, game rules as lifted moves),
`index` (Fin(n) and a small dataframe),
`sniff` (typed CSV-cell refinement), `sac` (split-apply-combine),
`laws`, `theories` (theories, instances, laws that run),
`arrows` (Control.Arrow's interface, as plain syntax) and `circuits`
(the arrows that aren't: stream transducers as ordinary data),
`payroll` (a whole small program: a resource, a theory and a grade
meeting in one pass over data),
`parallel`, `matrices`, `gla` (bundles and the bialgebra),
`code`, `transpose`, `io` — and finish with `registrar`, which uses
most of the language in forty lines about grade school.

## Extending it

There is **one arrow** — no `Arrow` class, no `Monad`, no higher kinds —
so "a new kind of computation" is never a new arrow. It is a `data`
(a new carrier, codata included), a `resource` (state threaded through a
region), a plain `def` (a new combinator — loops and guards are already
values), a `theory` + `instance` (a swappable interface with runnable
laws), or, for a genuinely different category like a stream transducer,
a `data` plus your own composition word. MANUAL §15 is the table, with a
worked example for each row.

## Status

A design-driven prototype: one Haskell module for the whole language
(typechecker, interpreter, REPL), a 698-case test suite, a full
reference (`MANUAL.md` — every feature, with checker-verified types),
and design notes recording each decision and the theorems that forced
it —
`expanded-spec.md`, `spec-sums.md`, `spec-code.md`,
`design-control-flow.md` (why guard syntax kept getting built and torn
out, and what replaced it), `design-exponents.md` (dimension-indexed
segments: why exponents not stars, why unary successors suffice, why
the eliminator is a fold and not an unroll), and `design-macros.md`
(elaboration as a library: functors over `Code`, the five invariants,
and the transport of `⇒` into other categories). `READING.md` is the
annotated bibliography behind all of them. Deliberately absent so
far: floats, modules beyond the auto-loaded prelude, labeled record
fields, and the last stage of the effects staging —
`resource` wires, `use` scopes, and theories/instances with runnable
laws have shipped, but there is no resource mark, no linear `World`
and no handlers (`design-effects.md` has the position, the staging,
and the two decisions implementation reversed).
