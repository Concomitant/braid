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

## Build and run

No local GHC needed — a Docker one-liner:

```sh
docker run --rm -it -v "$PWD":/w -w /w haskell:9.4-slim \
  sh -c "cabal build exe:braid && cabal run -v0 braid -- examples/registrar.braid"
```

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
the prelude; every REPL line runs against a persistent typed stack.

## A tour, in eleven ideas

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
5. **Guard ladders are ordinary words.** Bind the subject and a guard
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
6. **Loops are values.** `loop` is Elgot iteration; `while` and
   `until` are three-line prelude defs; general recursion uses
   `recurse` with a placement discipline.
7. **Data types are declared sums.** `data Tree(a) = (a | Tree(a)
   Tree(a))` — the name rolls, `unTree` unrolls (both free at
   runtime), and `foldTree` is *generated*: elimination by points.
8. **The list defines itself.** `type List(a) = (• | a List(a))` in
   the prelude; literals, `map`, `fold`, `filter` are all derived.
9. **Widths are exponents.** `Intⁿ` (typed `Int^n`) is n wires — a
   vector with no box, an exponential object with finite base. One
   fold word is variadic over bare stack products (`sumN : Intⁿ ⇒
   Int`); the GLA generators are width-polymorphic (`addN : Intⁿ Intⁿ
   ⇒ Intⁿ`, `zipN : aⁿ bⁿ ⇒ (a b)ⁿ`); a matrix is a value `Fn⟨Intⁿ ⇒
   Intᵐ⟩`; and a 3-weight syllabus cannot meet a 4-score transcript —
   dimension errors are type errors. `n` is erased: the running
   stack's width is its own witness.
10. **Laws are programs.** Associativity, De Morgan, dot-product
    symmetry, the copy/add bialgebra — they run as code
    (`examples/laws.braid`, `gla.braid`, `registrar.braid`), and
    they're operational: a checked law is a license to rewrite
    (contrapose a chain, parallelize a fold, flip a weighting).
11. **Code is data.** `reflect` turns a quotation into its spine — a
    list of stages of atoms — so `take`/`map`/`reverse` slice and
    transform *programs*; `evalCode` runs them (dynamically checked,
    failures on the miss track); `unparse`/`parse` and
    `readFile`/`writeFile` round-trip code through disk. The
    graphical-linear-algebra transpose is `reverse >> map dualize`.

## Examples

`examples/` is the guided tour: start with `fizzbuzz`, `validate`
(railway), `ladder` (every guard idiom), `iterate` (while), then `nat`
and `tree` (data types and folds), `lists`, `conditionals` and `case`
(rows, deferred sums, `case(…)`), `sniff` (typed CSV-cell refinement),
`sac` (split-apply-combine), `laws`, `parallel`, `matrices`, `gla`
(bundles and the bialgebra), `code`, `transpose`, `io` — and finish
with `registrar`, which uses most of the language in forty lines about
grade school.

## Status

A design-driven prototype: one Haskell module for the whole language
(typechecker, interpreter, REPL), a 420+ case test suite, a full
reference (`MANUAL.md` — every feature, with checker-verified types),
and design notes recording each decision and the theorems that forced
it —
`expanded-spec.md`, `spec-sums.md`, `spec-code.md`,
`design-control-flow.md` (why guard syntax kept getting built and torn
out, and what replaced it), `design-exponents.md` (dimension-indexed
segments: why exponents not stars, why unary successors suffice, why
the eliminator is a fold and not an unroll). Deliberately absent so
far: floats, modules beyond the auto-loaded prelude, typed splicing,
labeled record fields, effect types.
