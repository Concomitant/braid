# Braid

A strongly typed, concatenative, stack-based language — a textual
syntax for cartesian string diagrams. Programs are wiring diagrams:
juxtaposition is parallel wires, `>>` is composition, and the type
system infers a principal type for every diagram with no annotations,
ever.

The design bet: keep the primitive set tiny (~35 morphisms) and prove
it spans everything else **in the language itself**. The entire
standard library is derived user code: booleans, comparisons, `while`
and `until`, the list type and its library, the sum and list monads
and their distributive law, conditionals, data-type folds — and the
metaprogramming layer, where reflected code is a list you munge with
the same library.

```text
def fizzbuzz = (n -> (n 15 >> mod >> zero) ["FizzBuzz"] [(n 3 >> mod >> zero) ["Fizz"] [(n 5 >> mod >> zero) ["Buzz"] [n >> toStr] ... >> cond] ... >> cond] ... >> cond)

15 >> range >> [1 ... >> + >> fizzbuzz] ... >> map >> printAll
```

## Build and run

No local GHC needed — a Docker one-liner:

```sh
docker run --rm -it -v "$PWD":/w -w /w haskell:9.4-slim \
  sh -c "cabal build exe:braid && cabal run -v0 braid -- examples/fizzbuzz.braid"
```

`braid <file>` runs a file; `braid` alone opens the REPL:

```text
braid> :t true
true : • ⇒ Bool
braid> 7 >> [_ 100 >> less?] [2 _ >> *] ... >> while
stack: 112  :  Int
braid> :doc while
## run step while predicate hits; exit with the miss payload
```

`:t` shows a type (`:t!` raw, un-folded); `:doc` and `:defs` browse
the prelude; every REPL line runs against a persistent typed stack.

## A tour, in ten ideas

1. **Everything exact.** Constants are maps from nothing (`1 : • ⇒
   Int`), operations consume exactly their inputs (`+ : Int Int ⇒
   Int`). Passing other wires along is always explicit: `1 ... >> +`
   is increment. No implicit anything — this is what keeps inference
   principal.
2. **Sums are alternate flows.** `(Int | Str)` is one wire carrying
   either. Rows `(f | g)` run one branch; `merge` rejoins. Bool is
   just `(• | •)`.
3. **Predicates are routers.** `odd? : Int ⇒ (Int | Int)` *routes*
   its input instead of returning a detached boolean — branches
   receive the data. Drop the `?` to forget instead: `odd : Int ⇒
   Bool`, then `[then] [else] ... >> cond`.
4. **Failure is a track.** `>=>` composes hit-tracks and lets misses
   fall through: `even? >=> _ 100 >> less? >=> double >> ok` is a
   validation railway. `readFile` and `parse` are railway stages too.
5. **Guards are total.** `if … | [action] router … otherwise …
   endif` — omitting the otherwise-clause is a *type error* (the miss
   track is the empty sum).
6. **Loops are values.** `loop` is Elgot iteration; `while` and
   `until` are three-line prelude defs; general recursion uses
   `recurse` with a placement discipline.
7. **Data types are declared sums.** `data Tree(a) = (a | Tree(a)
   Tree(a))` — the name rolls, `unTree` unrolls (both free at
   runtime), and `foldTree` is *generated*: elimination by points,
   `tree >> [leafCase] [nodeCase] ... >> foldTree`.
8. **The list defines itself.** `type List(a) = (• | a List(a))` in
   the prelude; literals, `map`, `fold`, `filter` are all derived.
9. **Laws are programs.** Associativity checks run as code
   (`examples/laws.braid`), and they're operational: a checked monoid
   is a license to parallelize its fold (`examples/parallel.braid`).
10. **Code is data.** `reflect` turns a quotation into its spine — a
    list of stages of atoms — so `take`/`map`/`reverse` slice and
    transform *programs*; `evalCode` runs them (dynamically checked,
    failures on the miss track); `unparse`/`parse` and
    `readFile`/`writeFile` round-trip code through disk. The
    graphical-linear-algebra transpose is `reverse >> map dualize`
    (`examples/transpose.braid`).

## Examples

`examples/` is the guided tour: start with `fizzbuzz`, `validate`
(railway), `guards`, `iterate` (while), then `nat` and `tree` (data
types and folds), `lists`, `sniff` (typed CSV-cell refinement),
`sac` (split-apply-combine), `laws`, `parallel`, `matrices`, and
finish with `code`, `transpose`, and `io`.

## Status

A design-driven prototype: one Haskell module for the whole language
(typechecker, interpreter, REPL), a 320+ case test suite, and spec
notes (`expanded-spec.md`, `spec-sums.md`, `spec-code.md`) recording
each design decision and the theorems that forced it (why sums never
flatten, why the unroll is explicit, why n-ary eliminators are
generated per type). Deliberately absent so far: floats, modules
beyond the auto-loaded prelude, typed splicing, labeled record
fields, effect types.
