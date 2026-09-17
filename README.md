# Braid

A concatenative language with a static type system, where a program is
a string diagram: stages composed with `;`, wires side by side within
a stage. Written in Haskell. A prototype.

```braid
table Trades = "examples/data/trades.csv"          # declares Trades, sym, px, qty, loadTrades
def notional with Frame = dup ; px qty ; _ toFloat ; fmul
"examples/data/trades.csv" ; loadTrades ; (notional ; print | print) ; merge
```

## What is in it

- Types inferred, never annotated. Every arrow carries a manifest of
  labels (`=IO Recursive>`) that records what its code went through;
  labels join under composition.
- Sums, products (the stack), closures, a fixpoint, and rows with an
  open tail. Recursion is a header clause, `with Recursive`.
- `theory`, `model`, `transformation`: a theory presents operations
  and laws; a model interprets it; a transformation is checked
  slot by slot, proved where a normalizer can and sampled otherwise.
- Models of the Doctrine transport whole programs into another
  category: circuits, data frames, probability as a Markov category.
  The Doctrine's hom-object ranges over whole STACKS, so a stage of any
  width transports as itself — products stay flat.
- `Code` as data, with reflection (`getCode`, `typeOfCode`, `declOf`)
  and user-written `Code ⇒ Code` functors.
- 66 primitives; everything else is in the prelude, in Braid.

## Install and run

Prebuilt binaries for Linux x86_64 and macOS from
[Releases](https://github.com/Concomitant/braid/releases):

```sh
tar xzf braid-*.tar.gz && ./braid examples/registrar.braid && ./braid
```

Or clone and use the `./braid` script, which runs the toolchain in a
container:

```sh
./braid examples/registrar.braid   # run a file
./braid                            # the REPL
```

Building from source needs GHC 9.4 and cabal; `cabal build all` and
`cabal run braid-tests`.

## Where to read

- `MANUAL.md`: the language reference, with types checked against the
  implementation.
- `CONSTRUCTS.md`: the declaration layer, construct by construct.
- `examples/`: 71 programs, each run by the test suite.
- `design-*.md` and `READING.md`: the design decisions and the papers
  behind them.

## Status

One Haskell module for the checker, interpreter, and REPL, a 1174-case test suite that runs
every example, and design notes recording each
decision. Not yet present: labelled record fields, totality checking
(`Recursive` records that a word may not terminate; it does not prove
that others do), handlers, and a linear world for `IO`.

The documentation needs a cleanup pass. It was written stage by stage
and uses terms it never defines for a reader (`spine`, `stage`,
`receipt`, `K-word`, `carrier`, and others). Until that pass is done,
`MANUAL.md` is accurate but not always self-explanatory.
