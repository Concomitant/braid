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
- One model head, with optional clauses: a model may take a model
  parameter (a family), and it may carry an **object map** —
  `model Mod in Base(Int ↦ Mod7 via reduce)` reinterprets a program at
  another type, mapping literals through `via`, unfolding the defs it
  meets, and refusing by name any word it has no image for
  (`examples/modular.braid`).
- Models of the Doctrine transport whole programs into another
  category: circuits, data frames, probability as a Markov category.
  The Doctrine's hom-object ranges over whole STACKS, so a stage of any
  width transports as itself — products stay flat.
- A **resource** is a threaded wire, and it is a model of the Doctrine —
  so it is written as one: `model Log in Doctrine = Str`, told from
  every other `model` head by its body being a stack. `with R` is
  transport into it; the routing is inferred, so a word that calls a
  resource word carries the label with no header at all.
- `Code` as data, with reflection (`getCode`, `typeOfCode`, `declOf`)
  and user-written functors: `functor F = <graph morphism>` takes one
  image per generator, `Fn⟨Stage ⇒ Code⟩`, and is functorial by the
  universal property. Its extension is a word, so `lift2 [F]` applies
  the same functor at run time.
- Every keyword is a **declaration word** beneath: `def f = body` is
  `[body] "f" defW`, and `defW : Code Str =Dict> •` says in its arrow
  what it does. The table is open, and a program may declare too
  (`examples/dictionary.braid`).
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

One Haskell module for the checker, interpreter, and REPL, a 1233-case test suite that runs
every example, and design notes recording each
decision. Not yet present: labelled record fields, totality checking
(`Recursive` records that a word may not terminate; it does not prove
that others do), a handler *construct* (a handler is an ordinary word —
`examples/resources.braid` writes one), and a `World` wire you can
name: `IO`'s carrier is declared abstract and linear, but there is one
of it, it is ambient, and the elaborator never writes it.

The documentation needs a cleanup pass. It was written stage by stage
and uses terms it never defines for a reader (`spine`, `stage`,
`receipt`, `K-word`, `carrier`, and others). Until that pass is done,
`MANUAL.md` is accurate but not always self-explanatory.
