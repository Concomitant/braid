# Quick guide: open-arity words

Some words don't have a fixed number of inputs. Their input type has an
**open region** — a stack tail `ρ` (any wires at all) or an exponent
`aⁿ` (any number of `a`s) — and they work at every width:

```text
pass    : ρ ⇒ ρ                          thread everything
forget  : ρ ⇒ •                          destroy everything (terminal)
mapN    : Fn⟨a ⇒ b⟩ aⁿ ⇒ bⁿ              map across a bundle
apply   : Fn⟨ρ₀ ⇒ ρ₁⟩ ρ₀ ⇒ ρ₁            run a quotation on the segment
loop    : Fn⟨Σ ⇒ (Σ|Θ)⟩ Σ ⇒ Θ            Elgot iteration on the segment
foldExp : Fn⟨b a ⇒ b⟩ b aⁿ ⇒ b           fold a bundle, one wire at a time
foldExp2: Fn⟨b a c ⇒ b⟩ b (a c)ⁿ ⇒ b     fold a bundle of pairs
dupN    : aⁿ ⇒ aⁿ aⁿ                     copy a bundle
mapN2   : Fn⟨a b ⇒ c⟩ (a b)ⁿ ⇒ cⁿ        map across a PAIR bundle
zipN    : aⁿ bⁿ ⇒ (a b)ⁿ                 interleave two bundles
unzipN  : (a b)ⁿ ⇒ aⁿ bⁿ                 de-interleave
at      : Fin(n) aⁿ ⇒ a                  index a bundle (0 = deepest)
indicesN: aⁿ ⇒ (Fin(n) a)ⁿ               tag each wire with its index
```

`mapN`/`mapN2` are the lifters: with `zipN` they turn any one- or
two-wire word into its pointwise bundle version, which is why `addN`,
`scaleN`, `mulN` and `subN` are prelude defs rather than primitives
(`def addN = zipN >> [+] ... >> mapN2`).

`at` and `indicesN` are the index words: `Aⁿ` *is* the function space
`Fin(n) ⇒ A` stored flat, and a `Fin(n)` is an index into it. Indices
are **born of a bundle** — `indicesN` tags each wire of a live segment
with its own index, and `checkedAt` earns one by testing an `Int`
against the segment actually there (hit track = in range). The only
other source is an index literal (`fin0`, `fin1`, …), whose offset is
its own proof. Nothing conjures an index from nothing, for the same
reason nothing conjures a bundle (Rule 4).

Derived open words (ordinary prelude defs — openness is inherited):
`sumN : Intⁿ ⇒ Int`, `decide : a ((•|•) a)ⁿ ⇒ a`, `firstTrue`, `while`,
`until`. **Any def you write whose inferred input ends open is itself
an open word** — `def total = [+] 0 ... >> foldExp` is `Intⁿ ⇒ Int`
and runs at every width through one body.

## Rule 1 — open words go LAST in their stage

An open-arity atom must be the **final atom** of its tensor stage
(equivalently: the last thing before the newline/`>>`). In final
position it receives *the whole remaining stack* as its segment — at
runtime, the segment's actual width is what stands in for the erased
`ρ`/`n` (there is no width tag anywhere; the stack is the witness).

In any **non-final** position the open region is *closed instead*
(`ρ := •`, `n := 0`) — the word shrinks to its zero-width case, and the
checker holds you to it:

```braid
1 2 >> forget          # • — final forget got everything
1 2 >> forget 5        # STATIC ERROR: Cannot unify stacks: Int Int vs •
                       # non-final forget closed to • ⇒ • — it covers
                       # nothing, so the 1 2 are left uncovered
```

If an open word type-errors with `… vs •`, this rule is almost always
why: it isn't last in its stage, so it was closed.

## Rule 2 — fixed arguments go UNDERNEATH; `...` puts them there

Every open word takes its fixed arguments *below* the open bundle:
step and seed for the folds, the scalar for `scaleN`, the quotation for
`apply`/`loop`. When the bundle is already on the stack, you get the
fixed arguments underneath with the remainder marker — **`X ...`
pushes X at the BOTTOM and threads everything else on top**:

```braid
1 2 3                      # the bundle: Int³
[+] 0 ... >> foldExp       # step and seed slide UNDER it → 6
2 ... >> scaleN            # scalar under the bundle → 2 4 6
```

This is the same `...` as ever (explicit remainder); nothing special
happens for open words — the layout just always works out to "fixed
args at the bottom via `...`, bundle on top, open word last."

Corollary: a whole ladder can *accumulate* by ending every line with
`...` — each line's pushes go under the pile — and one open word folds
at the end (`examples/ladder.braid`, the `decide` form).

## Rule 3 — `_` passes one wire; `...` passes the rest

Both are explicit-remainder spellings. Use `_` when exactly one wire
rides through (`_ 10 >> div`), `...` when an unknown pile does
(`1 ... >> +`). Open words interact with `...`; they don't need `_`.

## Rule 4 — what erasure forbids

The width `n` exists only in types. Consequences:

- **No output-only exponents.** `zeroN : • ⇒ Intⁿ` is untypable in
  spirit: nothing at runtime says how many zeros. Bundles are consumed
  or transformed, never conjured (produce them with literal pushes).
- **You can't branch on width.** There is no `empty?` for a bundle —
  elimination is the fold, which handles every width uniformly
  (`foldExp` at `n = 0` just returns the seed).
- **One open region per input.** `aⁿ bⁿ` (same `n`) is fine; two
  *independent* open regions are ambiguous and rejected.

## Rule 5 — binders close their input

`(x -> body)` and `x ->` bodies are **input-closed**: all input arrives
through the parameters. So a binder cannot take one wire off the top
and leave an open bundle flowing underneath — if you need "grab the
top, keep the bundle open," put the wire you want DEEPEST instead and
let the fold's seed take it, as `firstTrue` does — its default is the
first argument for exactly this reason.

## Worked micro-examples

```braid
1 2 3 4 >> sumN                            # 10       (n = 4)
sumN                                       # 0        (n = 0: seed)
1 2 3 >> dupN >> addN                      # 2 4 6    (copy, pointwise add)
1 2 3 10 20 30 >> zipN                     # 1 10 2 20 3 30
def dot = zipN ; [(acc a b -> (a b ; *) acc ; +)] 0 ... ; foldExp2
1 2 3 4 5 6 >> dot                         # 32, and dot : Intⁿ Intⁿ ⇒ Int
```
