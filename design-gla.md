# Linear maps as a theory — the GLA stage

*2026-09-21. Stage 9 of the macro arc. The record for
`examples/linear.braid`. Its neighbours: `design-exponents.md` (the
VECTOR half — bundles, `Aⁿ`, the N-family), `MANUAL.md` §8 (the
Doctrine, the level table), `READING.md` "Matrices as a PROP".*

Graphical linear algebra arrived in the plan as a *type* problem — how
do you index a matrix by its dimensions? — and shipped as a *doctrine*
problem. The finding of the stage is that the dimensions were never the
hard part.

## 1. The carrier is STACK-SHAPED, and width-indexed was wrong

The 2026-09-18 spec wanted

```braid
data Mat(a, b) = Fn⟨Int^a ⇒ Int^b⟩          -- a, b WIDTHS
```

It does not declare: `data` takes no width parameters, and a
constructor argument cannot be width-kinded. That is the surface
reason, and it is the smaller one.

The real reason is that a **width-indexed hom-object forces width
arithmetic**. The PROP's generators are tiny — copy 1→2, add 2→1, zero
0→1, discard 1→0 — and everything else is built by composition *and
tensor*. Tensor at widths is

```text
tensor : k(a, b) k(c, d) ⇒ k(a+c, b+d)
```

two variables **added**, which is exactly the level-2 algebra
`design-exponents.md` defers, and which the syntax cannot even write
(`a^(n+m)` is refused). So the width-indexed carrier does not fail at
the declaration and then work; it fails at the declaration *because* it
would have failed at the tensor.

Over **stacks** the tensor is concatenation, which is free, because
stacks are flat and `k(ρ, σ)` already names a whole side of a diagram.
7a did the work when it moved the Doctrine to stacks: the pairing
parameter and the strength `first` went then, for the same reason.

```braid
data Mat(a..., b...) = Fn⟨a ⇒ b⟩ Fn⟨b ⇒ a⟩ Code
```

## 2. `in Doctrine` is not optional, and it is a CLAIM

A theory may declare a constructor parameter `k(..., ...)` and a
`compose` at exactly the Doctrine's shape and still have **no carrier**.
`transportOf` returns a transport only when `thIn th == Just
"Doctrine"`; without the clause, `def m in Dense = …` is refused with

```text
`in Dense` names a model of GLA in the base: it has no carrier to
build — write `with Dense`, or `in GLA` for a template.
```

which names two fixes and neither is the one wanted. This is 2026-09-13
working as designed — membership is *declared*, never detected from a
shape — but it is worth writing down, because a theory whose slots
already look like the Doctrine's is exactly where the omission is
easiest to make.

## 3. No TOTAL `embed` — and that is the whole guarantee

The Doctrine's `embed : Fn⟨a ⇒ b⟩ ⇒ k(a, b)` asserts an
identity-on-objects functor from the **whole base**. For linear maps
that assertion is false, and a theory that declares `embed` anyway
makes `embed [fsin]` a linear map.

`GLA` declares `compose` and not `embed`. That is the upper row of §8's
level table, and it licenses exactly what it should: morphisms built by
hand under `in Dense`, and a refusal for `with Dense`:

```text
`with Dense`: theory GLA takes Doctrine's `compose` and not its
`embed` (`Fn⟨ρ ⇒ σ⟩ ⇒ k(ρ, σ)`): `with Dense` cannot transport a base
stage; `in Dense` and compose by hand.
```

The consequence that matters: a def written under `in Dense` can name
only GLA's slots, and those slots ARE the generators of the PROP of
matrices (Bonchi–Sobociński–Zanasi: a comonoid, a monoid, the symmetry,
the scalars). **Everything nameable is linear by scope.** The runtime
fold `examples/transpose.braid` calls `linear?` — which walks reflected
code asking whether every atom is one of `dup`, `+`, `swap`, `_` — has
no question left to ask, because the scope answered it before the code
existed.

The price is the one the table names: composition is a **word**,
`f g ; compose`, not `;`. `;`-as-composition is what a `with` scope
writes out, and a `with` scope embeds every stage. §7 is how that price
is paid back without giving the guarantee up: `embed` defined on a
SUBCATEGORY, which is partial, and the partiality is the same guarantee
said a second way.

The honest caveat is the one `examples/circuits.braid` already ends on:
a model seals the **category**, not the **type**. `Mat` is an ordinary
constructor and Braid has no export lists, so `[fsin] [fsin] c ; Mat`
builds a carrier from outside the vocabulary. Sealing the type is a
separate, unshipped question.

## 4. Transposition needs the DUAL, not the `Code`

The spec said the carrier's `Code` component is what makes `tr`
possible: transposing a bare function means probing it at basis
vectors, which is an anamorphism, and erasure forbids anamorphisms —
so `tr` was to dualize the `Code` (the comonoid/monoid exchange) and
**rebuild** the function.

**The first half holds and the second does not.** `evalAs` is the only
road from `Code` back to `Fn`, and it takes a **witness**: a value
whose arrow the loaded code must meet. For `tr : k(a, b) ⇒ k(b, a)`
that witness is an `Fn⟨b ⇒ a⟩` — which is precisely the thing being
built. Nothing in scope has that type, and written out the model is
refused at the slot:

```text
model Dense: slot 'tr' is Mat(•, List(a0)) ⇒ Mat(•, List(a0)) but
theory GLA declares Mat(ρ0, ρ1) ⇒ Mat(ρ1, ρ0)
```

So the anamorphism argument is right about *functions* and does not
rescue *code*: the two roads are blocked by the same wall, once as
"nothing tells the runtime how big" and once as "nothing hands `evalAs`
a witness".

What `tr` needs is the **dual function, carried beside the map**: a
linear map here is a map *with a chosen adjoint*, which is Elliott's
representation of linear maps in the AD paper (READING). `tr` is then a
projection — it swaps the two halves — and `tr ; tr = id` and
contravariance hold *by construction* rather than by computation, which
is the stronger position anyway.

**The `Code` stays, for a job it does better.** It is the **diagram**,
and `sameCodeC` decides equations on it. Four laws are therefore
PROVED rather than sampled:

| law | how |
|---|---|
| `tr ; tr = id` | `sameCodeC` on the diagrams |
| `compose ; tr = (tr, tr) swapped ; compose` | `sameCodeC` |
| `Δᵀ = ∇` (`copy ; tr = add`) | `sameCodeC` |
| `zeroᵀ = discard` | `sameCodeC` |
| the bialgebra corollaries, the scalar's self-duality | **sampled** through `app` |

The split is not an accident of the implementation. The transposition
laws are statements about ONE diagram read backwards, and a normalizer
decides those. A bialgebra law relates TWO DIFFERENT diagrams that
denote the same matrix — that is what makes it a law and not a
definition — and no normalizer decides that.

## 5. Only one whiskering is spellable

A stack parameter may sit only in tail position. So

```braid
under : k(a, b) ⇒ k(c a, c b)      -- declares
over  : k(a, b) ⇒ k(a c, b c)      -- The stack parameter 'a' must be
                                   -- the last thing in its stack
```

A generator can be given wires riding **below** it and never above.
Where the theory declares `embed`, this costs nothing: `prob.braid`
builds `flip ⊗ flip` as `embed [swap] ; under flip ; embed [swap] ;
under flip`, taking the symmetry from the base at whatever width the
stage needs. **A theory with no `embed` has no such recourse.** `GLA`
declares the symmetry as a generator, but only at
`k(Float Float, Float Float)`, and widening *that* needs the whiskering
that does not exist.

So the monoidal product `m ⊗ n` is **not constructible from a theory's
own slots**, and the bialgebra law proper —
`∇ ; Δ = (Δ ⊗ Δ) ; (1 ⊗ σ ⊗ 1) ; (∇ ⊗ ∇)` — cannot be stated, because
it needs `copy ⊗ copy`. What ships is its unit, counit and scalar
corollaries, each reachable with `under` alone:

```braid
copy (discard ; under) ; compose   = scale 1.0     -- the counit
(zero ; under) add ; compose       = scale 1.0     -- the unit
copy add ; compose                 = scale 2.0     -- Δ∇ = 2
```

This is a real limit of the stack-shaped hom-object and it is the one
thing the stack shape cost. It is the right trade — width arithmetic
would have cost more, and cost it everywhere — but it should be on the
record, because "tensor is concatenation, free" is true of the BASE and
not of a theory's own generators.

## 6. Two smaller decisions

**The element type is `Float` outright, not a carrier parameter.** A
parametric GLA is the more general theory and it is unwritable for the
reason `examples/theories.braid` states at the top: a law over a
parametric theory cannot invent a value of the parameter, and every
sampled law needs a literal. It would need a `sample : • ⇒ e` slot, and
its generators would still be at one wire each — the generality bought
would be a renaming.

**`zero` and `discard` ship in v1.** They complete the comonoid and the
monoid, and plain composition does not need them — but the *laws* do:
the counit law names `discard` and the unit law names `zero`, and those
two are the only bialgebra content reachable without the tensor. A v1
without them would ship a presentation whose laws are all about
transposition.

**A scalar has no one-stage base spelling, and that is the affine trap
in miniature.** `_ 2.0 ; fmul` is TWO stages: a constant (`• ⇒ Float`,
not linear) and a multiplication (`Float Float ⇒ Float`, not linear in
both arguments). Reversing two stages does not transpose them, so the
scalar's diagram is one stage that NAMES the generator and carries its
value, `scale 2.0`. The price is paid in the open: `sameCodeC` refuses
any diagram containing it (*`scale` has no closed arity*), which is why
every scalar law samples. The same fact is what makes a bare Float
literal dangerous in a subcategory reader — see below.

## 7. `embed` on a SUBCATEGORY — shipped the same day

`;` becoming composition needs `embed`, and `embed` from the whole base
is false. What is true is a **wide subcategory** `B_lin ⊆ B` and a
functor `B_lin → K`, so `embed` is **partial and the partiality is the
guarantee**. A wide subcategory is determined by a set of generators
closed under composition; the base is presented, so "is this program in
the subcategory" reduces to "is every atom in the generator set" — a
syntactic scan, decidable. `linear?` does exactly that at run time and
answers with a Bool; this does it at elaboration and answers with a
refusal.

```braid
theory GLA(k(..., ...)) in Doctrine =
    compose : k(a, b) k(b, c) ⇒ k(a, c)
    copy    : • ⇒ k(Float, Float Float) = dup
    add     : • ⇒ k(Float Float, Float) = fadd
    under   : k(a, b) ⇒ k(c a, c b)     = _

def f with Dense = dup ; fadd        # Float =Dense> Float
```

### The mechanism is a model read backwards

The spellings ARE a model of the theory in the base (`copy ↦ dup`,
`add ↦ fadd`), whose image is `B_lin`. The table is injective on
generators — checked where it is written — so it has a partial inverse
`read : B ⇀ B[GLA]`, undefined off the table, and `embed_Dense` is
`read` then `Dense`. Not new machinery: one table used as a **parser**
composed with another used as an **interpreter**, and the universal
property does the rest, since a functor out of a free category IS a
graph morphism.

### The decision: the table is the THEORY's

The lead left this open with three candidates: (a) a reference model of
the theory in the base, named at the scope (`with Dense via Funcs`);
(b) the theory declares each slot's base spelling; (c) something else.

**(b), and the argument is about what `B_lin` IS.** Which base programs
are linear is a property of the **presentation** — it is the set of
generators, and the generators are what a theory declares. Two models of
one theory are two *interpretations* of the same subcategory; letting
either of them define it would let them disagree, and there would be no
answer to "is `dup ; fadd` linear?" without naming a model first, which
is exactly the wrong shape of question.

Two smaller reasons, each decisive on its own:

- **A model's slot bodies are PROGRAMS, not atoms.** `copyA = [dup] ;
  Arr` is a carrier-builder; inverting it means reaching inside a
  quotation inside a constructor application and hoping there is one
  atom in there. There is nothing to invert in the general case, and the
  cases where there is are an accident of how the model was written. A
  spelling beside the signature is a table because it is declared to be
  one.
- **It answers the "several models" question by construction.** With the
  table on the theory, `read` is shared and `embed_M = read ; M` for
  every model M — which is the statement that all of them agree about
  the subcategory and differ only about what its morphisms mean. With
  the table on a model, every scope would have to name two models and
  the reader would be a second axis of choice with nothing to constrain
  it.

The surface is the one the lead proposed, `slot : Σ ⇒ Θ = word`, split
on ` = ` with spaces because `=` without them is part of a labelled
arrow (`=IO>`).

### Atom-wise transport is a MODE, not a parameterization

`runTransport` splits the body into STAGES and sends each to `embed
[stage]`; the stage is opaque. A reader must send `dup ; fadd` to `copy
add ; compose`, which means looking INSIDE the stage. So `readTransport`
is a sibling clause of `runTransport` rather than an argument to it: the
two share the composition, the exit refusal, the K-word table and the
`_`-padding that slides an accumulated carrier underneath, and differ in
exactly one function — what one stage becomes. That is 60 lines, and the
shared part is the reason it is not more.

A stage a reader can transport is `_`\* followed by exactly one
generator: the `_`s are `under` and the generator is the carrier they
ride beneath. Two generators side by side is their TENSOR, and §5 says
there is nothing to send it to.

### The affine trap, pinned at the declaration

If a Float literal were a generator, `x ; 1.0 ; fadd` would be admitted,
and that map is AFFINE. It is refused, and **not by a special case**: a
base spelling is accepted only on a slot that builds a carrier out of
nothing or whiskers one, and a scalar (`scale : Float ⇒ k(Float,
Float)`) is neither — it takes a base wire, so it is one generator per
*value* and no one word spells it (§6). So no literal can enter the
table, and a literal inside a transported scope meets the ordinary *no
image* refusal with a message that names the trap.

The cost is honest and worth writing down: **a transported program
cannot scale.** `two`, `fan` and every scalar law in
`examples/linear.braid` are hand-built for that reason. Admitting
scalars would need a multi-stage pattern in the reader (`_ <lit> ;
fmul`), which is a different mechanism — the reader is a graph morphism
on ATOMS, and a scalar is not one.

### Sound, incomplete, and said out loud

`with Dense` accepts only programs built from the theory's generators,
every one of which is in the subcategory; it rejects programs that are
in the subcategory but spelled with an atom off the table; it never
accepts one that is not. The criterion is a **sufficient condition, not
a decision procedure**, and MANUAL §8 and §14 both say so — the
direction that costs something when it is wrong is the one this cannot
get wrong.
