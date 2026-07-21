# Sums and Control Flow

The consolidated design for sum types and everything built from them.
Extends `expanded-spec.md` and `spec-update-exponentials.md`; supersedes
the intermediate designs recorded in git history (branch, case/caseN,
guard, clause/finish, mergeN — see "History of cuts" at the end).

The central discovery of this chapter: **sums of stacks are a single
mechanism** that yields conditionals, data types, guards, pattern
matching, and loops. Nothing else was needed.

## 1. The type

A sum of stacks occupies **one wire** and carries a tagged bundle — one
of several alternative wire-rows:

```text
(Δ₁ | Δ₂ | … | Δₙ [| σ])
```

* Alternatives are whole stacks (multi-wire payloads are native — no
  Pair needed to fail with two values).
* The row is **rigid and n-ary**: `A | B | C` is one 3-ary sum, written
  flat. Nesting exists only where parentheses were written, and it means
  something: a staged decision tree.
* `σ` is an **alternatives-row variable**, allowed only as the tail —
  the same discipline as stack variables, one level up.
* `Bool ≡ (• | •)`. The empty sum `()` is the initial object: no
  alternatives, no values.

### Why sums never flatten

If `(A | (B | C)) ≡ (A | B | C)` held definitionally, unification would
work modulo associativity of `|`, and most general unifiers vanish:

```text
(α | β) ~ (A | B | C)
```

has two incomparable solutions (`α:=A, β:=(B|C)` and `α:=(A|B), β:=C`),
and normal forms are not substitution-stable (`(α | C)` changes arity
when `α := (A|B)`). This is word unification over the free `|`-monoid:
satisfiability is decidable (Makanin), principal solutions do not exist.
It is exactly the disease the stack dimension excludes with the
tail-only rule. A language gets **one** definitional monoid — its
juxtaposition; stacks claimed it. Everything inside a wire (`Fn⟨…⟩`,
`List`, sums) is a rigid constructor, which is what keeps unification
first-order and inference principal.

The same argument rejects automatic distribution/factoring
(`A B | A C` vs `A (B | C)`): those isos are *programs* (`dist`,
`factor` — derivable from rows and injections), never type equalities.

### Row variables

`(Δ₁ | … | σ)`: unification is list-with-optional-tail over the
alternatives — decidable, principal, the stack unifier one level up.
Producers commit only to a prefix (`in2 : Δ ⇒ (Δ₁ | Δ | σ)`); consumers
widen or close the row. **Elimination closes**: matching against a
closed row pins `σ`, so missing cases are unification errors.

## 2. Introduction: injections

```text
here  : ∀Δ σ.  Δ ⇒ (Δ | σ)      -- start a sum: my segment, front track
there : ∀Δ σ. (σ) ⇒ (Δ | σ)     -- widen: new unknown track in front (tag+1)
inN   : ∀…  . Δ ⇒ (Δ₁ | … | Δ | σ)   -- flat spelling: inN ≡ here >> there^(n-1)
```

Injections are unary numerals (`here`/`there`) with a lexical flat
family (`in1`, `in2`, …) as sugar; tags are positional and stable under
tail-widening, so runtime representation is `tag + bundle` and widening
is free. Value display echoes the family: `in2(3, 4)`.

## 3. Elimination: code rows

The `|` that forms sum *types* also forms sum *programs*:

```text
(p₁ | p₂ [| ...]) : (Γ₁ | Γ₂ [| σ]) ⇒ (Δ₁ | Δ₂ [| σ])
```

A **code row** is the sum functor action: one component per alternative,
**exactly one runs** (chosen by the tag), re-tagged in place. It mirrors
juxtaposition exactly — spaces tensor (all run, side by side), bars
alternate (one runs, by tag) — and satisfies the matching functoriality
law `(f | g) >> (h | k) = (f >> h | g >> k)`.

* A 1-ary row **is** plain grouping: `(p)`.
* The trailing residual `| ...` is identity on the remaining
  alternatives (open row). `pass` is the blessed readable spelling of an
  identity *component*; `...` remains synonymous. The ellipsis thus
  means "identity on the unknown remainder" in **both** monoidal
  dimensions (stack tail, row tail).
* Precedence, loosest to tightest: newline (strict `>>`), then `|`, then
  `>>`, then juxtaposition — so **each line is a row**, mirroring the
  type grammar. Newlines adjacent to `|` are absorbed (continuation
  layout).
* `merge : (Θ | Θ) ⇒ Θ` is the binary codiagonal ∇ (dual of `dup`),
  rejoining agreeing tracks.

**The delay law.** Bare code is conditional only *inside a row* (a row
is the one context where exactly one component runs). Quoted code is
skippable anywhere. This law decides every syntax question below: bare
things ride rows; deferred things wear brackets. Conditionals need no
thunk ceremony because rows are wiring, not functions.

## 4. Routers: predicates route

A verdict-returning predicate (`odd? : Int ⇒ Bool`) severs the decision
from the value it describes; everything downstream is then machinery for
reattaching them. In a wire language the predicate should **route the
wire, keeping it**:

```text
odd?, even?, zero?, negative? : Int ⇒ (Int | Int)       -- hit = track 1
lt?  : Int Int ⇒ (Int Int | Int Int)
eq?  : ∀A. A A ⇒ (A A | A A)
uncons : List A ⇒ (• | A List A)                        -- asymmetric router
```

A **router** is any program into a sum; predicates are the symmetric
case, destructors like `uncons` the asymmetric case. If-then-else is
then pure existing machinery:

```text
odd? >> (dup >> * | 1 ... >> +) >> merge     -- if odd then square else increment
```

`true`/`false : • ⇒ (• | •)` remain as degenerate routers (decisions
about nothing). Quoted routers dispatch with plain `apply`.

## 5. Guards: if / elif / otherwise / endif

Haskell-style guards, with zero new grammar — four primitives named as
keywords, riding ordinary rows:

```text
7 >> if
... | [dup >> *]  odd?
elif
... | [drop >> 0] negative?
elif
... | [1 ... >> +] otherwise
endif
```

State is the two-track sum `(Θ | Σ)`: done-so-far, and the untested
residual. Every clause line has the identical shape
`... | [action] router` — done rides the `...`, the quoted action waits,
the bare router decides. **The router is the final atom of the clause
because it claims the whole residual segment — the remainder discipline
itself fixes the pair order.**

```text
if        : ∀Θ Σ.  Σ ⇒ (Θ | Σ)                                -- entry: all residual
elif      : ∀Θ Σₕ Σₘ. (Θ | Fn⟨Σₕ⇒Θ⟩ (Σₕ|Σₘ)) ⇒ (Θ | Σₘ)     -- fold one clause
otherwise : ∀Σ.  Σ ⇒ (Σ | ())                                 -- always-hit router
endif     : ∀Θ Σ. (Θ | Fn⟨Σ⇒Θ⟩ (Σ | ())) ⇒ Θ                  -- fold + close
```

* `elif` is **asymmetric** in the router's tracks, so destructuring
  clauses work: `... | [head-handler] uncons` — guards are also pattern
  matching.
* **Static totality.** `otherwise` is the coproduct-unit iso
  `Σ ≅ Σ + 0`: its miss track carries the empty sum `()`, which is
  uninhabited. `endif` *demands* that track, so a chain missing its
  otherwise-clause is a **type error at the endif line**. The dead
  branch in `endif` is the absurdity map `0 ⇒ Θ` — the unique morphism
  from the initial object, which is why it needs no runtime code.
  Partial guard chains are inexpressible (there is no bottom).

### Why no single n-ary case/merge primitive exists

The obvious alternative — `caseN`/`mergeN` families routing onto n flat
tracks and collapsing at the end — fails a counting theorem: "n−1
predicates ↔ n tracks" and "collapse all n tracks" are *length
correlations*, and row variables quantify over unknown rests but cannot
count. Arity-indexed primitive families are the only static answer, and
they are a smell. The guard machine avoids counting entirely by
**folding instead of collecting**: the state shape `(Θ | Σ)` is
constant, each `elif` merges its clause immediately, and no n ever
appears. (This also fixes clause ordering and enables the interleaved
layout.)

## 6. Loops: Elgot iteration

```text
loop : ∀Σ Θ. Fn⟨Σ ⇒ (Σ | Θ)⟩ Σ ⇒ Θ
```

The body is a router into `(continue | done)`: the continue track
re-enters with new state, the done track exits. While/until/
tail-recursion in one scheme, with exits written in the same router/row
vocabulary as everything else. Example (sum 1..n):

```text
0 5
[(a n -> n >> zero? >> ((z -> a >> in2) | (m -> (a m >> +) (m 1 >> -) >> in1)) >> merge)] ...
loop        -- ⇒ 15
```

`loop` is the language's honest entry point for nontermination — a body
that always continues diverges. (It is Elgot iteration; the traced/fix
story from the earlier spec remains derivable later.)

## 6b. Recursion

Definitions may reference themselves, typed by **monomorphic recursive
binding** (the name is bound at a fresh monomorphic arrow while its body
is inferred; the recursive uses share it; two constraints tie the knot;
generalization happens after — polymorphic recursion is not offered).
Runtime recursion is guarded by the delay law for free: a self-call
inside a row component runs only when that track is chosen.

Tail recursion makes the loop harness disappear — the self-call is
`again`, falling through is `done`:

```text
def until100 = lt100? >> (double >> until100 | _) >> merge
```

and tree recursion becomes writable at all:

```text
def fib = lt2? >> (_ | (n -> n >> decr >> fib >> _ (n 2 >> - >> fib) >> +)) >> merge
```

Placement rule: like segment-consuming primitives, a recursive call's
enclosing group must sit in **final position** in its stage — its output
width is unknown until the knot ties, and non-final operands are closed
at elaboration time.  (`… >> fib >> _ (… >> fib) >> +` — the second
call's group is final; the first call's result rides the `_`.)

The trade that keeps both forms: `loop` is constant-space by
construction (Elgot iteration is the tail-call-optimized closed form);
general recursion consumes stack. Sections with `_` (the hole, a
synonym for `id`) make the constant-operand predicates point-free:
`def lt100? = _ 100 >> lt? >> (_ drop | _ drop)`.

## 6c. The sum monad, officially

Routers are the Kleisli arrows of the sum monad `(· | E)`, and the
combinator vocabulary of sections 3–5 turns out to be its structure
maps in costume:

* **return** = `in1` — injection into the hit track.
* **fmap f** = `(f | ...)` — a code row is the functor action.
* **join** = `(... | in2) >> merge` — flatten one nested layer.
* **Kleisli composition** = the `and` idiom: `p >> (q | in2) >> merge`.

The surface operator `>=>` makes the last one first-class syntax:

```text
p >=> q       ≡       p >> (q | in2) >> merge
```

It is pure parse-time sugar — the desugaring happens before inference,
so there are no new typing rules and the monad laws follow from the
row/merge semantics already specified. Precedence sits between `|`
and `>>`, so a Kleisli stage is a whole `>>`-chain:

```text
def process = even? >=> _ 100 >> less >=> double >> in1
```

reads as three stages — test even, test below 100, double-and-succeed
— with the failure track threaded invisibly past every stage. The
final `>> in1` is `return`, lifting the pure stage into the monad.
Short-circuiting is structural: a stage on the miss track never runs.

**Why there is no do-notation.** Haskell's `do` exists to manage
names (`x <- p; q x`). Braid has no names to manage — data flows by
position — so the entire content of do-notation collapses into the
choice of composition operator. A "do-block" would just be a region
where sequencing means `>=>`; the operator by itself is the whole
feature.

**Scope.** The desugaring is binary: the miss track is one
alternative (`in2`). N-ary error rows compose with explicit rows
and injections — a parse-time desugar cannot know the row's arity.
Monad *polymorphism* (code generic over which monad, via constructor
variables of kind Stack → Stack) is explicitly deferred; the sum
monad's operations are wiring patterns, and it is not yet clear the
abstraction pays for its unification machinery.

## 7. The two-level pattern

A recurring law of this design: each concept has a **flat spelling**
(arity visible in the source) and a **polymorphic iterator** (one
scheme, n-arity by composition):

| flat family | iterator |
|---|---|
| `inN` | `here` / `there` |
| guard tables | `if` / `elif` / `endif` folds |

Families are lexical (schemes generated from the name, like integer
literals); iterators are ordinary schemes. Both compile to the same
tags.

## 8. History of cuts

Recorded so the git history reads sanely:

* `branch` (thunk-based conditional) → subsumed by code rows
  (`choose = (c t e -> c >> (t | e) >> merge)`).
* `case` (promote quoted test) → subsumed by routers + `apply`.
* `caseN`/`mergeN` families → rejected by the counting theorem.
* `guard` (test-and-shift step) → superseded by `clause`.
* `clause`/`finish` (two-quote guard machine) → superseded by the
  router-based `if`/`elif`/`otherwise`/`endif`.
* Verdict predicates (`Int ⇒ Bool`) → routers.
