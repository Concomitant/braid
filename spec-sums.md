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
  type grammar. A newline is a strict `>>` and does **not** absorb around
  `|` or `>>`: a line is a complete row, and rows stack by newline. This
  is what makes aligned track-columns work bare — a trailing `|` (empty
  arm = `pass`) at a line's end and a leading `|` at the next line's
  start are two rows, not a collided `| |`. Continuation-absorption
  survives only for operators a newline cannot express: the railway ops
  `>=>`/`>?>`/`>!>` and the `||` list-literal, which may span lines.
  * The fish is *not* a separate composition — it is `>>` plus a lift:
    `t1 >=> t2 ≡ t1 >> (t2 | in2) >> merge` (dually `>?>` uses `(in1 |
    t2)`, `>!>` uses `(pass | t2)`), all the shape `t1 >> (a|b) >>
    merge` with the stage on one track and a default injector on the
    other. So a railway *already* decomposes into a plain newline-`>>`
    stack of rows — `even?` ⏎ `(g | in2) >> merge` ⏎ … — with no
    absorption. `>=>` keeps its line-spanning as a deliberate terseness
    sugar that bundles the `>>` and the lift into one infix token; the
    row form is always available when you'd rather stay purely `>>`.
* `merge : (Θ | Θ) ⇒ Θ` is the binary codiagonal ∇ (dual of `dup`),
  rejoining agreeing tracks.
* **The decision tree is a right-nested sum.** Deferred routers stack:
  each answers its track and passes the rest down (`(handle | pass)`
  then `(pass | route)`), so the leftover sum grows to the right —
  `(A | (B | (C | …)))`, the branch structure written in the type. Two
  structural tools tame it:
  * `assocL : (A | (B | C)) ⇒ ((A | B) | C)` and `assocR` (its inverse)
    re-nest the tree — pure `in1`/`in2`/`merge` rewiring, no data
    touched. With `not` (the sum braiding) they let you rebalance a
    tree before eliminating it. (Both carry open row tails from the
    injections; they are isos up to that openness.)
  * `case(b1, …, bn)` is the **coproduct eliminator**: one handler per
    nested track, each a bare program, all landing on a common result.
    Parse sugar for the nested rows —
    `case(a, b, c) ≡ (a | (b | c) >> merge) >> merge` — so it is to a
    sum what a generated `foldName` is to a data type: it folds the
    whole `(·|·)` spine in one stage instead of unwinding by hand with
    N `merge`s. Branches are spliced bare (like the `>=>` lift), so no
    quoting or `apply` — the handlers may have *different* domains as
    long as they agree on the result.

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

### Verdicts, when you really want them

The naming convention makes the choice one character: **`p?` routes
and keeps** (`eq?`, `less?`, `odd?` — data flows on), **bare `p`
forgets and answers `Bool`** (`equals`, `less`, `odd` — implicitly
`>> verdict`). A Bool then drives a choice through an ordinary row:
`odd >> (1 | 0) >> merge`.

Routers keep their payloads because kept data costs one word to drop
and dropped data is gone. When only the decision matters, `verdict`
(prelude) collapses any router's payloads generically:

```text
forget : ∀ρ. ρ ⇒ •                  -- the terminal morphism (primitive)
def verdict = (forget | forget)      -- (Δ₁ | Δ₂) ⇒ (• | •)

eq? >> verdict : a a ⇒ (• | •)
```

`forget` is the segment-wide terminal map every cartesian category
guarantees (`drop` is its single-wire case). Without it, collapsing a
payload was an arity-indexed family (`drop`, `drop drop`, …) — the
caseN disease again; with it, one polymorphic def covers all routers.

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

### Leading `|`: identity default

A code row may begin with `|`, defaulting its first alternative to
identity (`pass`): `(| f)` ≡ `(pass | f)`, `(| f | g)` ≡
`(pass | f | g)`; symmetrically a trailing `|` defaults the LAST arm
(`(f |)` ≡ `(f | pass)`). Useful for the common "keep one track, transform the
other" conditional — `router >> (| f) >> merge` passes the hit track
and applies `f` to the miss — and it lets a vertical row put every arm
on its own `|`-led line.

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

* **return** = `in1`, alias `ok` — injection into the hit track.
* `in2` has the alias `miss` — stay on the miss track.
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
def process = even? >=> _ 100 >> less >=> double >> ok
```

reads as three stages — test even, test below 100, double-and-succeed
— with the failure track threaded invisibly past every stage. The
final `>> ok` is `return`, lifting the pure stage into the monad.
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

## 6d. The list monad, derived

With one new primitive (`cons : a List a ⇒ List a` — lists could be
consumed but never built) the list monad is prelude-level user code:

```text
def single  = _ list() >> cons                    -- return
def concat  = [append] list() ... >> fold          -- join
def flatMap = map >> concat                        -- bind
def filter  = (p -> [p ... >> apply >>
                (single | drop >> list()) >> merge]) ... >> flatMap
```

`filter` is the monad in action: each element maps to a singleton or
the empty list, and join flattens — order-preserving, no reverse
tricks. Its type came out more general than asked:
`filter : Fn⟨a ⇒ (b | c)⟩ List a ⇒ List b` — asymmetric routers
filter and transform in one pass. `append`/`reverse` are fold/cons
exercises. Note List is the free monoid: `[append] list() ... >> fold`
and `[+] 0 ... >> fold` are the same generic reduction applied to two
Monoid instances — the dictionary is just wires.

## 6e. User data types are initial models

`type Nat = (• | Nat)` and friends close the categorical loop: a
recursive declaration is the initial algebra of a row functor, the
`Name`/`unName` coercions are the algebra isomorphism, and `unName`
output is a sum wire — data-type elimination IS the control-flow
machinery of this chapter. Each declaration also generates `foldName`,
the catamorphism: elimination by points (`[case1] [case2] ... >>
foldName`, recursive slots pre-folded), with hand recursion through
`unName` for everything else.

## 6f. Guards as a fold over data (matchWith)

The `if`/`elif`/`otherwise`/`endif` machine bakes the clause chain into
primitives with static totality — but its fold threads a fresh
done/continue split per clause, which currently mis-instantiates when
the done-type differs from the continue-type across ≥2 interior
clauses (a real limitation; homogeneous chains are fine). The
list-fold alternative sidesteps it entirely: a clause list
`List(Fn⟨A ⇒ (A|A)⟩ Fn⟨A ⇒ B⟩)` — each element a `[router] [action]`
two-wire pair (multi-wire list literals, cf. `List(A B)`) — folded by

```text
def matchWith = (x default clauses ->
  clauses >> [x >> default ... >> apply]
             [(rest p f -> x >> p ... >> apply
                >> (f ... >> apply | drop >> rest) >> merge)]
          ... >> foldList)
```

`foldList` is a right fold, so the head clause is checked first
(first-match); the accumulator is one fixed monomorphic type `B`, so
there is no per-clause instantiation and no bug. The trade: totality
becomes dynamic (the `default` supplies the fall-through the
`otherwise`-clause made static). Because clauses are *data*, they can
be built, filtered, and reordered like any list — control flow you can
compute. See examples/match.braid (FizzBuzz).

## 6g. Guards as `||` clause-products

A guard is a **product** of lanes, not a coproduct: to probe each
predicate you need all n lanes present at once. So it is written with a
distinct delimiter `||` (leaving `|` entirely for sums), which reads as
"or" — first-true-wins is short-circuit or.

`|| e1 || e2 || e3` is a **vertical list literal** — the same value as
`list(e1, e2, e3)`, each element an arbitrary bracketed program, so
`||`-lists compose with `map`/`fold` like any list. For guards, each
lane is `[router] [action]`, and the value has type
`List(Fn⟨A ⇒ (A|A)⟩ Fn⟨A ⇒ B⟩)` — a first-class value that
type-checks alone and can be bound, passed, and reused.

`choose : A List(Fn⟨A⇒(A|A)⟩ Fn⟨A⇒B⟩) ⇒ (B | A)` folds the product,
running the first lane whose router hits (`in1(result)`), or `in2(input)`
if none. `else? = in1` is the always-hit router — a final
`|| [else?] [d]` lane makes the guard total. No dependent types (a
product is a plain List); `|` is untouched. See examples/fizzbuzz.braid,
examples/guards.braid.

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
* The `if`/`elif`/`otherwise`/`endif` primitive guard machine →
  superseded by `matchWith` (guards as a fold over a clause list, §6f)
  plus `cond`/rows. Cut because: `if` name-squatted on a guard-state
  initializer of type `ρ ⇒ (Θ | ρ)` (a phantom done-track); the fold
  mis-instantiated heterogeneous done/continue types across ≥2 interior
  clauses (never fixed); and every use case had a better home. Its one
  real loss — static chain-totality via the `()`-typed miss track —
  survives in spirit: rows remain statically total (every track must
  be covered), and matchWith's `default` is the dynamic residue.
