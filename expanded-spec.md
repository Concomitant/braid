# Handoff: Cartesian concatenative string-diagram language prototype

## Core idea

Build a small strongly typed concatenative language where programs are typed stack transformers:

```text
Γ ⇒ Δ
```

`Γ` and `Δ` are stack shapes: ordered products of values. Product is native stack concatenation, not nested tuple construction. This avoids `(A,(B,C))` vs `((A,B),C)` coherence problems.

The language is best understood as textual syntax for cartesian string diagrams.

## Core syntax

Horizontal composition / tensor:

```text
f g h
```

Means block-split tensor:

```text
f ⊗ g ⊗ h
```

If:

```text
f : A ⇒ B
g : C ⇒ D
h : E F ⇒ G
```

then:

```text
f g h : A C E F ⇒ B D G
```

Each term consumes a contiguous input block.

Sequential composition:

```text
f >> g
```

or newline.

If:

```text
f : Γ ⇒ Δ
g : Δ ⇒ Θ
```

then:

```text
f >> g : Γ ⇒ Θ
```

A program is therefore a sequence of tensor stages.

## Required core primitives

Cartesian structural basis:

```text
id   : ∀A. A ⇒ A
swap : ∀A B. A B ⇒ B A
dup  : ∀A. A ⇒ A A
drop : ∀A. A ⇒ •
```

Signatures are exact: an operation consumes and produces precisely the wires written, and constants source from `•`. Nothing carries an implicit remainder — passing wires through is always explicit (`pass` / `...` / `>>>`, or `id` per known wire). When a stack variable does appear in a scheme (`pass`'s ρ, `apply`'s Γ), it is always the rightmost tail; see "Remainder discipline" for why.

Stack identity / remainder passthrough:

```text
pass : ∀ρ. ρ ⇒ ρ
```

`pass` is not a separate categorical primitive; it is identity on an unknown remainder stack. It is only legal as the final atom of a tensor chain (or as a whole stage by itself).

Empty stack:

```text
•
```

is the tensor/product unit and terminal object.

## Surface sugar

Trailing remainder marker:

```text
...
```

desugars to appending `pass` at the end of the current tensor chain.

Example:

```text
f h g ...
```

desugars to:

```text
f h g pass
```

Boundary operator:

```text
>>>
```

means: append `pass` to the immediately preceding tensor stage, then sequence.

Example:

```text
1 2 3 4 5 6 >> f h g >>> +
```

desugars to:

```text
1 2 3 4 5 6 >> f h g pass >> +
```

Here `f`, `h`, `g` sit under wires 1–3 and consume the values `1 2 3`; `pass` carries `4 5 6`. Tensor atoms align with wires left to right, so each line reads as a vertical slice of the string diagram.

`>>>` opens only the immediately preceding tensor stage, never the accumulated program:

```text
a >> b >>> c   ≡   a >> (b pass) >> c
               ≢   ((a >> b) pass) >> c
```

Newline is strict `>>`, not implicit `pass`.

## Remainder discipline and principal typing

### Stack shape invariant

Every stack type, declared or inferred, has one of two shapes:

```text
T1 … Tn ρ    (open: one stack variable, always in final position)
T1 … Tn      (closed)
```

At most one stack variable per stack, and only ever as the rightmost tail. Stack unification is then plain list unification with an optional tail variable — decidable, with most general unifiers, so inference stays HM-principal.

### Instantiation rule for tensor chains

In a tensor chain `t1 t2 … tn` (atoms aligned with wires left to right):

```text
ti : Γi ⇒ Δi          (i < n: instantiated with ρ := •, closed)
tn : Γn ρ ⇒ Δn ρ      (may retain its scheme's remainder; Γn, Δn closed)
------------------------------------------------------------------
t1 … tn : Γ1 … Γn ρ ⇒ Δ1 … Δn ρ
```

Only the final atom may be open; every earlier atom has its stack variable instantiated to `•`. The result again satisfies the invariant.

Since operations are exact, ρ-retention matters only for `pass` (hence `...`/`>>>`) and for the segment variables of higher-order eliminators (`apply`, `branch`) in final position. A bare `+` requires the stack to be exactly two wires wide; on a deeper stack write `+ ...`.

Operational reading: a stage consumes the leftmost `k` wires, where `k` is the sum of its atoms' closed input arities. If the stage is open (it ends in `pass` / `...`, or its final atom is a segment-consuming eliminator), all wires to the right flow through (or into the segment). If it is closed, the incoming stack must be exactly `k` wires wide.

### Why the variable may only be the tail

A `pass` (or retained `ρ`) anywhere but final position puts a stack variable to the left of concrete types. Unification then loses most general unifiers:

```text
ρ Int  ~  Int σ
```

is solved by `ρ := •, σ := •`, by `ρ := Int, σ := Int`, by `ρ := Int Int, σ := Int Int`, … — infinitely many, pairwise incomparable. This is word unification over a free monoid: satisfiability is decidable (Makanin), but there is no principal solution, and the list-with-tail-variable representation cannot even express such stacks. Keeping the variable in tail position is exactly what keeps inference canonical.

(This subsumes the earlier restriction: no middle `pass`, and no leading one either.)

### Worked schemes

```text
def square = dup >> *
-- dup : A ⇒ A A;  * : Int Int ⇒ Int
-- unify: A = Int
-- square : Int ⇒ Int

def first = id drop
-- id : A ⇒ A;  drop : B ⇒ •
-- first : ∀A B. A B ⇒ A

dup >> f g        -- f : A ⇒ B, g : A ⇒ C
-- dup : A ⇒ A A;  f g : A A ⇒ B C
-- : A ⇒ B C

def increment = (1 ... >> +)
-- 1 ... : ρ ⇒ Int ρ;  + : Int Int ⇒ Int
-- unify: ρ = Int
-- increment : Int ⇒ Int
```

### Consequences for the extension sections

* All signatures are exact as written — no primitive quantifies over an implicit remainder. Stack variables appear only in `pass : ∀ρ. ρ ⇒ ρ` and as the consumed/produced segments of higher-order eliminators.
* `apply : Fn⟨Γ ⇒ Δ⟩ Γ ⇒ Δ` already satisfies the invariant: the quotation sits on the first wire and `Γ` is the tail. Higher-order eliminators must follow this shape — a segment variable can only be a tail, so control values (quotations, booleans) come first and the consumed segment comes last.
* `branch` and `trace` are oriented accordingly (see their sections: condition/quotations on the leftmost wires, `Γ` as the tail; `trace` feeds back the first wire, not the last).

### Implementation notes

* Represent stacks as a list of element types with an optional tail variable at the right end. Stack append then only ever attaches a closed prefix onto a possibly-open tail — total, no placeholder case. (The current `SCons` orientation and the `appendStack (SVarTy v)` hack both go away.)
* Instantiation is position-dependent: non-final tensor atoms unify their fresh `ρ` with `•` immediately.
* `>>>` desugaring must open only the last stage of the accumulator, not wrap the accumulated term: `a >> b >>> c` is `Seq (Seq a (Tensor b pass)) c`, not `Seq (Tensor (Seq a b) pass) c`.

## Type inference

Use Hindley–Milner-like inference extended with stack variables.

Type variables:

```text
A, B, C
```

Stack variables:

```text
ρ, σ
```

Stack effects:

```text
Σ_in ⇒ Σ_out
```

Tensor rule:

```text
t : Γ1 ⇒ Δ1
u : Γ2 ⇒ Δ2
-------------------------
t u : Γ1 Γ2 ⇒ Δ1 Δ2
```

Instantiation in tensor position follows the remainder discipline above: only the final operand of a chain may carry an open tail variable; all others are closed with `ρ := •`.

Sequential rule:

```text
t : Γ ⇒ Δ
u : Δ ⇒ Θ
----------------
t >> u : Γ ⇒ Θ
```

In implementation, infer fresh stack effects for subterms; `>>` generates equality constraints between output and input stacks. Solve by stack/list unification.

Definitions should support let polymorphism:

```text
def name = program
```

Generalize all free type and stack variables not fixed by the environment.

## Cartesian laws to preserve or normalize by

Category laws:

```text
id >> f = f
f >> id = f
(f >> g) >> h = f >> (g >> h)
```

Tensor laws:

```text
(f >> g) (h >> k) = (f h) >> (g k)
f • = f = • f
```

Symmetry:

```text
swap >> swap = id id
```

Comonoid/cartesian laws:

```text
dup >> dup id = dup >> id dup
dup >> swap = dup

dup >> drop id = id
dup >> id drop = id
```

Naturality:

```text
f >> dup = dup >> f f
f >> drop = drop
```

## Example programs

Assume:

```text
+     : ∀ρ. Int Int ρ ⇒ Int ρ
*     : ∀ρ. Int Int ρ ⇒ Int ρ
print : ∀ρ A. A ρ ⇒ ρ
```

Square:

```text
def square = dup >> *
```

Projection:

```text
def first = id drop
```

Parallel unary functions:

```text
1 2 3
f g f
+
print
```

Partial tensor stage with remainder:

```text
1 2 3 4 5 6
f h g ...
+
```

or:

```text
1 2 3 4 5 6 >> f h g >>> +
```

Cartesian pairing:

```text
dup >> f g
```

Given `f : A ⇒ B` and `g : A ⇒ C`, this has type:

```text
A ⇒ B C
```

## Quotations / function values

Add a value type for quoted programs:

```text
Fn⟨Γ ⇒ Δ⟩
```

Quotation:

```text
[p] : • ⇒ Fn⟨Γ ⇒ Δ⟩
```

when:

```text
p : Γ ⇒ Δ
```

Application:

```text
apply : Fn⟨Γ ⇒ Δ⟩ Γ ⇒ Δ
```

Example:

```text
[dup >> *] 7
apply
print
```

Should print `49`.

Initially restrict quotations to closed programs. Add closures later only if needed.

## Exponentials update — integration notes

`spec-update-exponentials.md` extends this document with open abstractions,
exponential values, named-variable wiring, and refined tensor rules. Adopted
into this spec:

* **`Fn⟨Γ ⇒ Δ⟩` is the exponential type** (renamed from `Code⟨…⟩` throughout
  this document; the implementation's `TCode`/`Code⟨…⟩` display is queued for
  the same rename). `Thunk⟨Δ⟩ ≜ Fn⟨• ⇒ Δ⟩` is display sugar.
* **Parentheses group, brackets reify.** `(p)` is the open program `p`,
  unchanged in type; `[p]` is exponential introduction. `list(…)` remains a
  distinct literal form (the tokenizer already special-cases `list(`).
* **Named abstractions** `(x y -> body)` / `[x y -> body]` are syntax over
  `id`/`swap`/`dup`/`drop`: elaborate to structural wiring, then (for
  brackets) reify. The scope rule is strict — unresolved names are errors,
  never inferred parameters.
* **`[f g]` ≠ `[f] [g]`** — matches the existing quotation semantics (each
  bracket is one reification). `tensorFn`, `curry`, `uncurry` are staged as
  explicit combinators; exponential boundaries never flatten.

Reconciliation with the remainder discipline:

* **The `apply` ordering question is settled by the invariant.** The
  argument-first signature `Γ Fn⟨Γ ⇒ Δ⟩ ⇒ Δ` puts a segment variable in
  leading position — inexpressible under the tail-only invariant and
  non-principal to unify. So the typing convention is **function-first**:
  `apply : Fn⟨Γ ⇒ Δ⟩ Γ ⇒ Δ`. Crucially, the argument-first *surface style*
  still works, because pushed values enter at the front wire:

  ```text
  7
  [square] ...
  apply
  ```

  After line 2 the stack is `Fn⟨Int ⇒ Int⟩ Int` — the quotation landed on
  wire 1, exactly where function-first `apply` wants it, with the `...`
  carrying the `7` beneath it (constants have no implicit remainder). The
  update's desired visual parallel with `7 / square` holds with no change
  to the typing convention.
* **Constants are strictly terminal-source — no implicit remainder.**
  `7 : • ⇒ Int`, `true : • ⇒ Bool`, `[p] : • ⇒ Fn⟨…⟩`,
  `list(…) : • ⇒ List A` — exactly as written, in every position. A
  constant makes exactly its own wires; pushing onto a nonempty stack
  requires the explicit remainder: `7 ... : ρ ⇒ Int ρ`. Consequently
  `1 >> +` is ill-typed (`•` cannot supply `+`'s second wire) and the
  increment is `(1 ... >> +) : Int ⇒ Int`.
* **Operations are exact too — no implicit remainder anywhere.**
  `+ : Int Int ⇒ Int` consumes exactly two wires; on a deeper stack write
  `+ ...`. Every signature in the language means literally what it says,
  and the spec-update's types hold verbatim (no elided-`ρ` reading
  convention). The only stack variables in the primitive environment are
  `pass`'s ρ — the sole source of remainder passing, reached via
  `...`/`>>>` — and the segment variables of `apply`/`branch`, which are
  consumed by the eliminator rather than passed. Every line is a total
  description of its diagram slice: each wire is covered by an atom, an
  `id`, or the `...`.
* **Decided — strict tensor everywhere; explicit `>>`.** A consumer never
  eats the outputs of producers written earlier in the same row. Combined
  with strictly-closed constants, the increment program is
  `(1 ... >> +) : Int ρ ⇒ Int ρ` — the `...` passes the incoming wire
  beneath the pushed literal (`1 >> +` alone is ill-typed: `•` cannot
  supply `+`'s second wire). Bare `1 +` is still a well-typed tensor —
  `(• ⇒ Int) ⊗ (Int Int ρ ⇒ Int ρ) = Int Int ρ ⇒ Int Int ρ` — the literal
  lands on the front wire and the sum of the two incoming wires sits
  behind it. Named-abstraction bodies need only the `>>`
  (`(x -> x 1 >> +)` works without `...`, since `x` and `1` are both
  terminal-source in context: `x 1 : • ⇒ Int Int`). Spec-update examples
  written in the loose row style are to be read accordingly; see the
  amendment note in `spec-update-exponentials.md`.
* **Closures and local bindings are milestones, not day one.**
  `[x -> x n +] : Γ ⇒ Fn⟨Int ⇒ Int⟩` needs closure values (environment
  capture at reification), and `7 -> x;` needs the two-zone judgment
  `Γ ⊢ p : Σ ⇒ Δ`. Both slot in after the named-abstraction elaborator;
  they supersede "restrict quotations to closed programs" above when they
  land.
* **Grouped programs obey the instantiation rule** like any other atom: a
  non-final `(…)` in a tensor chain is closed (`ρ := •`); only the final
  atom keeps its remainder.

## Sums and control flow (superseding note)

The branching/looping design was consolidated and substantially extended
in `spec-sums.md` — sums of stacks, code rows, routers, the
if/elif/otherwise/endif guard machine, and Elgot iteration (`loop`).
That chapter supersedes the "Branching extension" section below (branch
was retired: `choose = (c t e -> c >> (t | e) >> merge)`).

## Branching extension

Booleans:

```text
true      : • ⇒ Bool
false     : • ⇒ Bool
negative? : Int ⇒ Bool
```

Branch:

```text
branch :
  Bool
  Fn⟨Γ ⇒ Δ⟩
  Fn⟨Γ ⇒ Δ⟩
  Γ
  ⇒ Δ
```

Both branches must have identical input/output stack effects.

The condition and both quotations sit on the leftmost wires; `Γ` — the data both branches consume — is the tail, as the remainder discipline requires.

## Lists extension

Homogeneous lists:

```text
List A
```

Literals:

```text
list(1, 2, 3)
```

Higher-order list ops:

```text
map :
  Fn⟨A ⇒ B⟩
  List A
  ⇒ List B

fold :
  Fn⟨B A ⇒ B⟩
  B
  List A
  ⇒ B
```

Example:

```text
[dup >> *] list(1, 2, 3, 4, 5)
map
[+] 0 id
fold
print
```

Computes sum of squares.

## Fixed points / feedback

Add trace as the diagrammatic primitive:

```text
trace :
  Fn⟨X Γ ⇒ X Δ⟩ Γ
  ⇒ Δ
```

It feeds the first `X` output back into the first `X` input. (The feedback wire is leftmost, not last: `Γ` and `Δ` must be tails per the remainder discipline.)

Add conventional fixed point:

```text
fix :
  Fn⟨A Γ ⇒ A⟩ Γ
  ⇒ A
```

Derivable from trace:

```text
fix [f] = trace [f >> dup]
```

Important: unrestricted `fix` implies possible nontermination. For total/productive subsets, add guarded recursion or delayed feedback later.

## Monads / effects

Prefer stack-indexed monadic computations:

```text
M⟨Γ⟩
```

rather than `M A`, because programs may return multiple wires.

Core operations:

```text
pureM : Γ ⇒ M⟨Γ⟩

mapM :
  M⟨Γ⟩
  Fn⟨Γ ⇒ Δ⟩
  ⇒ M⟨Δ⟩

joinM :
  M⟨M⟨Γ⟩⟩
  ⇒ M⟨Γ⟩

bindM :
  M⟨Γ⟩
  Fn⟨Γ ⇒ M⟨Δ⟩⟩
  ⇒ M⟨Δ⟩
```

with:

```text
bindM = mapM >> joinM
```

Do not let ordinary juxtaposition imply symmetric tensor for arbitrary effectful computations. Effects like IO/state are order-sensitive. Keep spaces as pure symmetric tensor. Use explicit bind for ordered effects.

Effectful tensor should only be available for commutative effects that provide a lawful `zipM`.

## Selection monads / control

Selection effects are useful for continuation-aware choice/search/optimization.

Ordinary selection monad:

```text
Sel R A = (A -> R) -> A
```

Stack version:

```text
Select R⟨Γ⟩ ≈ Fn⟨Γ ⇒ R⟩ -> Γ
```

Eliminator:

```text
runSelect :
  Select R⟨Γ⟩
  Fn⟨Γ ⇒ R⟩
  ⇒ Γ
```

Bind:

```text
bindSelect :
  Select R⟨Γ⟩
  Fn⟨Γ ⇒ Select R⟨Δ⟩⟩
  ⇒ Select R⟨Δ⟩
```

Use for:

* choose-best / choose-worst
* search returning witnesses
* game-tree/backward-induction choices
* constraint solving
* planning/scheduling choices scored by downstream cost

Surface syntax idea:

```text
select max by [score] {
  ...
  options >> choose
  ...
}
```

Semantics: `choose` captures the rest of the selection region and selects the option whose continuation yields the best score.

Caution: selection may evaluate continuations multiple times. Keep selection regions pure initially, or add an explicit effect discipline.

## Implementation priority

1. Parser for tensor stages, `>>`, newline, `...`, `>>>`.
2. Core AST: `Prim`, `Tensor [Term]`, `Seq Term Term`, `Quote Term`, maybe `Def`.
3. Stack-effect inference with type variables and stack variables.
4. Unification for stack shapes.
5. Built-ins: `id`, `swap`, `dup`, `drop`, `pass`, literals, arithmetic, `print`.
6. Desugaring: `...` and `>>>` insert trailing `pass`.
7. Let-polymorphic definitions.
8. Quotations and `apply`.
9. Branch/list extensions.
10. Later: trace/fix, monads, selection handlers.

Core invariant to preserve:

```text
spaces      = independent horizontal wiring
>>/newline  = ordered vertical composition
dup/drop    = cartesian copying/deleting
pass/...    = explicit remainder identity at tensor-stage boundary
[program]   = reified diagram
apply       = splice/run reified diagram
```

