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
id   : ∀ρ A. A ρ ⇒ A ρ
swap : ∀ρ A B. A B ρ ⇒ B A ρ
dup  : ∀ρ A. A ρ ⇒ A A ρ
drop : ∀ρ A. A ρ ⇒ ρ
```

The remainder variable `ρ` is always written last: a primitive acts on the leftmost wires and passes everything to the right of them through. See "Remainder discipline" for why `ρ` may appear only in this position.

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

A single-atom stage is its own final atom, so a bare `+` keeps its `ρ` and acts on the two leftmost wires.

Operational reading: a stage consumes the leftmost `k` wires, where `k` is the sum of its atoms' closed input arities. If the stage is open (its final atom retains `ρ`, or it ends in `pass` / `...`), all wires to the right flow through untouched. If it is closed, the incoming stack must be exactly `k` wires wide.

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
-- dup (sole atom) keeps ρ  : A ρ ⇒ A A ρ
-- *   (sole atom) keeps ρ' : Int Int ρ' ⇒ Int ρ'
-- unify: A = Int, ρ = ρ'
-- square : ∀ρ. Int ρ ⇒ Int ρ

def first = id drop
-- id   (non-final) closed : A ⇒ A
-- drop (final) keeps ρ    : B ρ ⇒ ρ
-- first : ∀A B ρ. A B ρ ⇒ A ρ

dup >> f g        -- f : A ⇒ B, g : A ⇒ C
-- dup keeps ρ : A ρ ⇒ A A ρ;  f g closed : A A ⇒ B C
-- unify: ρ = •
-- : A ⇒ B C
```

### Consequences for the extension sections

* All library primitives implicitly quantify over a trailing remainder (`+ : ∀ρ. Int Int ρ ⇒ Int ρ`); extension signatures omit `ρ` for brevity.
* `apply : Code⟨Γ ⇒ Δ⟩ Γ ⇒ Δ` already satisfies the invariant: the quotation sits on the first wire and `Γ` is the tail. Higher-order eliminators must follow this shape — a segment variable can only be a tail, so control values (quotations, booleans) come first and the consumed segment comes last.
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
Code⟨Γ ⇒ Δ⟩
```

Quotation:

```text
[p] : • ⇒ Code⟨Γ ⇒ Δ⟩
```

when:

```text
p : Γ ⇒ Δ
```

Application:

```text
apply : Code⟨Γ ⇒ Δ⟩ Γ ⇒ Δ
```

Example:

```text
[dup >> *] 7
apply
print
```

Should print `49`.

Initially restrict quotations to closed programs. Add closures later only if needed.

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
  Code⟨Γ ⇒ Δ⟩
  Code⟨Γ ⇒ Δ⟩
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
  Code⟨A ⇒ B⟩
  List A
  ⇒ List B

fold :
  Code⟨B A ⇒ B⟩
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
  Code⟨X Γ ⇒ X Δ⟩ Γ
  ⇒ Δ
```

It feeds the first `X` output back into the first `X` input. (The feedback wire is leftmost, not last: `Γ` and `Δ` must be tails per the remainder discipline.)

Add conventional fixed point:

```text
fix :
  Code⟨A Γ ⇒ A⟩ Γ
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
  Code⟨Γ ⇒ Δ⟩
  ⇒ M⟨Δ⟩

joinM :
  M⟨M⟨Γ⟩⟩
  ⇒ M⟨Γ⟩

bindM :
  M⟨Γ⟩
  Code⟨Γ ⇒ M⟨Δ⟩⟩
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
Select R⟨Γ⟩ ≈ Code⟨Γ ⇒ R⟩ -> Γ
```

Eliminator:

```text
runSelect :
  Select R⟨Γ⟩
  Code⟨Γ ⇒ R⟩
  ⇒ Γ
```

Bind:

```text
bindSelect :
  Select R⟨Γ⟩
  Code⟨Γ ⇒ Select R⟨Δ⟩⟩
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

