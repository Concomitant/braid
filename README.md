# Braid

## Implementation Plan (Cartesian Variant)

### 1) Language Design Freeze
- **Core semantics**: every program is a stack transformer with judgment `Σ_in ⇒ Σ_out`.
- **Stacks**: `Γ ::= • | Γ · A` (lists, not nested pairs). The empty stack `•` is the tensor unit.
- **Composition**:
  - **Sequential**: `t >> u` (pipe output of `t` into input of `u`).
  - **Tensor (juxtaposition)**: `t u` runs in parallel on disjoint stack blocks (block split tensor).
- **Cartesian structure**: build in **copy** and **discard** by default. This is the cartesian (symmetric monoidal) variant where each object has a canonical commutative comonoid structure.
- **Decisions to lock**:
  - Precedence: juxtaposition binds tighter than `>>`.
  - Left-associativity for both operators.
  - Type names, literal syntax, and primitive catalog.

### 2) Syntax & Parsing
- **AST nodes**:
  - `Prim(name)`
  - `Tensor(left, right)` for juxtaposition
  - `Seq(left, right)` for `>>`
- **Parser**:
  - Tokenize identifiers, integers, and `>>`.
  - Parse juxtaposition by whitespace adjacency with higher precedence than `>>`.

### 3) Type Representation
- **Stack types**:
  - `Empty | Cons(Stack, Type) | Var(ρ)`
- **Program type**:
  - `Arrow(Stack_in, Stack_out)`
- **Polymorphism**:
  - Stack variables `ρ` provide row-polymorphic prefixes.

### 4) Constraint Generation
- For each AST node, assign a fresh `Σ_in ⇒ Σ_out`.
- **Sequential**: add constraint `Σ_out(left) = Σ_in(right)`.
- **Tensor**: build `Σ_in = Σ1 ⧺ Σ3`, `Σ_out = Σ2 ⧺ Σ4`.

### 5) Unification with Stack Variables
- Represent stacks as **list + tail var**: `[T1, T2, … | ρ]`.
- Unify lists elementwise, allowing tail-variable substitution with occurs-check.
- This yields HM-style principal types extended to stacks.

### 6) Core IR & Semantics
- Use a **DAG/string-diagram IR** as the canonical representation (not just an AST).
- Implement an interpreter where the runtime stack is a vector of values.
- **Tensor**: split the stack into two blocks based on inferred arities and run both sides in parallel.
- **Sequential**: run left, then right.

### 7) Standard Library Primitives
- **Required cartesian basis**: `id`, `swap`, `dup`, `drop`.
- **Arithmetic & IO**: `1`, `2`, `+`, `print` as examples.
- **Derived utilities**: `rotl`, `rotr`, and future `dip`-like operators if higher-order features are added.

### 8) Testing
- Parser tests for precedence and associativity.
- Type inference tests for stack-polymorphic primitives.
- Combinator law tests via rewrite normalization.
- Interpreter tests for stack traces.

### 9) Stretch Goals
- Graph-based IR for diagrammatic optimization.
- Quotations + higher-order combinators.
- Bytecode backend.

---

## Language Specification (Cartesian, Concatenative, Stack-Based)

### 1) Core Typing Shape
All programs are stack transformers.

- **Types (elements)**: `A, B, C, ...`
- **Stacks**: `Γ ::= • | Γ · A`
- **Programs**: `Γ ⇒ Δ`

**Composition**

- **Sequential (`>>`)**: if `t : Γ ⇒ Δ` and `u : Δ ⇒ Θ`, then `t >> u : Γ ⇒ Θ`.
- **Tensor / Juxtaposition**: if `t : Γ1 ⇒ Δ1` and `u : Γ2 ⇒ Δ2`, then
  `t u : (Γ1 ⧺ Γ2) ⇒ (Δ1 ⧺ Δ2)`.

The empty stack `•` is the tensor unit. Stacks are lists, so associativity/unit are definitional.

### 2) Required Primitive Combinators (Cartesian Basis)

**Identity**

- For each type `A`:
  - `id_A : A ⇒ A`
- Generalize via tensor: `id_Γ` is the tensor of `id` across the stack.

**Symmetry (wire crossing)**

- For each `A, B`:
  - `swap_{A,B} : A B ⇒ B A`
- Permutations are derived from swaps.

**Copy and Discard (Cartesian / Comonoid Structure)**

- For each `A`:
  - `dup_A : A ⇒ A A`
  - `drop_A : A ⇒ •`

These make the monoidal product cartesian (values can be duplicated and discarded).

### 3) Derived Conveniences (Optional)

- `rotl : A B C ⇒ B C A`
- `rotr : A B C ⇒ C A B`
- “Apply under a block” combinators (dips) derived from permutations + tensor.

### 4) Laws (Definitional Equalities / Rewrites)

#### 4.1 Category Laws (for `>>` and `id`)
- Left identity: `id >> f = f`
- Right identity: `f >> id = f`
- Associativity: `(f >> g) >> h = f >> (g >> h)`

#### 4.2 Monoidal Laws (for tensor/juxtaposition)
- Tensor functoriality:
  `(f1 >> g1) (f2 >> g2) = (f1 f2) >> (g1 g2)`
- Tensor unit: `•` is the unit for concatenation.

#### 4.3 Symmetry Laws (swap)
- Involution: `swap_{A,B} >> swap_{B,A} = id_{A B}`
- Coherence/naturality: swaps behave like wire crossings (can be enforced by permutation normalization).

#### 4.4 Cartesian/Comonoid Laws (dup, drop)
For each `A`, `dup_A` and `drop_A` form a commutative comonoid.

- **Coassociativity**:
  - `dup >> (dup id) = dup >> (id dup)`

- **Counit laws**:
  - `dup >> (drop id) = id`
  - `dup >> (id drop) = id`

- **Commutativity**:
  - `dup >> swap = dup`

#### 4.5 Naturality (Interaction with Arbitrary Functions)
For `f : A ⇒ B`:

- **Dup naturality**:
  - `f >> dup_B = dup_A >> (f f)`

- **Drop naturality**:
  - `f >> drop_B = drop_A`

These yield the equational theory of cartesian categories (up to strictness).

### 5) Stack-Polymorphic Primitives
Primitives are polymorphic over an untouched stack prefix `ρ`.

Examples:

- `1 : ∀ρ. ρ ⇒ ρ · Int`
- `f : ∀ρ. ρ · Int ⇒ ρ · Int`
- `+ : ∀ρ. ρ · Int · Int ⇒ ρ · Int`
- `print : ∀ρ. ρ · Int ⇒ ρ`

### 6) Example Program

Program:

```
1 2 >> f g >> + >> print
```

Typing summary:

- `1 2` pushes two `Int`s in parallel (tensor).
- `f g` applies to each `Int` in parallel.
- `+` consumes two `Int`s.
- `print` consumes the final `Int`.

Inferred overall type:

```
• ⇒ •
```

Or stack-polymorphic:

```
∀ρ. ρ ⇒ ρ
```

### 7) Implementation Notes

We are committing to a **graph-based IR**:

- Parse into a **DAG / string-diagram IR** with explicit `dup/drop/swap` nodes.
- Perform graph rewriting for coherence and optimization.
- This aligns with cartesian string-diagram semantics and makes normalization (permutations + comonoid “spider” fusion) straightforward.
