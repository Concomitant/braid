# Language update: open abstractions, exponential values, variable wiring, and tensor rules

Spec addendum extending `expanded-spec.md`. See its "Exponentials update —
integration notes" section for how this reconciles with the remainder
discipline and the current implementation.

> **Amendment (decided after writing):** strict block-split tensor holds
> everywhere, including abstraction bodies — a consumer never eats the
> outputs of producers written earlier in the same row. Examples below in
> the loose row style are to be read with an explicit `>>` before the
> consumer: `(x -> x 1 +)` → `(x -> x 1 >> +)`, `(x -> x x *)` →
> `(x -> x x >> *)`, and so on. Bare `1 +` remains well-typed as the
> tensor `(• ⇒ Int) ⊗ (Int Int ⇒ Int) = Int Int ⇒ Int Int` — the literal
> on the front wire, the sum behind it — which is precisely why the
> implicit reading is rejected: it would silently shadow an
> already-meaningful program.
>
> Further, *nothing* carries an implicit remainder — constants are
> strictly terminal-source (`1 : • ⇒ Int`) and operations are exact
> (`+ : Int Int ⇒ Int` consumes exactly two wires; on a deeper stack
> write `+ ...`). Every signature in this document is therefore literal,
> with no elided-`ρ` convention. The point-free increment needs the
> explicit remainder to pass its argument beneath the pushed literal:
> `(1 +)` → `(1 ... >> +) : Int ⇒ Int`, and `[1 +]` →
> `[1 ... >> +] : • ⇒ Fn⟨Int ⇒ Int⟩`. Named bodies need no `...` —
> `x 1 : • ⇒ Int Int` since both are terminal-source in context.

## Design direction

Keep the core language purely concatenative and stack-based:

```text
p : Γ ⇒ Δ
```

Every ordinary program fragment is an open string diagram. Product and stack types are always flat:

```text
(A B) C ≡ A B C ≡ A (B C)
```

The empty stack:

```text
•
```

is the terminal object.

A literal such as:

```text
7
```

is therefore already a complete program:

```text
7 : • ⇒ Int
```

Likewise, a named function such as:

```text
square : Int ⇒ Int
```

is already a program. Thus:

```text
7 >> square
```

and:

```text
7
square
```

both denote ordinary sequential composition:

```text
• ⇒ Int
```

No function value or apply operation is involved.

Exponentials are used only when a program itself must become a first-class value:

```text
Fn⟨Γ ⇒ Δ⟩
```

A value of exponential type occupies one slot in the surrounding flat stack, even though its latent domain and codomain may each contain multiple wires.

## Programs versus exponential values

The language must distinguish:

1. an open program that may be composed immediately;
2. a point of an exponential object that may be stored, passed, returned, or applied later.

These are related, but they are not the same syntactic object.

### Open program

An ordinary program:

```text
dup >> *
```

has type:

```text
Int ⇒ Int
```

It may be composed directly:

```text
7
dup
*
```

or:

```text
7 >> dup >> *
```

### Grouped open program

Parentheses delimit an open program without turning it into a value:

```text
(dup >> *)
```

still has type:

```text
Int ⇒ Int
```

Therefore:

```text
7 >> (dup >> *)
```

is ordinary composition.

Parentheses provide syntactic grouping only. They do not introduce an exponential.

### Exponential introduction

Brackets turn an open program into a point of an exponential object:

```text
[dup >> *]
```

has type:

```text
• ⇒ Fn⟨Int ⇒ Int⟩
```

This is a first-class function value.

To use it on an integer:

```text
7 [dup >> *] >> apply
```

where:

```text
apply :
  Γ Fn⟨Γ ⇒ Δ⟩ ⇒ Δ
```

or, if the chosen stack order places the function first:

```text
apply :
  Fn⟨Γ ⇒ Δ⟩ Γ ⇒ Δ
```

The implementation must select one ordering convention and use it consistently.

The key distinction is:

```text
(dup >> *)
```

an open program:

```text
Int ⇒ Int
```

versus:

```text
[dup >> *]
```

a producer of a function value:

```text
• ⇒ Fn⟨Int ⇒ Int⟩
```

This gives the visual rule:

> Parentheses delimit a program.
> Brackets reify a program as a value.

## Definitions

Definitions bind named programs or morphisms directly.

```text
def square =
  dup
  *
```

binds:

```text
square : Int ⇒ Int
```

Likewise:

```text
def seven = 7
```

binds:

```text
seven : • ⇒ Int
```

Then:

```text
seven
square
```

is ordinary composition:

```text
• ⇒ Int
```

A function-valued definition must explicitly introduce an exponential:

```text
def squareValue = [dup >> *]
```

with:

```text
squareValue : • ⇒ Fn⟨Int ⇒ Int⟩
```

Using the direct program:

```text
7
square
```

Using the function value:

```text
7
squareValue
apply
```

These are semantically related but syntactically distinct.

A constant thunk is similarly explicit:

```text
def coordinates = [1 4 5]
```

with:

```text
coordinates : • ⇒ Fn⟨• ⇒ Int Int Int⟩
```

By contrast:

```text
def coordinates = 1 4 5
```

binds the terminal-source program:

```text
coordinates : • ⇒ Int Int Int
```

Mentioning it produces the values immediately.

## Constant exponential values

A bracketed program may contain only terminal-source producers:

```text
[1 4 5]
```

The enclosed program has type:

```text
• ⇒ Int Int Int
```

Therefore the bracketed form has type:

```text
• ⇒ Fn⟨• ⇒ Int Int Int⟩
```

Equivalently:

```text
[1 4 5] : • ⇒ Thunk⟨Int Int Int⟩
```

where:

```text
Thunk⟨Δ⟩ ≜ Fn⟨• ⇒ Δ⟩
```

Applying it:

```text
[1 4 5]
apply
```

produces:

```text
1 4 5
```

This supports:

* delayed constants;
* branch bodies;
* defaults;
* nullary constructors;
* reusable templates;
* effectful computations that should run later rather than at definition time.

The distinction is:

```text
1 4 5
```

produce the values now;

```text
[1 4 5]
```

produce a reusable nullary function that will produce them later.

## Named-input open abstractions

Add named-input syntax for constructing open programs.

Recommended syntax:

```text
(x y -> body)
```

This creates an open program directly. It does not create a function value.

Example:

```text
(x -> x 1 +)
```

has type:

```text
Int ⇒ Int
```

It may be composed immediately:

```text
7
(x -> x 1 +)
```

which produces 8.

Example with two inputs:

```text
(x y -> x y +)
```

has type:

```text
Int Int ⇒ Int
```

The parameter list determines the input-wire order.

Alternative separator spellings may remain parser experiments:

```text
(x y => body)
(x y | body)
```

The recommended initial spelling is:

```text
->
```

because it clearly marks abstraction and remains distinct from sequential composition:

```text
>>
```

## Named-input exponential values

Brackets around a named abstraction produce a point of the corresponding exponential:

```text
[x y -> body]
```

This is shorthand for:

```text
[(x y -> body)]
```

Example:

```text
[x -> x 1 +]
```

has type:

```text
• ⇒ Fn⟨Int ⇒ Int⟩
```

Example:

```text
[x y -> x y +]
```

has type:

```text
• ⇒ Fn⟨Int Int ⇒ Int⟩
```

Thus:

```text
(x -> x 1 +)
```

is an open program:

```text
Int ⇒ Int
```

while:

```text
[x -> x 1 +]
```

is a terminal-source producer of a function value:

```text
• ⇒ Fn⟨Int ⇒ Int⟩
```

This distinction must remain explicit in the parser, type checker, and IR.

## Semantics of named variables

Named parameters are not runtime dictionary lookups. They label generalized elements of the input context.

For:

```text
(x : A, y : B -> body)
```

the input context is:

```text
A B
```

Categorically:

```text
x : A B ⇒ A
y : A B ⇒ B
```

They are projections from the input product.

The compiler elaborates variable use into cartesian structural wiring:

* one use routes the input wire to that occurrence;
* repeated use inserts copying;
* an unused parameter inserts deletion;
* reordered use inserts symmetry or a general permutation.

The named layer is therefore syntax over:

```text
id
swap
dup
drop
```

It does not add new semantic power.

### Examples

Named square:

```text
(x -> x x *)
```

elaborates to:

```text
dup >> *
```

Named subtraction with reversed inputs:

```text
(x y -> y x -)
```

elaborates approximately to:

```text
swap >> -
```

First projection:

```text
(x y -> x)
```

elaborates to:

```text
id drop
```

Repeated and reordered use:

```text
(x y -> x x * y +)
```

elaborates to a diagram equivalent to:

```text
dup id
>> * id
>> +
```

modulo the exact canonical permutation chosen by the compiler.

The bracketed equivalents:

```text
[x -> x x *]
[x y -> y x -]
[x y -> x]
[x y -> x x * y +]
```

reify those open diagrams as exponential values.

## Variables and generalized elements outside abstractions

Local variables may also be introduced outside parentheses or brackets.

For example:

```text
7 -> x;
x
square
```

The binder takes an existing runtime wire and introduces a name for it in the lexical context.

The occurrence:

```text
x
```

denotes a generalized element of its type relative to that context.

If the lexical context is:

```text
Γ
```

and:

```text
x : A
```

then the occurrence has semantics:

```text
x : Γ ⇒ A
```

More precisely, when the visible data stack is also present, the internal typing judgment may be:

```text
Γ ⊢ p : Σ ⇒ Δ
```

and a variable occurrence behaves as a contextual producer:

```text
Γ ⊢ x : Σ ⇒ Σ A
```

The compiler may eventually lower local variable use to ordinary cartesian wiring.

Repeated local use:

```text
x x +
```

corresponds to pairing the generalized element with itself:

```text
⟨x, x⟩ : Γ ⇒ A A
```

and therefore introduces copying.

The same name-resolution principle applies everywhere:

> A name denotes a morphism appropriate to the current context.
> Writing the name inserts that morphism into the current program.

## Scope rule

Undefined names are always errors.

Invalid:

```text
x 1 +
```

unless x has been explicitly introduced by:

* an open abstraction parameter;
* a bracketed abstraction parameter;
* a local binding;
* a global definition;
* a primitive definition.

The compiler must not silently convert unresolved identifiers into inferred parameters.

This prevents misspelled identifiers from becoming accidental abstractions.

Valid explicit forms include:

```text
(x -> x 1 +)
[x -> x 1 +]
7 -> x;
x 1 +
```

Unknown names inside any of these forms remain errors.

## No inferred-parameter quotation initially

Do not initially interpret:

```text
[x 1 +]
```

as an implicit abstraction over x.

Instead, parse it as a bracketed ordinary program containing the identifier x.

If x is not already in scope, it is an error.

To introduce a parameter, require:

```text
[x -> x 1 +]
```

For the open-program form, require:

```text
(x -> x 1 +)
```

Reasons:

* typos remain detectable;
* parameter order is explicit;
* global-name lookup remains predictable;
* the distinction between capture and abstraction stays visible;
* parser behavior is not dependent on name-resolution failure.

Point-free forms remain concise:

```text
(1 +)
```

has type:

```text
Int ⇒ Int
```

and:

```text
[1 +]
```

has type:

```text
• ⇒ Fn⟨Int ⇒ Int⟩
```

These correspond respectively to:

```text
(x -> x 1 +)
```

and:

```text
[x -> x 1 +]
```

## Tensor-product rules

### First-order tensor

Juxtaposition of open programs is horizontal composition.

If:

```text
f : Γ₁ ⇒ Δ₁
g : Γ₂ ⇒ Δ₂
```

then:

```text
f g : Γ₁ Γ₂ ⇒ Δ₁ Δ₂
```

The domains and codomains flatten:

```text
(Γ₁ Γ₂) Γ₃ ≡ Γ₁ Γ₂ Γ₃
```

Each juxtaposed term consumes one contiguous input block, ordered left to right.

Example:

```text
f : A Z ⇒ B
g : A   ⇒ C
```

Then:

```text
f g : A Z A ⇒ B C
```

The two A inputs are distinct.

Tensor does not duplicate or share inputs.

To share one input explicitly:

```text
dup >> f g
```

If:

```text
f : A ⇒ B
g : A ⇒ C
```

then:

```text
dup >> f g : A ⇒ B C
```

### Terminal-source programs under tensor

Suppose:

```text
seven : • ⇒ Int
four  : • ⇒ Int
```

Then:

```text
seven four
```

has source:

```text
• •
```

which flattens using the terminal-unit law:

```text
• • ≡ •
```

Therefore:

```text
seven four : • ⇒ Int Int
```

and:

```text
seven four
+
```

is a complete program:

```text
• ⇒ Int
```

This is why constants need not be treated as nullary function values. They are already terminal-source morphisms.

## Tensor inside grouped programs

Parentheses preserve the ordinary tensor semantics of the enclosed program.

If:

```text
f : Γ₁ ⇒ Δ₁
g : Γ₂ ⇒ Δ₂
```

then:

```text
(f g)
```

has type:

```text
Γ₁ Γ₂ ⇒ Δ₁ Δ₂
```

Parentheses do not affect the type except by determining parsing and scope.

Example:

```text
(square even?)
```

where:

```text
square : Int ⇒ Int
even?  : Int ⇒ Bool
```

has type:

```text
Int Int ⇒ Int Bool
```

It consumes two independent integers.

To share one integer:

```text
(dup >> square even?)
```

has type:

```text
Int ⇒ Int Bool
```

## Tensor inside exponential values

Brackets reify the entire enclosed tensor program as one function value.

If:

```text
f : Γ₁ ⇒ Δ₁
g : Γ₂ ⇒ Δ₂
```

then:

```text
[f g]
```

has type:

```text
• ⇒ Fn⟨Γ₁ Γ₂ ⇒ Δ₁ Δ₂⟩
```

Example:

```text
[square even?]
```

has type:

```text
• ⇒ Fn⟨Int Int ⇒ Int Bool⟩
```

It represents one function that consumes two independent integers.

To construct one function sharing a single integer:

```text
[dup >> square even?]
```

has type:

```text
• ⇒ Fn⟨Int ⇒ Int Bool⟩
```

The open and reified versions are:

```text
(dup >> square even?)
:
Int ⇒ Int Bool

[dup >> square even?]
:
• ⇒ Fn⟨Int ⇒ Int Bool⟩
```

## Multiple exponential values

Separate brackets produce separate function values.

```text
[f] [g]
```

has type:

```text
• ⇒
  Fn⟨Γ₁ ⇒ Δ₁⟩
  Fn⟨Γ₂ ⇒ Δ₂⟩
```

By contrast:

```text
[f g]
```

produces one function value:

```text
• ⇒ Fn⟨Γ₁ Γ₂ ⇒ Δ₁ Δ₂⟩
```

Therefore:

```text
[f g]
```

and:

```text
[f] [g]
```

are not equivalent.

The distinction is:

```text
[f g]
```

one exponential point representing the tensor program;

```text
[f] [g]
```

two exponential points representing two separate programs.

Do not automatically fuse adjacent function values.

An explicit combinator may be provided later:

```text
tensorFn :
  Fn⟨Γ₁ ⇒ Δ₁⟩
  Fn⟨Γ₂ ⇒ Δ₂⟩
  ⇒
  Fn⟨Γ₁ Γ₂ ⇒ Δ₁ Δ₂⟩
```

Operationally, tensorFn constructs the exponential point corresponding to the tensor of the two represented morphisms.

The core rule remains:

> Juxtaposition tensors open programs.
> Brackets determine which entire program is reified as one value.

## Products and exponentials

All ordinary stack products remain flat:

```text
A B C
```

This represents:

* three stack wires;
* the strict product object A × B × C;
* the input or output boundary of a multivalue program.

A function type has flat latent boundaries:

```text
Fn⟨A B C ⇒ D E⟩
```

The function value itself occupies one outer stack position.

Nested exponentials are not flattened:

```text
Fn⟨A ⇒ Fn⟨B ⇒ C⟩⟩
```

remains distinct from:

```text
Fn⟨A B ⇒ C⟩
```

They may be connected by explicit operations:

```text
curry
uncurry
```

This means:

* products flatten;
* tensor boundaries flatten;
* grouped program syntax does not affect types;
* exponential boundaries remain explicit;
* nested exponentials encode staging;
* quotation is exponential introduction, not mere grouping.

## Application and evaluation

Application is evaluation for an exponential value.

Choose one canonical stack order.

For function-first order:

```text
apply :
  Fn⟨Γ ⇒ Δ⟩ Γ ⇒ Δ
```

Example:

```text
[dup >> *]
7
apply
```

For argument-first order:

```text
apply :
  Γ Fn⟨Γ ⇒ Δ⟩ ⇒ Δ
```

Example:

```text
7
[dup >> *]
apply
```

The latter may align more naturally with:

```text
7
square
```

because the direct and indirect forms become visually parallel:

```text
7
square
```

direct composition;

```text
7
[square]
apply
```

evaluation of an exponential value.

Whichever convention is selected must remain fixed across:

* apply;
* higher-order combinators;
* closure construction;
* map;
* fold;
* branching;
* tensoring of function values.

## Capturing outer variables

Open abstractions may depend on an outer lexical context.

Suppose:

```text
n : Int
```

is already bound.

Then:

```text
(x -> x n +)
```

denotes an open program relative to the outer environment:

```text
Γ Int ⇒ Int
```

or, semantically:

```text
Γ × Int → Int
```

The x parameter is exposed as an input wire. The n dependency remains in the outer context.

The bracketed form:

```text
[x -> x n +]
```

produces a closure:

```text
Γ ⇒ Fn⟨Int ⇒ Int⟩
```

It captures the generalized element n.

Thus:

```text
(x -> x n +)
```

is an environment-dependent open program;

```text
[x -> x n +]
```

is an environment-dependent producer of a function value.

This is the categorical distinction between:

```text
Γ A ⇒ B
```

and its transpose:

```text
Γ ⇒ Fn⟨A ⇒ B⟩
```

## Proposed grammar

Conceptual grammar:

```text
program
  ::= sequence
sequence
  ::= tensorStage (">>" tensorStage)*
tensorStage
  ::= term*
term
  ::= identifier
    | literal
    | primitive
    | groupedProgram
    | quotation
    | localBinding
groupedProgram
  ::= "(" program ")"
    | "(" parameters "->" program ")"
quotation
  ::= "[" program "]"
    | "[" parameters "->" program "]"
parameters
  ::= identifier*
localBinding
  ::= "->" identifier ";"
```

Newline is strict sequential composition:

```text
p
q
```

desugars to:

```text
p >> q
```

Spaces within one tensor stage denote juxtaposition/tensor.

### Parsing examples

```text
(x)
```

means grouping of the resolved program x.

```text
[x]
```

means reification of the resolved program x.

```text
(x -> x)
```

means an open identity program.

```text
[x -> x]
```

means a point of:

```text
Fn⟨A ⇒ A⟩
```

The arrow is required for parameter introduction.

An empty parameter list is unnecessary:

```text
[1 4 5]
```

already expresses a closed exponential value.

Likewise:

```text
(1 4 5)
```

is merely a grouped terminal-source program.

## Type checking named open abstractions

For:

```text
(x₁ ... xₙ -> body)
```

type inference should:

1. Create fresh parameter types:

```text
x₁ : A₁
...
xₙ : Aₙ
```

2. Treat the open input boundary as:

```text
A₁ ... Aₙ
```

3. Resolve each variable occurrence to its parameter projection.
4. Infer and synthesize the required structural wiring.
5. Infer the output stack:

```text
Δ
```

6. Return the open-program type:

```text
A₁ ... Aₙ ⇒ Δ
```

Repeated occurrences must have one consistent parameter type.

Example:

```text
(x -> x x +)
```

assuming:

```text
+ : Int Int ⇒ Int
```

forces:

```text
x : Int
```

and produces:

```text
Int ⇒ Int
```

## Type checking named exponential values

For:

```text
[x₁ ... xₙ -> body]
```

first infer the enclosed open abstraction exactly as above:

```text
A₁ ... Aₙ ⇒ Δ
```

Then perform exponential introduction and return:

```text
• ⇒ Fn⟨A₁ ... Aₙ ⇒ Δ⟩
```

If outer variables are captured under environment Γ, the type is instead:

```text
Γ ⇒ Fn⟨A₁ ... Aₙ ⇒ Δ⟩
```

The implementation should not treat named bracket syntax as a separate variable-binding semantics. It is:

1. named open abstraction;
2. followed by exponential introduction.

## Suggested intermediate representation

Do not immediately lower named parameters to stack shuffles during parsing.

Represent contextual terms explicitly.

```text
OpenAbstraction {
  parameters: [Param],
  body: Program
}
Quote {
  body: Program
}
```

Variable occurrences should initially remain contextual references:

```text
Var {
  binderId: BinderId,
  type: Type
}
```

During elaboration:

1. infer parameter and captured-variable types;
2. construct the contextual dependency graph;
3. compute usage multiplicities;
4. synthesize copying, deletion, and permutation;
5. lower named references to point-free structural wiring;
6. produce an ordinary open program;
7. if brackets were present, perform exponential introduction.

Conceptually:

```text
[x y -> x x * y +]
```

becomes:

```text
Quote(
  OpenAbstraction(
    parameters = [x, y],
    body = x x * y +
  )
)
```

which lowers to:

```text
Quote(
  structuralPrelude
  >> ordinaryBody
)
```

The evaluator only needs:

* ordinary primitives;
* id;
* swap;
* dup;
* drop;
* tensor;
* sequential composition;
* exponential construction;
* evaluation/application.

## Examples

Direct constant:

```text
1 4 5
:
• ⇒ Int Int Int
```

Grouped constant program:

```text
(1 4 5)
:
• ⇒ Int Int Int
```

Grouping does not change its type.

Constant thunk:

```text
[1 4 5]
:
• ⇒ Fn⟨• ⇒ Int Int Int⟩
```

Direct point-free increment:

```text
(1 +)
:
Int ⇒ Int
```

The parentheses are optional when parsing is already clear.

Point-free increment value:

```text
[1 +]
:
• ⇒ Fn⟨Int ⇒ Int⟩
```

Named direct increment:

```text
(x -> x 1 +)
:
Int ⇒ Int
```

Named increment value:

```text
[x -> x 1 +]
:
• ⇒ Fn⟨Int ⇒ Int⟩
```

Named direct square:

```text
(x -> x x *)
:
Int ⇒ Int
```

Named square value:

```text
[x -> x x *]
:
• ⇒ Fn⟨Int ⇒ Int⟩
```

Projection:

```text
(x y -> x)
:
A B ⇒ A
```

Projection value:

```text
[x y -> x]
:
• ⇒ Fn⟨A B ⇒ A⟩
```

Swap:

```text
(x y -> y x)
:
A B ⇒ B A
```

Swap value:

```text
[x y -> y x]
:
• ⇒ Fn⟨A B ⇒ B A⟩
```

Parallel independent programs:

```text
(f g)
:
Γf Γg ⇒ Δf Δg
```

One exponential value containing the tensor:

```text
[f g]
:
• ⇒ Fn⟨Γf Γg ⇒ Δf Δg⟩
```

Two separate exponential values:

```text
[f] [g]
:
• ⇒
  Fn⟨Γf ⇒ Δf⟩
  Fn⟨Γg ⇒ Δg⟩
```

Shared-input direct program:

```text
(dup >> f g)
:
A ⇒ B C
```

Shared-input function value:

```text
[dup >> f g]
:
• ⇒ Fn⟨A ⇒ B C⟩
```

Named shared-input direct program:

```text
(x -> x x >> f g)
:
A ⇒ B C
```

assuming the named-body elaborator permits the two occurrences of x to feed the two tensor branches.

Named shared-input function value:

```text
[x -> x x >> f g]
:
• ⇒ Fn⟨A ⇒ B C⟩
```

## Initial implementation recommendation

Implement now:

```text
p
(p)
[p]
(x y -> p)
[x y -> p]
apply
```

Use these exact semantic rules:

* every ordinary term denotes a morphism;
* literals are terminal-source programs;
* named definitions bind morphisms directly;
* newline is strict sequential composition;
* juxtaposition tensors open programs;
* parentheses group open programs without reifying them;
* brackets reify the enclosed program as a point of an exponential object;
* (x y -> p) constructs an open program with named input wires;
* [x y -> p] constructs the corresponding exponential value;
* parameter order determines input-wire order;
* repeated parameter use generates copying;
* unused parameters generate deletion;
* reordered use generates permutation;
* unresolved names are always errors;
* local variables denote generalized elements of the lexical context;
* tensor inside parentheses behaves exactly like tensor outside parentheses;
* [f g] is one function value representing a tensor program;
* [f] [g] produces two distinct function values;
* product and stack types are flat;
* nested exponential types remain explicit;
* exponential values require evaluation through apply;
* direct named programs compose without apply.

This preserves the core model:

> Any open code fragment is already a program.
> Parentheses merely delimit that program.
> Named abstraction labels its exposed input wires.
> Brackets transpose and reify the program as a point of an exponential object.
> The compiler erases names into ordinary cartesian string-diagram structure.
