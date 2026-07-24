# Code⟨⟩ v1: Reflection

## Representation: spine normal form

    data Atom = (Sym | Int | Str | Sym | List(List(Atom)) | List(List(List(Atom))) Bool | List(List(Atom)))
    type Stage = List(Atom)      # a tensor row of atoms
    type Code = List(Stage)      # a chain of stages

Code is quotiented by associativity and units of composition: the
spine, not the parse tree. Consequences: contiguous sections are
sublists (`take`/`skip`), the list library is the metaprogramming
library, and every concatenative property survives reflection — any
slice of well-typed code is well-typed runnable code. Atom tracks:
prim name (Sym, dotted) | int literal | str literal | sym literal |
quote | row (components + residual flag) | grouped compound.
`foldAtom` (generated) is the seven-way eliminator; per-declaration
`mergeName` artifacts give every data type its n-ary uniform collapse.

## reflect : Fn⟨Γ ⇒ Δ⟩ ⇒ (Code | Str)

Three normalizations, in order: (1) captured closure values are
GROUNDED — embedded as literal-pushing code (sums rebuild via
injections, functions recurse); (2) named abstractions are ELIMINATED
into pure wiring — parameters become leading input wires, a parameter
block threads at the back of the stack, per-stage fetch wiring
(dup/swap chains) copies parameters into position, grouped compounds
recurse (cf. Elliott, Compiling to Categories); (3) the result is
encoded as the spine. v1 gate, on the miss track with an explanation:
parameters captured inside quotations or row components (true
closures — await curry), and segment-consuming or open-arity atoms
(apply, injections, merge, loop, …) inside abstraction bodies. Plain
wiring, arithmetic, literals, groups, closed rows, and exact defs all
reflect — the GLA fragment in particular.

## evalCode : Code ρ1 ⇒ (ρ2 | Str ρ1)

The dynamically-checked splice: rebuild the term, infer its principal
type in-process, run it on the segment. Any failure (malformed code,
type error, runtime error) rides the miss track with the message AND
the untouched segment. Documented hole: ρ2 is free, so a lying
context is caught downstream by the interpreter's defensive value
checks (clean runtime errors, never crashes). Typed splice is future
work.

## First transforms (examples/transpose.braid)

Transpose (GLA dagger): reverse the spine, dualize atoms (dup↔+,
swap↔swap) — `reverse >> [[dualAtom] ... >> map] ... >> map`.
Linearity: `linear?` folds atom-wise membership in the linear
generator set. Both are user code; the customer queue for later
transforms: fusion/IR rewrites under checked laws, within-namespace
elaboration, doc-field attachment to stage ranges.
