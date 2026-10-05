# Glossary

The terms the reference uses without stopping to explain them. The
section after each entry is where `MANUAL.md` treats it. When two docs
spell one concept two ways, this file settles which spelling wins.

**bundle** (§5, §13). `Aⁿ`: one stack segment repeated n times. `Aⁿ` is
the function space `Fin(n) ⇒ A`, stored tabulated and flat. The width is
erased at run time.

**carrier** (§3, §8). The type a model supplies for its theory's
hom-object. `model Circuits in Arrow(Circuit)` makes `Circuit(ε, a, b)`
the carrier. A resource's carrier is a wire of its own type, and `IO`'s is
an abstract linear `World`. The carrier is what a label adds to the
objects; the hom-object is the parameter it fills.

**closed spine** (§8, §12). A spine with no free name and no recursive
back-reference left to resolve. Every elaborated def is one, because
`with Recursive` rewrites the knot to `#fix` and nothing in the body then
names the def. That is what keeps `reflect`, the per-stage schemes and
every functor total.

**cut** (§12). A stage boundary. Splitting a program at a cut yields two
runnable halves whose composite is the whole, and the type between them
is a fact about the cut rather than about the program, so each cut states
its own witnesses (`examples/cuts.braid`). A connected component of a
spine was called a cut too; it is now a **component**, and
`cuts : Code ⇒ List(Code)` is `components`, because `cut` is the older
sense and has the most uses.

**the Doctrine** (§8). The built-in theory a theory may extend to become
transportable: `compose`, `embed`, `observe`, `sample`, and laws. A model
of a theory declared `in Doctrine` owns `;` inside a `with` scope, so a
whole program transports into the category that model presents. The
hom-object ranges over whole stacks, so a stage of any width transports
as itself.

**the empty stack** `•`, `one` (§5, §9). The terminal object: zero wires
and one value, which is the empty stack. `•` is the type display and
`one` is the word, `one : • ⇒ •`; `one` is also `•`'s ASCII spelling in
type position. "One" counts inhabitants rather than wires, and Braid has
no initial object and no empty sum.

**entry** (§8). A slot that builds a carrier out of nothing,
`• ⇒ k(a, b)`. An entry is already a stage of the category, so a `with`
scope leaves it alone. A model's entries are the evidence a sampled law
draws from.

**evidence** (§3, §8). A label is evidence because it cannot be written
by hand and does not have to be threaded, so an arrow carrying one was
really built that way (§3). A model's evidence for a law is its entries
(§8).

**exit** (§8). A slot that takes a carrier and hands back base, such as
`observe : k(Int, Int) ⇒ Int`. An exit is refused inside `with M` and
called under `in M`: entering is a marker, leaving is a model.

**family** (§8). A model that takes a model parameter,
`model F(T(a)) in T′(args)`. Read it as a functor from models of one
theory to models of another. A family applied mints one label for the
whole application, and its argument mints none.

**fragment** (§12). The part of the language `sameCode` decides: the free
bicartesian closed category over the words a program mentions. Wiring,
composition, juxtaposition, literals as nullary constants, and quotations
with `capture` and `ev` are in it. A law over anything outside it is
sampled rather than proved.

**functor** (§8, §12). A user-written graph morphism:
`functor F = <program>` at `• ⇒ Fn⟨Stage ⇒ Code⟩`, one image per
generator. One image per generator determines the whole functor, because
a functor out of a free category is a graph morphism. `with F` extends it
along a scope's spine, and the extension is itself a word, so
`lift2 [F]` applies the same functor at run time.

**grade** (§3). The set of labels on an arrow. Grades live in the
join-semilattice `(P(labels), ∪, ∅)`, so composition unions them and the
empty grade is the bottom. The four words of this family name four
things: a grade is the set, a **label** is one member, a **manifest** is
the grade as the display writes it, and a **receipt** is a label a scope
minted.

A grade may also be a type ARGUMENT, at a position a declaration marks
`ε`, and then it is written as its members: `•` for the empty grade, a
label, a grade variable, or several of those side by side. Juxtaposition
means "at least these" — `k(ε ε', a, c)` is the grade of a composite —
and it is lowered at the parser to the `⊆` constraints composition already
emits, so no type holds a union (§8).

**graded carrier** (§3, §8). A carrier that takes a grade as an argument,
so that the morphism's own grade is in its type: `Circuit(•, Int, Int)` is
a pure circuit and `Circuit(IO, Int, Int)` is one that prints, under one
theory and one model. The display folds the carrier's grade into the
manifest beside the receipt, and the theory's exit (`observe : k(ε, Int,
Int) =ε> Int`) takes it back out onto the arrow that runs the thing. A
carrier with no grade parameter fixes one grade for every program its
theory embeds.

**hom-object** (§8). The parameter of a theory declared with
arrow-shaped arguments, `theory Arrow(k(..., ...))`, or
`theory Arrow(k(ε, ..., ...))` for a graded one. A model fills it with a
carrier. A theory that has one can join the Doctrine and transport whole
programs.

**`in`** (§6, §8). The header clause of membership. `def f in X = body`
declares that this def is a morphism of X. It applies nothing, writes no
wires and mints no label, and the body is exactly as written.

**K-word** (retired). Vocabulary from the `mode` era, which dissolved
into models. A word built by hand under `in K` is a **morphism of the
model**, and the table the elaborator keeps of them is the model's **word
table**; the implementation function `checkKWordShape` still carries the
old name.

**label** (§3). One member of a grade. Every label names a functor and
carries that functor's carrier, looked up from the label's own
declaration. `IO` and `Recursive` are built in; every other label is the
name of a resource, model or functor that a scope minted.

**manifest** (§3). An arrow's grade as the display writes it, between `=`
and `>`, sorted. A pure arrow prints `⇒` and shows no manifest. A
threaded resource and a model's carrier fold onto the same glyph.

**model** (§8). An interpretation of a theory: one program per slot,
`model M in T(args) = slot = body, …`. A model is a functor out of the
category its theory presents. `with M` applies it, and `in M` declares
membership in it.

**pure** (§3). Having the empty grade. A pure arrow prints `⇒`, sits
beside any other arrow without contributing a label, and is what a
written `Fn⟨Σ ⇒ Θ⟩` demands of the quotation that fills it.

**qualified name** (§2, §8). `F/says`: a name an `as` import placed in the
scope `F`. The separator is `/`, which appears in no other construct, so a
qualified name lexes as one identifier. A qualified import is the
inclusion composed with the renaming `with M` applies to slot names, so
nothing downstream asks whether a name has a prefix. A **derived** name
stays inside the scope: `un` of `F/Pair` is `F/unPair`. A slot name is
never qualified, because it is the theory's rather than the module's.

**receipt** (§3, §12). The label a `with` scope mints on the manifest of
everything it elaborated. A receipt says this scope **changed** this
code, so a scope that found nothing to rewrite mints nothing: a model
whose slot names do not occur, and a `with Recursive` on a body that
never names the def, both leave the arrow bare. `in` mints no receipt,
because it applies nothing.

**residual** (§5, §6). The open tail of a row, written `---` and
displayed as a row variable `σ`. A row ending in a residual is the
identity on every alternative it does not name. `...` continues a track's
wires instead and is a different kind of tail, so `(f | ...)` is refused.

**resource** (§3, §8). A nominal wire threaded rather than consumed,
declared `model R in Doctrine = <stack>`. Resource wires ride deepest,
and a run of them shared by both sides of an arrow folds onto the arrow
as `=Log Counter>`. `with R` is transport into the model the declaration
generates, and the routing is inferred, so a word that calls a resource
word carries the label with no header.

**row** (§6). The program form `(p₁ | p₂ | …)`: one wire carrying
alternative stacks, with component i running on alternative i. Rows are
line-scoped and an arm is bare code. The word also names the alternative
list of a sum type, which is the same thing seen as a type, and a line of
a CSV read by `table` (§8).

**slot** (§6, §8). A named operation of a theory, declared
`slot : Σ ⇒ Θ` and filled by a model with `slot = body`. The word also
names one position in a binder's parameter list (§6); the theory sense is
far more common.

**spine** (§12). A program as a list of stages, `Code = List(Stage)`.
`reflect` turns a quotation into its spine, and the list library becomes
the metaprogramming library.

**stage** (§3). A juxtaposition of atoms aligned with wires left to
right, the leftmost atom taking the deepest wires. A stage is one
horizontal slice of the diagram. `;`, `>>` and a newline all compose
stages.

**template** (§8). A def whose header is `in T` for a theory `T`. It is a
morphism of `T`, its body waits for a model, and it is not a def until
one arrives. A `with M` scope expands it against M's bindings.

**theory** (§8). A presentation: named slots with signatures, and laws
written as programs. A theory says what operations exist and what must
hold of them, and interprets nothing. `with Monoid` is refused, because a
theory is not a functor.

**transformation** (§8). A natural transformation between two models of
one theory, declared with a base word between their carriers. The
generated squares are naturality squares, proved where the normalizer
reaches and sampled otherwise. `:transformations` lists every declared
one with the verdict on each square.

**width** (§5, §13). The exponent `n` of a bundle `Aⁿ`, a unary natural
and a sort of its own. A width is erased at run time. A literal width
expands during checking; a variable width never flattens.

**wire** (§3). One component of the stack, which is a product of wires.
An atom covers exactly its own wires, and every incoming wire must be
covered by some atom in the stage.

**`with`** (§6, §8). The header clause of application.
`def f with X … = body` writes the body in the domain of X and applies X
to it. It names resources, models, functors and the marker `Recursive`,
and one clause may mix kinds. Every `with` that changes the code leaves a
receipt.

**word table** (§8). The table the elaborator keeps of the words a
program built by hand under `in K`, for `K` a model with a carrier. A def
joins it when it builds one carrier out of nothing, which is what a
morphism of the category is, and a later `with K` then leaves it alone
instead of embedding it.
