# The constructs of Braid

*A reference, not a history. Every claim here is checked against the
shipped checker and the example that exercises it; the examples named
run clean (`cabal run braid -- examples/<f>.braid`) and the test suite
runs all of them.*

Braid's **declaration layer** is small on purpose. Beside the type
layer (`type`, `data`) there are **six declarations** — `theory`,
`model`, `transformation`, `functor`, `resource`, `table` — **one
definition form** (`def`), and **two header clauses** that say what a
definition is and what is applied to it (`in`, `with`). Everything
else — templates, hand-built morphisms, families, receipts, the
Doctrine — is one of those read a particular way, and this document
says which. Two of the six are **sugar over the others**: a `table`
writes a `data` declaration, and a `resource` writes a carrier, a
theory and a `model` of the Doctrine. Both show you what they wrote
(`:doc`).

Cross-references are to `MANUAL.md`.

---

## The table

| construct | declares | applies | mints | checked by | examples |
|---|---|---|---|---|---|
| `theory T(…)` | a presentation: named slots with signatures, and laws | nothing | nothing | `parseTheory` (heads, slot signatures, kinds); `checkExtends` if it is `in Doctrine` | `theories`, `build`, `circuits`, `autodiff`, `prob`, `frame`, `lifting`, `reified`, `resources`, `payroll`, `optimizer`, `distributive`, `transformations` |
| `model M in T(args)` | an interpretation of `T` — a functor out of the category `T` presents | nothing | nothing | `parseInstance`, `declaredSlots` + `checkInstance` (subsumption, per slot); `transportOf` (its shape); the theory's laws **run** at module start | every file with a `theory` |
| `model M in Base` | a rewriting of the *ambient* presentation | nothing | nothing | `parseBaseInstance`, `checkBaseInstance` (each image must have the generator's own scheme) | `optimizer` |
| `model F(T(binders)) in T′(args)` | a **family** — a functor Mod(T) → Mod(T′) | nothing (it is applied by `with F(M)`) | nothing | `parseInstance` (the parameter clause); `familyInstances` mints each member by substitution; each member is then an ordinary model | `autodiff` |
| `transformation N in A ⇒ B = w, …` | a natural transformation between two models of one theory | nothing | nothing | `transformationDefs` (types of the squares); `checkTransformation` (`sameCode` first, the theory's samples second) | `transformations`, `autodiff`, `prob` |
| `functor F = word` | a `Code ⇒ Code` word, usable as a scope | nothing | nothing | `checkFunctorWord` at the first `with F` (Code ⇒ Code, pure, defined) | `traced`, `metered`, `optimizer` |
| `resource R = Ty` | a wire the elaborator threads — **and a model of the Doctrine**: the carrier `data R@k(a..., b...) = Fn⟨R a ⇒ R b⟩`, the theory `R@t` (`compose` and `embed` only), and `model R in R@t(R@k)` | nothing | nothing | the `data` machinery, `transportOf` (the model's shape), and the routing pass (`elabScope`), which is that model's fused evaluator | `resources`, `metered`, `payroll`, `lifting`, `prob`, `autodiff` |
| `table N(cols) = "f.csv"` | a data type, a loader and a header word, read from a CSV **at check time** | nothing | nothing | `parseTableLine`, `tableBlock` (the file, the header, the column types) | `frame` |
| `def f = body` | a word | nothing | nothing | inference | all |
| `def f in T = body` (T a theory) | a **template**: a morphism of `T`, waiting for a model | nothing | nothing | recorded, not defined; `expandTemplates` checks it at the call | `theories`, `build`, `autodiff`, `prob`, `resources`, `transformations` |
| `def f in K = body` (K a model with a carrier) | a **hand-built morphism** of the category `K` presents | nothing | nothing | `inTarget` (the name's kind), `checkKWordShape` (the arrow) | `circuits`, `reified`, `frame`, `prob`, `lifting`, `transformations` |
| `def f with X … = body` | nothing | X to the body | **one label per name** | `elabHeaders`, then ordinary inference of the result | `theories`, `circuits`, `autodiff`, `prob`, `traced`, `metered`, `optimizer`, `resources`, … |
| the Doctrine | *nothing* — it is a built-in theory a theory may extend | nothing | nothing | `checkExtends`, `transportOf` | `circuits`, `frame`, `lifting`, `prob`, `reified`, `transformations` |
| a receipt (`with@F`) | nothing | nothing | it **is** the mint | `receiptScheme`; unwritable by hand (`elabHeaders` refuses `@`) | `traced`, and every arrow with a label |

---

## `theory`

**What it is.** A **presentation**: a set of generators with
signatures, plus equations (laws). It names a category — the free
category on those generators, modulo the laws — without naming any
particular one.

**Syntax.**

```text
theory NAME [ ( params ) ] [ in DOCTRINE ] =
    slot : Σ ⇒ Θ            # a generator, one per line
    law name = <program>    # an equation, one per line
```

Parameters are **kinded by how they are written**: a bare name is one
wire (`Monoid(a)`), `...` a stack, and a type **constructor** carries its
kind **one mark per argument** — `_` where that argument is one wire,
`...` where it is a whole stack. So a hom-object over stacks is
`k(..., ...)` and a parameterized exit over one wire is `d(_)`. A slot
may name variables the theory does not declare; each is local to its
slot and generalized there — and in a constructor's stack position they
are stack variables, which is why `compose : k(a, b) k(b, c) ⇒ k(a, c)`
composes whole sides of a diagram.

`in DOCTRINE` (§8) says this theory **extends** another — at most one,
because a presentation extends by inclusion and two inclusions want a
pushout nobody has asked for.

**What the checker does.** `parseTheory` reads the head (kinds,
parameters, the `in` clause) and each entry (a slot's arrow through the
ordinary type parser; a law's source kept verbatim). `checkExtends`
runs **once per theory, whether or not anything models it**: every slot
the theory declares that the doctrine also declares must be the
doctrine's slot *at the doctrine's shape*, with the doctrine's
constructor parameters instantiated **consistently across every such
slot**.

**What `with` does to it.** Nothing — `with T` is refused (below). A
theory is applied by being *modelled*.

**Examples.** `theories.braid` (`Monoid`, the introduction);
`build.braid` (`Config`, a theory whose models are build settings);
`autodiff.braid` (`Smooth(a, g)`, a ring with `exp` and `sin` over one
carrier, and a second parameter for an exit whose result type varies by
model); `circuits.braid` (`Arrow(k(..., ...)) in Doctrine`, and `Vault`,
a **sealed** theory with no exit); `prob.braid` (`Prob(k(..., ...),
d(...)) in Doctrine`, a Markov category); `frame.braid` (`Columns`);
`lifting.braid` (`Lifting`); `reified.braid` (`Reflective`);
`resources.braid` (`Collector(e, a)`, the generic handler);
`payroll.braid`, `optimizer.braid`, `distributive.braid`,
`transformations.braid`.

**Refusals.**

```text
theory T declares no operations
Malformed theory declaration: after the parameters a theory head takes
  at most `in <Theory>` (…)
`over` is gone since 2026-09-16: a theory extending another is
  MEMBERSHIP — write `theory … in <Theory>` where the `over` is
A constructor parameter's kind is written with one mark per argument —
  `_` for a wire, `...` for a stack: k(..., ...), d(_)
theory T: slot 's' is <arrow>, but Doctrine declares it <arrow> — a
  theory that extends Doctrine declares Doctrine's operations at
  Doctrine's signatures.
theory T: slot 's' reads Doctrine's parameter 'k' as X, but another
  slot reads it as Y — one theory instantiates it once.
theory T: `in Doctrine` declares nothing: Doctrine's operations are …
`Base` is the ambient presentation and may not be declared
`;` composes; separate slots with `,` or a newline
```

---

## `model`

A **model** interprets a theory: a functor out of the category the
theory presents, given by an image for each generator. Four kinds, one
declaration form, and §"the same thing said four ways" below says why
they are one thing.

### Plain model — `model M in T(args)`

**What it is.** An object of Mod(T): a choice of carrier(s) and a
program for each slot, audited against the theory's laws.

**Syntax.** Both body forms, exactly as `def` has both:

```braid
model IntSum in Monoid(Int) =
    unit   = 0
    op     = +
    sample = 7

model Ints in Ring(Int) = add = +, mul = *      # the inline form
```

`,` separates bindings on a line; a newline separates them in a block.
`;` **never** separates: it composes, so `mul = dup ; *` is one binding
whose body composes.

An argument for a **wire** parameter is a full type expression
(`Wrap(List(Int))`); an argument for a **constructor** parameter is a
bare `data` name.

**What the checker does.**
1. `parseInstance` reads the head at the theory's kinds and the
   bindings from both body forms.
2. `instanceDefs` turns each binding into an ordinary def named
   `M@slot`, with the header `with M` so the slot names inside resolve
   to this model's own words.
3. `declaredSlots` + `checkInstance` compare each slot's **inferred**
   arrow against the theory's **declared** arrow instantiated at this
   model's arguments — by subsumption, so a more general body is fine.
4. `transportOf` reads this model's *shape* off the theory's declared
   arrows (composition, embedding, exits) — never off a slot's name.
5. The theory's **laws run**, as ordinary programs, at module start,
   before `main`.

**What `with` does to it.** `with M` **renames**: every occurrence of a
slot name in the body becomes `M@slot`. If the theory is `in Doctrine`
and supplies composition and embedding, `with M` additionally
**transports** — unless the def is declared `in T` for M's theory, in
which case it only instantiates (see `with`, below).

**Examples.** `theories.braid` (`IntSum`, `IntProd`, `StrCat`);
`autodiff.braid` (`Floats`, `Rev`, `RevThread`); `build.braid` (`Dev`,
`Prod`); `circuits.braid` (`Circuits`, `Funcs`, `Sealed`);
`prob.braid` (`Enum`, `Sampler`, `Nondet`, `Mixtures`, `Means`);
`frame.braid` (`Frame`); `reified.braid` (`Reified`);
`resources.braid` (`Logs`, `Counts`); `transformations.braid`
(`Names`, `Funcs`, `ListMonoid`, `IntSum`); `payroll.braid`,
`lifting.braid`, `distributive.braid`.

**Refusals.**

```text
`:` types a slot and nothing else since 2026-09-16: a model's head says
  which theory it interprets, which is MEMBERSHIP — write
  `model M in <Theory>(…)`
model M: no binding for 's' (declared by theory T)
model M: 's' is not an operation of theory T
model M: slot 's' is <arrow> but theory T declares <arrow>
model M: theory T expects N argument(s)
model M: theory T declares 'k' as a type constructor of arity 2, so its
  argument names a declared data type; 'X' is not one
model Bad: T cannot fill the constructor parameter 'k' — theory Arrow
  declares it at k(_, _), so T's parameters must be declared bare (a
  wire) where that says `_`   (and the mirror, `...` where that says
  `...`)
law 'assoc' fails for model M: a model must be an audited model of its
  theory
Duplicate model declaration: M (a functor and a model share one
  namespace — each declares a name a `with` clause may carry)
`;` composes; separate bindings with `,` or a newline
```

### Model of `Base` — `model Opt in Base = p = q, …`

**What it is.** A **partial** model of the *ambient* presentation —
the presentation whose generators are every word in scope, each with
its own scheme as the slot's declared type. It is a rewriting: an image
for the generators it names, and the identity on every generator it
does not.

**Syntax.** `model Opt in Base = p = q, r = s`, or one `p = q` per
indented line. `Base` is reserved and cannot be declared.

**What the checker does.** `checkBaseInstance` blesses each binding
**once**, over the finished environment (so a binding may name a word
declared anywhere in the module): the image must have the generator's
own scheme, at the generator's own use. The declaration also generates
a **word** `Opt : Code ⇒ Code` — the table handed to the `rewrite`
engine — so `[Opt]` is an ordinary quotation and `lift2 [Opt]` applies
the same reinterpretation at run time.

**What `with` does to it.** `with Opt` renames the generators to their
images, through quotations, rows and `fix` bodies, and mints `=Opt>`.

**Examples.** `optimizer.braid` (`model Opt in Base = dupSwap = dup,
copyDrop = id, dupInt = dup, twice = double`, then `with Opt` and
`[Opt]` at run time); `test/imports/util.braid` (a Base model crossing
a module boundary).

**Refusals.**

```text
model Bad in Base: no bindings: write `model Bad in Base = p = q`, or
  one `p = q` per indented line (…)
model Bad in Base: `dup = dupInt` is refused: dup is used at a0 ⇒ a0 a0
  but dupInt is Int ⇒ Int Int
model Bad in Base: nowhere is not defined at this point
model Bad in Base: Mon is a theory, not a word
model Bad in Base: two bindings give `p` an image, and a model sends
  each generator to one thing
`;` composes; separate bindings with `,` or a newline
```

### Model of a Doctrine theory — a category model

**What it is.** A model whose theory is `in Doctrine` and supplies the
doctrine's composition and embedding: it presents a **category**, and
`with` of it is the functor from the base into that category.

**Syntax.** No syntax of its own — it is an ordinary `model`. What
makes it transport is the **shape** of its theory, read by
`transportOf`: a hom-object `k(..., ...)`, a slot at `k(a, b) k(b, c) ⇒
k(a, c)`, a slot at `Fn⟨a ⇒ b⟩ ⇒ k(a, b)`, and exits (`k(Int, Int) ⇒
Int` and kin) — `a`, `b`, `c` being **stacks**, so the carrier is a
process on a whole side of a diagram. Its data type declares a stack
parameter per side: `data Circuit(a..., b...) = …`.

**What the checker does.** Everything a plain model gets, plus:
`transportOf` records the carrier, composition, embedding and exit
slots; a generated word of the model's own name is checked like any
functor's word (`checkFunctorWord`), so that `[Circuits]` and
`lift2 [Circuits]` are values.

**What `with` does to it.** `with M` **transports**: every stage
becomes `embed` of that stage as a quotation and every `;` becomes
`compose`. No arity is read and nothing is packed or whiskered — a
stage of any width embeds as **itself**, and is weighed at exactly the
width it was written, so a stage that does not cover the stack it is
handed fails with the base's own message (`Cannot unify stacks: • vs
Int`). Exits are **refused inside** the scope and called under `in M`.
At most one such model per clause.

```text
def sq with Circuits = dup ; *
#   with@Circuits >> [dup] >> Circuits@embed >> _ [*] >> _ Circuits@embed >> Circuits@compose
```

**Examples.** `circuits.braid` (`Circuits` over stateful stream
transducers, `Funcs` over plain functions, `Sealed` with no exit);
`frame.braid` (`Frame`, a data frame as a category — no loop is ever
written); `prob.braid` (`Enum`, `Sampler`, `Nondet`);
`reified.braid` (`Reified`, a program paired with its own `Code`);
`lifting.braid` (`Notes`); `transformations.braid` (`Names`, `Funcs`).

**Refusals.**

```text
`with M`: theory T takes Doctrine's `compose` and not its `embed`
  (`Fn⟨ρ ⇒ σ⟩ ⇒ k(ρ, σ)`): `with M` cannot transport a base stage;
  `in M` and compose by hand.
`observe` leaves M; call it outside `with M` (a category is left by a
  model, not by a marker)
`with M1 M2`: a clause may name at most one category — the second would
  embed the first's carriers as if they were programs. …
`with M`: the scope is empty, and a transported scope must build a K
```

### Family — `model F(T(binders)) in T′(args)`

**What it is.** Not a model: a **functor Mod(T) → Mod(T′)**. ML's
higher-order functor, Kiselyov's interpreter transformer, and the ring
construction R ↦ R[ε]/ε² are the same thing in three vocabularies.

**Syntax.**

```braid
model Fwd(Smooth(a, _)) in Smooth(Dual(a), a) =
    add = Dual(x, dx) Dual(y, dy) -> (x y ; add) (dx dy ; add) ; Dual
    …
```

The parameter clause names **the theory the argument must model** and a
binder for each of that model's own theory arguments, so the head can
write its own in terms of them; `_` is a binder the head does not use.
There is no name for the parameter itself, and no use for one: a body
is written in **the theory's** vocabulary, and there is exactly one
parameter.

**What the checker does.** `familyInstances` mints each member the
module asks for, **deepest first**, reading the applications off the
source — def headers, def bodies, main, model bindings and the two
model names a transformation declares. The carrier is read by
**substitution**: the binders take the argument model's own theory
arguments and the head is read off. A member is an ordinary `Instance`
from then on, so everything downstream (a transformation naming it, a
receipt printing it, the laws running) needs no case of its own. A
family's **slot bodies are templates over the parameter's theory**, so
they are wrapped in `with <the argument model>` rather than in `with
<itself>`; its **laws** are wrapped in `with <itself>` and run **at
each instantiation**.

**What `with` does to it.** `with F(M)` applies the family and mints
the member; the receipt is the **whole application as one label**
(`=Fwd(Floats)>`, `=Fwd(Fwd(Floats))>`), because one model read the
template and `Floats` never saw it.

**Examples.** `autodiff.braid` — `Fwd`, applied at `Fwd(Floats)` and
at `Fwd(Fwd(Floats))`, which is the second derivative of the *same*
three templates.

**Refusals.**

```text
model F: a parameterized model takes ONE parameter — two would give one
  slot name two meanings inside a body …
model F: a parameter is written `Theory(a, b)` — the theory its argument
  must model, and a name for each of that model's own arguments (`_` for
  one the head does not use), not: …
`with F`: F is a model PARAMETERIZED by a model, so it is a family and
  not a model — apply it, `with F(<model of T>)`
`with F(Nope)`: Nope is not a model declared at this point
`with F(Ints)`: the parameter of model F takes a model of Ring, and
  Ints models Monoid
`with Floats(Fwd)`: Floats is not a parameterized model at this point …
law 'mulAssoc' fails for model Fwd(Floats): …
```

---

## `def … in T` — a template

**What it is.** A **morphism of the theory `T`**: a program in `T`'s
vocabulary, which is to say a morphism of `B[T]`, the base presentation
extended by `T`'s generators. It is not a def until a model says what
its slot names mean.

**Syntax.** `def NAME in T = body`, or `def NAME in T with R… = body`
when it also threads a resource.

**What the checker does.** A template is **recorded, not defined**: it
enters neither the environment nor the runtime scope, because it has no
body that runs. `expandTemplates` inlines it at each call site, inside
the innermost enclosing scope whose model is a model of `T`, and wraps
the inlined body in an **instantiating** scope. Every instantiation is
then **re-inferred where it lands**, so each gets its own principal
type — no rank-1 wall, no dictionary.

**What `with` does to it.** A model of `T` in the `with` clause
instantiates it. Under a Doctrine model, instantiating is **all** it
does: the spine stays base composition, because a morphism of `B[T]`
composes like the base (§8).

**Examples.** `theories.braid` (`fold1 in Monoid`, read by three
models); `build.braid` (`banner`, `stamped`, `plan` over `Config` — a
template calling templates); `autodiff.braid` (`poly`, `wave`, `fxy`,
`cosOf` over `Smooth`, read by five models); `prob.braid` (`bothFlip`,
`coinSnd`, `flipSnd` over `Prob`, instantiated per model);
`resources.braid` (`collected` over `Collector`, the generic handler);
`transformations.braid`.

**Refusals.**

```text
fold1 needs a model of Monoid in scope (`with <model>` before calling it)
template loopy calls itself: a template is expanded at the call, so it
  cannot recurse
`in Monoid Pointed`: a def is ONE thing, so `in` names exactly one
  theory (making this def a template) or one model with a carrier …
`Recursive` is applied, not lived in: write `with Recursive`; the
  open-recursion body is `fix` by hand (MANUAL §8)
```

---

## `def … in K` — a hand-built morphism

**What it is.** A **word of the category `K` presents**, written in
`K`'s vocabulary and entered without transport: a morphism the functor
may not have in its image at all.

**Syntax.** `def NAME in K = body`, where `K` is a model whose theory
has a hom-object.

**What the checker does.** `inTarget` resolves the name **by kind** and
refuses every other kind with the clause to write instead.
`renameSlotsT` puts `K`'s slot words in scope — and nothing else: no
embedding, no composition, no receipt. After inference,
`checkKWordShape` asks whether the def builds **one carrier out of
nothing** (`• ⇒ K(a, b)`), which is what a morphism of the category is;
if it does, the def joins the **K-word table**, so a later `with K`
leaves it alone instead of embedding it. A def that neither builds a
carrier nor uses one of `K`'s words is refused: the clause did nothing.
Membership is **written**, never read off an inferred type.

Since 2026-09-16, an **instantiated template** is classified the same
way: `def f in T with K = …` is a morphism of `T` read by `K`, so if it
builds one carrier it is one of `K`'s words too.

**What `with` does to it.** Nothing — `in` applies nothing. A later
`with K` treats it as a carrier, not as a stage.

**Examples.** `circuits.braid` (`hand`, `sum0`, `scale3`, `byHand`, and
the `…Out` observations that call an exit); `prob.braid` (`bothFlipE`,
`coinSndE`, `flipSndE`, `idS`, `thenS`, …); `reified.braid` (`sq5`,
`w5`); `frame.braid` (`column`, `sqOut`, `polyOut`, `wiringOut`);
`lifting.braid` (`report in Notes`); `transformations.braid`
(`namedSq in Names`).

**Refusals.**

```text
`in Ints` names a model of Ring in the base: it has no carrier to build
  — write `with Ints`, or `in Ring` for a template.
`in Opt` names a model of Base — a rewriting of the ambient
  presentation, which is applied, not inhabited.  Write `with Opt`.
`in Same` names a functor, and a functor is applied to a body, not
  inhabited by one.  Write `with Same`.
`in Log` names a resource, and a resource is threaded through a body.
  Write `with Log`.  (Asked before the model the declaration generates:
  a representable fibre's carrier is cancelled, so no def holds one.)
`in Nope` names nothing declared at this point.  `in` takes a THEORY …
  or a MODEL WITH A CARRIER …
`in Funcs`: bad neither builds one of Funcs's carriers — `• ⇒ Arr(a, b)`
  … — nor uses any of Funcs's words, so the clause did nothing: … Take
  the inputs inside the carrier (embed embeds a program), or drop the
  clause and let `with Funcs` transport the def.
```

---

## `transformation`

**What it is.** A **natural transformation** between two models of one
theory — the models are functors out of the presented category, and
this is a map between them.

**Syntax.**

```braid
transformation Len in ListMonoid ⇒ IntSum = len
transformation Value in Fwd(Floats) ⇒ Floats = value, zeroTangent
```

`in` because the head says which **hom-set of Mod(T)** the
transformation is a member of; `⇒` because that is the arrow of every
written type in Braid; `=` gives the body, and `,` lists its
**components** — one word per theory parameter, in the theory's order.

**What the checker does.** `transformationDefs` contributes the
component as a word, both sides of every slot's square, and — where the
theory's evidence allows it — a sampled law per square. For each slot
`s : Σ ⇒ Θ` it builds

```text
A@s ; K(Θ)   =   K(Σ) ; B@s
```

where `K` at a stack is the component **on each wire that is the
theory's parameter** and the identity on the rest. Because the base is
the *free* category on the generators, one square per generator is
complete. `checkTransformation` decides each square: `sameCode` first
(a **proof**, for every input), and where that answers false or cannot
decide, the theory's own `sample` evidence. The verdicts are **stored
on the module**, so `:transformations` reads them rather than deciding
again.

**What `with` does to it.** Nothing: a transformation contributes a
word, and the word is called like any other.

**Examples.** `transformations.braid` (`Len : ListMonoid ⇒ IntSum`,
sampled; `Forget : Names ⇒ Funcs`, four squares — `embed` and `sample`
**proved**, `compose` and `observe` **sampled**, because over stacks the
witness is `Fn⟨ρ ⇒ σ⟩` with ρ open and `ev` of an open wire has no
closed arity);
`autodiff.braid` (`Value : Fwd(Floats) ⇒ Floats` — "AD computes the
right value", all nine proved; `Transpose : Fwd(Floats) ⇒ Rev` —
"forward and reverse are the same linear map", six sampled);
`prob.braid` (`Expect : Mixtures ⇒ Means`).

**Refusals.**

```text
`:` types a slot and nothing else since 2026-09-16: a transformation's
  head says which hom-set of Mod(T) it is a member of — write
  `transformation Name in ModelA ⇒ ModelB = word`
Malformed transformation declaration (want `transformation Name in
  ModelA ⇒ ModelB = word`, or one word per theory parameter in order,
  `= w1, w2`)
transformation N: A and B model different theories: a transformation is
  between two models of ONE theory
transformation N: theory T has N parameter(s) and a natural
  transformation has ONE COMPONENT PER PARAMETER
transformation N: the square for slot 's' does not typecheck (…)
transformation N: the square for slot 's' does not commute at the
  theory's samples
transformation N: the square for slot 's' is FALSE — `sameCode` decides
  the two sides are different programs …
`;` composes; separate components with `,` or a newline
```

---

## the Doctrine

**What it is.** The **built-in theory of the base's own structure** — a
category whose hom-objects range over **stacks**, and the embedding of
the base into it; Hughes' `arr` and `>>>` without his `first`, because
a stage of any width now embeds as itself. It is not declared by anyone
and cannot be: it names the shape a theory must have for its models to
transport.

**Syntax.** `theory T(k(..., ...)[, …]) in Doctrine = …`. The Doctrine
is `theory Doctrine(k(..., ...))` with four slots — the two structural
ones, `compose : k(a, b) k(b, c) ⇒ k(a, c)` and `embed : Fn⟨a ⇒ b⟩ ⇒
k(a, b)`, plus the evidence a law needs, `observe : k(Int, Int) ⇒ Int`
and `sample : • ⇒ k(Int, Int)` — and five laws stated over them
(identity twice, associativity, functoriality of `embed`, and
`embedWide`, which states `embed [f] ; embed [g] = embed [f ; g]` at a
stage that is one wire in and two out and at one that whiskers,
`(_ 1 ; +) _`). `k` is the hom-object, and `a`, `b`, `c` are stacks:
there is no pairing parameter and no strength, because the base's own
`...` does the whiskering **inside the quotation**, before `embed` sees
it. A theory declares as many of the four as it wants, and there are
two levels:

| declared | it licenses |
|---|---|
| `compose` | `in M ; f g ; compose` — carriers built by hand compose. `with M` is refused: *theory `Half` takes Doctrine's `compose` and not its `embed` (`Fn⟨ρ ⇒ σ⟩ ⇒ k(ρ, σ)`) … `in Half` and compose by hand.* |
| `+ embed` | `with M` transports **any** stage, at the width it is written. |

**What the checker does.** `checkExtends` verifies the claim once per
theory, whether or not anything models it: every slot the theory
declares that the Doctrine also declares must be the Doctrine's slot at
the Doctrine's shape (`matchArrow`, a one-way match whose pattern
variables are the Doctrine's slot-local stacks and its constructor
parameter), with `k` instantiated **consistently across every slot**.
The grade is not compared — what a model may *do* is the theory's
business, which is why `Arrow`'s slots may be `=Recursive>`. A theory
that takes the composition and not the embedding is audited for
associativity and for nothing else: exactly what it claimed, since
every other law names `embed`. The Doctrine's **laws are inherited**,
and a model runs an inherited law when it can *state* it — when it
declares every slot the law names.

A theory may declare a **strength of its own**, and one does:
`prob.braid`'s `Prob` has `under : k(a, b) =Recursive> k(c a, c b)`, a
wire `c` riding under the kernel's domain, with no pairing anywhere. It
needs one because a Markov category's **generators** — `flip`,
`uniform`, `condition` — are carriers at a fixed width, and nothing in
the base can widen a carrier. `under` is not a Doctrine slot, so it is
an ordinary slot of that theory: in scope under `in M`, ignored by
transport.

**What `with` does to it.** Nothing directly; it is `transportOf`
reading a model of such a theory that makes `with M` transport.

**Examples.** `circuits.braid` (`Arrow`, `Vault`), `frame.braid`
(`Columns`), `lifting.braid` (`Lifting`), `prob.braid` (`Prob`, whose
five inherited category laws run for all three models before anything
prints), `reified.braid` (`Reflective`),
`transformations.braid` (`Arrow`).

**Refusals.** Those listed under `theory`, plus *`in Doctrine`
declares nothing* when the theory shares no slot with it.

---

## `with` — the application clause

**What it is.** The clause that **applies** things to a def's body.
Every `with` mints a receipt.

**Syntax.** `def NAME [in T] with X₁ X₂ … = body`, left of the `=`,
never in a spine. A **quotation** takes the same clause, introduced by
the same `=`: `[with Fuel = dup ; *]`. In the **REPL** a bare `with X`
line opens an ambient scope over the rest of the session — the one
place it stands alone, because a session has no `def` to hang it on.

The kinds of name it may carry, applied in a fixed order — templates
expand, models rename, resources route, a category model composes,
functors rewrite left to right — so a functor always sees finished
wiring:

| `with X` where X is | what happens | mints | example |
|---|---|---|---|
| a **model** of a base theory | its slot names replace the theory's | `=X>` | `def total with IntSum = fold1` (`theories.braid`) |
| an **applied family** `F(M)` | the member is minted and reads the body | `=F(M)>` (one label) | `def polyD with Fwd(Floats) = poly` (`autodiff.braid`) |
| a model of **`Base`** | its generators are renamed to their images, through quotes and rows | `=X>` | `def poly with Opt = …` (`optimizer.braid`) |
| a **resource** | **transport into the model `resource R` generates, in fused form**: the wire is routed deepest and every stage is padded, which is what `embed [s] ; compose` normalises to at a representable fibre. The header is **optional** — routing is inferred | `=R>`, on the claim's own stage rather than a new one | `def score with Log Counter = …` (`resources.braid`) |
| a **functor** | the routed, renamed body goes to its `Code ⇒ Code` word as `Code`, and what comes back is spliced | `=F>`, plus the word's own labels | `def poly with Fuel Metered = …` (`metered.braid`) |
| **`Recursive`** | the def's own name goes into scope in its own body and the knot is tied (innermost, before every other scope) | `=Recursive>` | `def fac with Recursive = …` (`recursion.braid`) |
| a **model with a carrier**, no `in` | **transport**: stage ↦ `embed`, `;` ↦ `compose` | `=X>` | `def easy with Circuits = add1 ; dbl` (`circuits.braid`) |
| a **model with a carrier**, with `in T` for its theory | **instantiate only**: slot names resolve, the spine stays base composition | `=X>` | `def bothFlipE in Prob with Enum = bothFlip` (`prob.braid`) |

**What the checker does.** `elabHeaders` runs **between parse and
inference** and writes the clause out: a syntactic Term rewrite with
the environment available for arities and resource signatures. The node
never reaches inference. `with` **asserts** a resource claim — the
incoming wires must really be those resources, even when the body never
touches one.

**Routing needs no clause.** A def is routed for a resource when the
scheme of an atom in its body, **alone in its stage**, carries that
resource as its deepest wire on both sides — read from the prefix
scope, which is fixed before the def is touched, so invariant five is
untouched. Callers are routed the same way, transitively, until the
wire meets an **install site** (a written seed) or a **handler** (a
discharge). `with R` stays legal, is exactly what inference does
(routing is idempotent), and is the **override**: it names the scope
where inference only proposes one. Two things are never auto-routed — a
body that names the carrier's constructor or un-constructor (`Log` /
`unLog`) is handling the wire itself, and a stage that writes its own
`_` and `...` around the resource word is threading by hand and says
so. `:t!` prints why a def was routed.

**Refusals.**

```text
`use` is gone since 2026-09-16: applying a model, a resource or a
  functor is a def's HEADER CLAUSE, not a stage — write
  `def <name> with <X> = …` (MANUAL §8)
`with` is a def's header clause, not a stage: it goes left of the `=` …
`with Monoid` names a theory: `with` applies a functor, and a theory is
  not one — write `in Monoid` to make this def a template
`with`: X is named twice
`with`: X is not a resource, model or functor in scope     (REPL)
`with M1 M2`: a clause may name at most one category …
`Recursive` is the built-in recursion marker (MANUAL §8), so
  `with Recursive` cannot name your declaration: rename it
`with Recursive` names the def it heads, and there is no def here: it
  puts a definition's OWN NAME in scope in its own body, so it may only
  be a def's header
Empty definition body: f
a quotation's `with` clause is followed by `=` and then the quoted body:
  `[with Fuel = dup ; *]`
`in` says what a DEF is a morphism of, and a quotation is not a def: a
  quotation applies (`with`) and declares nothing
```

---

## `in` — the membership clause

**What it is.** The clause that says **what a def is**: a morphism of
the category the named thing presents, written in that thing's
vocabulary. It applies nothing, writes no wire and mints no label.

**Syntax.** `def NAME in X … = body` — at most once, before `with`,
left of the `=`. There are exactly **two** kinds of `X`: a **theory**
(the def is a template) and a **model with a carrier** (the def is a
hand-built word of that category). Every other kind is refused by name.

`in` also decides, for a `with` clause naming a Doctrine model, whether
that model **instantiates** or **transports**:

| the def | `with M` does | because |
|---|---|---|
| `def f in T with M = …`, T = M's theory | instantiates | the body is already a morphism of `B[T]`, which composes like the base |
| `def f with M = …`, no `in` | transports | the body is a base program and M is the functor carrying it in |

Never both. The mixed case `in K with K` for one Doctrine model K is
allowed and means *K's own words inline, base stages transported around
them*.

**The pin.** Both of these type, and they are different programs:

```text
def a with Enum = half ; flip ; dup   # a0 =Enum Recursive> Bool Bool
def b in Enum   = flip ; dup          # • =Recursive> Kern(Float, Bool) Kern(Float, Bool)
```

`a` is the Markov copy — one flip, copied, so HH and TT at ½ each
(`prob.braid` §6 prints it). `b` is two kernel *values* side by side,
which is not a kernel at all. Nothing but `in` tells them apart.

**What the checker does.** The clause is consumed where a def is
recorded (`addDef`), so it never reaches elaboration. `inTarget`
resolves the name by kind; `checkKWordShape` checks what `in K`
promised against the arrow that came out.

**Refusals.** `in Recursive` (see the template section), the
`inTarget` messages (see the hand-built section), plus:

```text
`over` is gone since 2026-09-16: saying what a def is a morphism of is a
  def's HEADER CLAUSE, not a stage — write `def <name> in <X> = …`
`in` is a def's header clause, not a stage: it goes left of the `=` …
`in` comes before `with`: a def says what it IS, then what is applied to
  it — `def <name> in <T> with <M> = …`
`in X Y`: a def is ONE thing, so `in` names exactly one theory … `with`
  is the clause that takes a list.
```

---

## `table`

**What it is.** A **CSV read at check time**, turned into a `data`
declaration, a loader and a header word.

**Syntax.** `table Trades = "trades.csv"` — columns and types sniffed
from the file — or `table Sector(ticker: Str, sector: Str, weight:
Float) = "sectors.csv"`, which declares them. Unchanged by the
2026-09-16 rename: a table names a file, and that is a definition.

**What the checker does.** `parseTableLine` reads the head;
`tableBlock` resolves the path **against the importing file's
directory**, reads the header line and the rows at check time, checks
the declared columns against the file's, and splices the generated text
in under the declaration line. It generates exactly two words —
`load<Name>` and `header<Name>` — and one data type; the compiler's own
`@` helpers are unreachable from source.

**What `with` does to it.** Nothing.

**Examples.** `frame.braid` (`Trades` sniffed, `Sector` declared, both
loaded into the `Frame` category).

**Refusals.**

```text
`loadTrades@row` is the compiler's spelling of a table's insides: a
  `table` generates `loadTrades` and `headerTrades`, and those are the
  only words it puts in scope
table: a table can only be declared when the module is loaded from a
  file, and this one was checked without a file context: table Trades
```

---

## receipts

**What it is.** The **label a `with` clause leaves** on the manifest of
everything it elaborated: provenance about how a word was built, not a
claim its author made.

**Syntax.** None — you cannot write one. Internally it is a word
`with@F : ∀ρ. ρ =F> ρ`, a unit endomorphism prepended to the expansion;
it costs nothing at run time, whiskers at any width, and is visible in
reflected code:

```text
with@Ticked >> dup >> "tick" pass >> print pass >> + >> "tick" pass >> print pass
```

(`traced.braid`, printed).

**What the checker does.** `receiptScheme` gives it its type;
`elabHeaders` mints it **unconditionally** for every `with`, because a
functor that leaves no receipt cannot be audited; and the same walk
refuses `@` in source, which is what makes a label evidence. The one
scope that does not mint is a model's own component — the `with I`
wrapping a slot body resolves names, it does not apply the model to
itself. `in` mints nothing, ever: a hand-built morphism is by
definition not in the functor's image, and `=K>` on it would over-claim
in exactly the gap between "went through F" and "is in the image of F".

**Examples.** Every labelled arrow. `traced.braid` prints one inside
reflected code and uses it as an `evalAs` witness; `theories.braid`
shows `=IntSum>` distinguishing two instantiations of one template;
`autodiff.braid` shows `=Fwd(Fwd(Floats))>` as **one** label.

**Refusals.**

```text
with@Ticked is the receipt of `with Ticked`, not a word: a label is
  minted by a scope, never written by hand
`IntSum@op` is the compiler's spelling of a slot: reach it with
  `with IntSum`
```

---

## the reflection words — **not** declarations *(2026-09-16)*

**What they are.** Five **prims**: `typeOfWord : Str ⇒ (TypeRep |
Str)`, `typeOfCode : Code ⇒ (TypeRep | Str)`, `declOf : Str ⇒ (Decl |
Str)`, `showType : TypeRep ⇒ Str` and `envOf : • ⇒ List(Box(Str
TypeRep))`. They belong on this page only to say where they sit: they
**declare nothing, apply nothing and mint nothing**. They are words, and the only
reason they are in the kernel rather than derived is the kernel's own
criterion — they touch the implementation, reading the four tables the
checker holds (the environment, the `data`/`resource` declarations, the
`type` aliases and the theories) exactly as `print` touches the world.

**What they answer with.** `data TypeRep` and `data Decl`, declared in
the prelude beside `data Atom`, for the same reason: a prim's scheme
has to point at something. `TypeRep` mirrors `Ty`/`SType`/`EffRow`/
`Arrow` in nine alternatives — the last two being a repeated closed
**segment** with its width (`Aⁿ`) and **`Fin`** at a width, whose widths
are a `WidthRep` and not a type; `Decl` is a `data` (name, parameters,
body, **field names**), a `type` (name, parameters, body) or a `theory`
(name, parameters, slots, law names). A `resource` reflects as the
`data` it is; a `table` reflects as the `data` declaration it wrote.

**Why this is not a new declaration layer.** Every construct on this
page is a *claim* the checker audits. These three are the opposite
direction: they hand a program what the checker already decided. So
there is nothing to check, nothing to mint, and no clause to write —
and a `functor` may call them, which is what makes an
**elaboration-time derivation** an ordinary Braid word rather than a
construct of its own (`cellsFor`, the prelude; `examples/frame.braid`).

**What is not reflected, and why.**

| not reflected | why |
|---|---|
| `model`, `transformation`, `functor`, `resource`'s routing (and the model it generates) | nothing has asked; each needs a rep of its own and none of them is a function of the *declaration* alone |
| a template (`def f in T`) | it has no type until a model reads it, so `typeOfWord` has nothing to answer |

**The width tier has its own sort** *(2026-09-16)*. `Aⁿ` is a stack
SEGMENT repeated n times, so its rep stands in a `StackRep` beside the
open end rather than being a wire, and the width beside it is a
`WidthRep` — `lit k`, or `var n k` for `n+k`. A width is a second sort
and keeping it one is the whole point: a CONCRETE width reflects
expanded, because the checker itself expands it (`Int³` *is* three
wires), and a VARIABLE width is never flattened, or `a0ⁿ⁰` and `a0ᵐ⁰`
would be one type. `typeOfWord "pack"` answers now, and so do `zipN`,
`mapN`, `checkedAt` and `indicesN`.

**Refusals.** None of their own: `typeOfWord`, `typeOfCode` and
`declOf` are total, and put the checker's own message on the **miss
track** — "there is no such word" is an answer, not a failure.
`showType` is the one that can fail, and only on a rep nobody built.

**Where a derivation goes.** A `functor` may call all five, so a def
whose body names a declaration can elaborate into the program that
declaration implies (`examples/typerep.braid` §4). What such a
derivation cannot do yet is **declare** anything: the scope that runs
the functor mints a receipt, so the derived word wears `=F>` and no
longer fits an `Fn⟨a ⇒ b⟩`. A declaration form whose body is computed
is what is missing, and it is the one construct this page expects to
gain (`design-macros.md`, 2026-09-16).

---

## The same thing said four ways

A model is **a presentation interpreted in a category, given by an
object map and an image for each generator.** The four kinds are four
readings of that one sentence:

| kind | object map | generator images |
|---|---|---|
| `model Opt in Base = dupInt = dup, …` | the **identity** | a table, **partial** — every generator it does not name maps to itself |
| a plain model (`model IntSum in Monoid(Int)`) | the theory's parameters, instantiated at this model's arguments | one program per slot, total over the theory's generators |
| a Doctrine model (`model Circuits in Arrow(Circuit)`) | the identity on base types, with `embed` **total** — every base program has an image | the theory's slots, and `;` goes to `compose` |
| a family (`model Fwd(Smooth(a, _)) in Smooth(Dual(a), a)`) | a type-level **substitution**, `a ↦ Dual(a)` | written over the **parameter's** words, not the base's |

A written **object map** is the first row's map made explicit, and the
head already has a clause reserved for it (`inObjMap`, empty today):
`model FwdAD in Base(Float ↦ Dual)`. When it arrives, all four are one
declaration read four ways and nothing that exists has to move.

---

## What is NOT a construct, and why

| retired | when | what it is now |
|---|---|---|
| `instance` | 2026-09-13 | `model` — it fills a theory's slots, and "instance" is a typeclass word for a thing that is not a typeclass |
| `mode` | 2026-09-13 | nothing: a model whose theory has a hom-object transports when it is **applied**, so the model IS the declaration. Write `with M` where `mode` was entered, and `in M` to build one of its morphisms by hand |
| `rules` | 2026-09-13 | `model Name in Base = p = q, …` — a rule set is a **partial model of the ambient presentation**, which is a model |
| `morphism` | 2026-09-14 | `transformation` — a map between two models of a theory is a **natural transformation** between the functors they are |
| `over` | 2026-09-16 | the `in` clause. It was a preposition doing a verb's job, it lived in the body where a scope is not a stage, and losing a block body silently lost the whole scope |
| `use` | 2026-09-16 | the `with` clause. It named nothing about what was applied to what, it took "the rest of the enclosing scope" as its body, and a header clause has no body to lose |

Each is refused **by name**, with the replacement spelled out, rather
than failing as an unknown word.

---

## Where to read more

| topic | MANUAL |
|---|---|
| labels, grades and receipts | §3 |
| why the header clauses are not in the "must end its stage" family | §4 |
| quotations, the header clauses, resources, rows | §6 |
| theories, models, templates, transformations, families, tables, modules | §8 |
| `Code`, functors, `sameCode`, splicing | §12 |
| every refusal class, with an example of each | §14 |
| what to reach for when the language is missing something | §15 |
| the decisions and what they cost | `design-macros.md` (dated amendments) |
