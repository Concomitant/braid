# Braid

A strongly typed, concatenative, stack-based language — a textual
syntax for cartesian string diagrams. Programs are wiring diagrams:
juxtaposition is parallel wires, `>>` (or `;`, or a newline) is
composition, and the type system infers a principal type for every
diagram with no annotations, ever.

The design bet: keep the primitive set tiny (**58 morphisms**, counted
2026-09-14) and prove it spans everything else **in the language
itself**. A word keeps its place in the kernel only if it is a
structure map of the doctrine — cartesian, coproduct, exponential — or
if it touches the implementation (arithmetic, io, reflection) — which
is why the eleven `Float` words of 2026-09-14 are prims and
`fneg`/`fabs` are not: a double is a machine number, negation is `0.0`
minus. The entire
standard library is derived user code: `id`, booleans, three of the four
comparisons, iteration (`loop` and `fix` are both derived under the
`use Recursive` marker), `while` and `until`, the list type and
its library, the sum monad, conditionals and guard ladders, data-type
folds — and the metaprogramming layer, where reflected code is a list
you munge with the same library.

```text
# scores travel as a bare bundle; the syllabus is a dot product;
# the letter is a decision ladder; fairness is a law you can run
def dot = zipN ; [(acc a b -> (a b ; *) acc ; +)] 0 ... ; foldExp2

def letter =
    p ->
    (89 p ; less) "A" ...
    (79 p ; less) "B" ...
    (69 p ; less) "C" ...
    "F"               ...
    decide

95 90 95 ; weighted ; letter ; print     # A — and dot : Intⁿ Intⁿ ⇒ Int
                                         # was inferred, not written
```

## Install and run

**Prebuilt binary** (Linux x86_64, macOS arm64/x86_64) from
[Releases](https://github.com/Concomitant/braid/releases):

```sh
tar xzf braid-*.tar.gz && ./braid examples/registrar.braid && ./braid
```

**No install at all** — clone and use the `./braid` script, which keeps
the toolchain in a container and the sources here:

```sh
./braid examples/registrar.braid   # run a file
./braid                            # open the REPL
./braid - <<'EOF'                  # run a program on stdin
95 90 95 ; grade ; print
EOF
```

Only the first run pays for compiling. A release binary unpacked over
the script keeps the same interface, so `./braid file.braid` means the
same thing either way.

**From source**: `cabal build exe:braid` with GHC ≥ 9.4.

`braid <file>` runs a file; `braid` alone opens the REPL:

```text
braid> :t true
true : • ⇒ Bool
braid> :t dupN
dupN : a0ⁿ⁰ ⇒ a0ⁿ⁰ a0ⁿ⁰
braid> 7 >> [_ 100 >> less?] [2 _ >> *] ... >> while
stack: 112  :  Int
braid> :doc decide
## fold a product of decisions accumulated line by line with `...`
```

`:t` shows a type (`:t!` raw, un-folded); `:doc` and `:defs` browse
the prelude; `:transformations` lists every declared transformation
with the verdict on each of its squares; every REPL line runs against a
persistent typed stack. A
bare `use Log` line opens an ambient scope over the rest of the
session — the resource threads itself through every later line, and a
bare `use` leaves.

## A tour, in sixteen ideas

1. **Everything exact.** Constants are maps from nothing (`1 : • ⇒
   Int`), operations consume exactly their inputs (`+ : Int Int ⇒
   Int`). Passing other wires along is always explicit: `1 ... >> +`
   is increment. No implicit anything — this is what keeps inference
   principal.
2. **Sums are alternate flows.** `(Int | Str)` is one wire carrying
   either. Rows `(f | g)` run one branch; `alt1`…`altN` tag; `merge`
   rejoins; `assocL` / `assocR` re-nest; `case3` folds a whole nested
   sum at once. Bool is just `(• | •)`. A row has **two tails**: `...`
   continues a track's wires, `---` continues the alternatives — so
   `(f | ---)` acts on the first alternative and passes every other one,
   named or not, and `into` peels one alternative off a row nobody has
   to have written down.
3. **Predicates are routers.** `odd? : Int ⇒ (Int | Int)` *routes*
   its input instead of returning a detached boolean — branches
   receive the data. Drop the `?` to forget instead: `odd : Int ⇒
   Bool`.
4. **Failure is a track.** `>=>` composes hit-tracks and lets misses
   fall through; `>?>` chains along the miss track (it *is* elif);
   `readFile` and `parse` are railway stages too. None of them are
   primitive: each is `>> (stage | alt1/alt2) >> merge`, bundled.
5. **Names label wires; they don't cut them.** `x y ->` consumes the
   wires it names, so the body re-pushes them. `-> x y` instead tags
   them as they go by — identity at runtime, wires flowing on, names in
   scope for the rest of the block, the way a label sits beside a wire
   in a drawn diagram. The arrow's side is the whole rule. It is sugar,
   not machinery: `-> x y z` *is* `x y z ... -> x y z ...`, and
   `reflect` compiles it back to dup/swap/drop to prove it — and, for a
   name a quotation or a row branch closed over, to `curry`/`ev`, the
   exponential's two maps. Closures are wiring too, so `reflect` is
   total on binder code and `use Traced` over a `use Recursive` def works.
6. **Guard ladders are ordinary words.** Bind the subject and a guard
   is a bare Bool beside its answer; `...` accumulates one lane per
   line and `decide` folds the product — first true lane wins:
   ```text
   x ->
   (x >> negative) "neg"  ...
   (x >> zero)     "zero" ...
   (x >> toStr)           ...
   decide
   ```
   Guards-as-data variants (`firstTrue`, clause ladders + `choose`,
   `if`/`elif`/`else` fold-as-you-go) are all prelude defs. No guard
   syntax exists in the parser.
7. **Loops are values, and so is the knot.** Write `use Recursive` in a
   def's header to put the def's own name in scope in its own body.
   Elaboration rewrites the body to the closed form so the def is still a
   closed spine; `Recursive` is the receipt that scope mints. `fix` and
   `loop` are ordinary prelude defs written under the marker, as are
   `while` and `until`. A word without `Recursive` ties no knot and
   terminates by construction; an unmarked self-reference is refused with
   a message that names the marker (MANUAL §8).
8. **Data types are declared sums.** `data Tree(a) = (a | Tree(a)
   Tree(a))` — the name rolls, `unTree` unrolls (both free at
   runtime), and `foldTree` is *generated*: elimination by points — a
   structural recursor: it descends on a smaller value, so it
   terminates by construction, needs no knot, and mints no `Recursive`.
9. **The list defines itself.** `type List(a) = (• | a List(a))` in
   the prelude; literals, `map`, `fold`, `filter` are all derived. A
   cell is one wire — declaration parameters are kinded, a bare name
   being a wire and `...` a whole stack — so a pair-list is
   `List(Box(a b))` and the *whole* library works on it, not just
   `fold`. Keeping stack variables in tail position is what makes the
   type system's tail-only invariant true rather than aspirational.
10. **Widths are exponents.** `Intⁿ` (typed `Int^n`) is n wires — a
    vector with no box, an exponential object with finite base. One
    fold word is variadic over bare stack products (`sumN : Intⁿ ⇒
    Int`); `mapN`/`mapN2` lift any ordinary word pointwise, so the GLA
    generators are *derived* (`def addN = zipN ; [+] ... ; mapN2`); a
    matrix is a value `Fn⟨Intⁿ ⇒ Intᵐ⟩`; and a 3-weight syllabus cannot
    meet a 4-score transcript — dimension errors are type errors. `n`
    is erased: the running stack's width is its own witness. And `Aⁿ`
    *is* the function space `Fin(n) → A` kept tabulated, so indices are
    first-class and bounds-checked by the type (`at`, `indicesN`,
    `checkedAt`) — each one witnessed by a live bundle or a literal's
    own offset (`examples/index.braid`).
11. **Laws are programs.** Associativity, De Morgan, dot-product
    symmetry, the copy/add bialgebra — they run as code
    (`examples/laws.braid`, `gla.braid`, `registrar.braid`), and
    they're operational: a checked law is a license to rewrite
    (contrapose a chain, parallelize a fold, flip a weighting).

    Laws now have a front door. A **theory** declares named slots and
    the laws they must satisfy; an **model** supplies programs and
    is *audited* by running them — at module start, before main, so a
    failing model is not a model and the module is rejected:
    ```text
    theory Monoid(a) =
        unit   : • ⇒ a
        op     : a a ⇒ a
        sample : • ⇒ a
        law leftUnit = (sample ; unit ... ; op) sample ; eq? ; (forget ; true | forget ; false) ; merge

    model IntSum : Monoid(Int) =
        unit   = 0
        op     = +
        sample = 7

    def total = use IntSum ; [op] unit ... ; foldExp     # Intⁿ⁰ =IntSum> Int
    ```
    This is not typeclasses: nothing is inferred and nothing is
    dispatched. `use IntSum` picks a model **by name**, and the
    pick is a renaming at elaboration — once per scope, no dictionary
    per call. The trade is deliberate: you give up inferring *which*
    model, and keep annotation-freeness, coherence in a structural
    type system, and freedom from higher kinds. The audit is
    signatures, completeness, and laws typed `• ⇒ Bool`; the honest
    limit is that a law runs on the samples it names — property
    testing's poor cousin, minus generation and shrinking, plus being
    part of what it *means* to be a model
    (`examples/theories.braid`). A theory parameter may also be a type
    **constructor** — `theory Arrow(k(_, _))`, with slots like
    `compose : k(a, b) k(b, c) ⇒ k(a, c)` — which is enough to state the
    Arrow interface once and audit circuits and functions against it
    (`examples/circuits.braid`). That is still not higher kinds: `k`
    lives in the signature, the model head names a declared data
    type, and the substitution happens before inference ever runs.
    The **prelude** declares that interface once and for all as
    `theory Doctrine(k(_, _), p(_, _))` — `compose`, `embed`, `first`,
    and the seven arrow laws — and a theory joins it by writing
    `over Doctrine` and declaring its operations. That declaration is
    what makes `use M` *transport* a whole block into the category,
    and how much it declares is the level: composition alone composes
    by hand, `+ embed` carries one-wire stages, `+ first` carries any
    stage. The laws are inherited and run at model check, so
    `examples/circuits.braid` and `examples/reified.braid` — a
    stateful circuit and a program paired with its own `Code` — are
    audited against the same seven.

    Two models of one theory have **transformations** between them:
    `transformation Len : ListMonoid ⇒ IntSum = len` says `len` is a
    homomorphism, and the elaborator generates one naturality square
    per slot and *decides* it — proved by `sameCode` where the
    normalizer reaches, sampled at the theory's own `sample` slot where
    it does not, and refused, naming the slot, where it can do neither.
    When the two models are models of a theory that extends `Doctrine`,
    that is an **internal functor**, and the squares are functoriality
    (`examples/transformations.braid`).

    A body can be written **once over the theory**. Two header words
    say which side you are on: **`over X` declares** that this def is a
    morphism of X, and **`use X` applies** X to the block that follows
    — *what follows is written in the domain of X, and X is applied to
    it*. So a def headed `over Monoid` is a **template**, and a def
    headed `use IntSum` expands it there and re-infers it there:
    `def fold1 = over Monoid ; [op] unit ... ; foldExp` becomes
    `Intⁿ⁰ =IntSum> Int` under `use IntSum` and `Strⁿ⁰ =StrCat> Str`
    under `use StrCat`, each with its own
    principal type and nothing passed at run time. It is ML's functor
    application spelled as scope: no new syntax, no parameter list, and
    a template called outside every model scope is an error naming
    the theory (`examples/build.braid`). Models of base theories point
    *into* the base; a model with a carrier, a resource and a functor
    point *out* of it; `over` is the only way to declare membership and
    `use` the only way to apply a functor.

    Laws about *functors* are the same idea one level up. A functor's
    output is `Code`, so `sameCodeC : Code Code ⇒ Bool` states them —
    functoriality, identity preservation, the interaction of two
    functors, and **idempotence**, `F(F p) = F p`, which is what makes
    an optimizer an optimizer. Idempotence is a functor law and belongs
    to a theory; *image membership*, `F(p) = p`, is a claim about one
    particular program and is written beside that program — the two are
    kept apart because the second only means anything when the first
    holds (`examples/optimizer.braid`).
12. **Effects are wires.** State, logs, readers, exceptions,
    nondeterminism — the whole effect zoo decomposes into structure
    the language already has: a threaded wire, a captured closure, the
    railway sum, a list. Only IO is irreducible, so `IO` is the one
    label the effect zoo ever needs — an arrow carrying it prints
    `=IO>`, a pure one `⇒`, and the label sits on the arrow just like
    resource names do. The manifest is a SET, though: a functor scope
    mints its own label onto everything it rewrote (item 14), and
    `=IO Traced>` is an ordinary type. `Recursive` (item 7) is the second
    built-in member: the `use Recursive` scope mints it, and `fix` and
    `loop` (written under that marker) carry it; structural recursors
    (and so `fold`, `map`, `filter`) do not — so **knot-free pure code
    terminates by construction**, and an unlabelled written type
    refuses recursive code exactly as it refuses io. Which labels you get is
    **inferred, never annotated**: four prims are marked
    (`print`, `readLine`, `readFile`, `writeFile`) and every
    other grade follows from composition, which **joins** the labels
    rather than forcing them equal, so a part is never asked for the
    composite's labels — `def shout = toStr >> print : a0 =IO> •`,
    while `loop : Fn⟨ρ0 ⇒ (ρ0 | ρ1)⟩ ρ0 =Recursive> ρ1` recurses without
    asking its body to.
    Quoting stays pure, since pushing an action isn't doing it:
    `[print] : • ⇒ Fn⟨a0 =IO> •⟩`, and `ev` is what transfers the grade out.

    The other wires you can *name*: `resource Log = Str` declares a
    threaded wire — nominal, so `Int Int` is never silently a
    GameState, and one wire however wide its contents. A run of them
    shared by both sides of an arrow folds onto the arrow, grade
    included: `note : Str =Log> •`, `peek : • =IO Log> •`. And `use`
    makes the threading disappear — it opens a scope over its
    resources, taking the rest of the block as its body, and an
    elaborator writes every `_` and `...` for you:
    ```text
    def score =
        use Log Counter
        dup ; *
        bump
        "scored "
        note                # Int ρ0 =Log Counter> Int ρ0
    ```
    Nothing there is compiler magic you couldn't write: what `use` does
    to a pure stage is `lift : Fn⟨ρ0 ⇒ ρ1⟩ ⇒ Fn⟨a0 ρ0 ⇒ a0 ρ1⟩`, an
    ordinary prelude word (tensorial strength — run a program one wire
    deeper). It only saves you the counting (`examples/resources.braid`
    shows both spellings side by side). Scopes compose: a word threading
    exactly its scope's resources is callable from that scope, so a
    resourceful step is an ordinary fold's step function and a whole
    stateful pass over data is `[step] seed ... ; fold`
    (`examples/payroll.braid`).
13. **Code is data.** `reflect` turns a quotation into its spine — a
    list of stages of atoms — so `take`/`map`/`reverse` slice and
    transform *programs*; `evalAs` runs them (witness-checked: the loaded
    code must subsume an ordinary program whose arrow is the expected type);
    `unparse`/`parse` and `readFile`/`writeFile` round-trip code
    through disk. The graphical-linear-algebra transpose is
    `reverse >> map dualize`.
14. **Elaboration is a library.** A `functor` is any pure `Code ⇒
    Code` word, and `use Traced` applies it to a scope's wiring at
    elaboration; the expansion is re-inferred, never trusted. One
    functor is *checked* rather than re-inferred: `interpose` inserts a
    stage after every cut and admits only stages that read no wire
    (`ρ ⇒ ρ`, or `E ρ ⇒ E ρ` over a resource) — so metering a resource
    is one line, and the tracer that lifts everywhere is a marker, not
    a probe. `lift2` applies any such functor at run time with the
    program as its own witness and fallback.

    **Every `use` leaves a receipt**, and only a `use` mints one:
    `use IntSum` puts `IntSum` on the manifest of everything it read,
    `use Traced` puts `Traced` on everything it rewrote
    (`poly : Int =Traced> Int`), so the type says which models and
    which functors built a word and every caller inherits it. Written
    by hand a receipt is an error, which is what makes it evidence.
    `over` mints nothing — it applies nothing.

    An **model of `Base`** is the declared, once-checked rewrite:
    `Base` is the ambient presentation — every word in scope, its own
    scheme as the slot's declared type — and `model Opt : Base =
    dupInt = dup, twice = double` is a *partial* model of it, the
    generators it names reinterpreted and every other mapped to itself.
    Each binding is blessed where it is written, by *subsumption* —
    `q` may stand wherever `p` stands iff `scheme(q) ≥ scheme(p)`, a
    rank-2 statement no `Fn` type can hold, which is why it is a
    declaration and not a word. *Unification blesses a call;
    subsumption blesses a rule.* The renaming reaches through
    quotations, rows and `fix` bodies, and `use Opt` mints `=Opt>` —
    an optimizer you can audit rather than one you have to trust. (An
    model of `Base` whose images are *provably equal* to the
    generators is an optimizer; one whose images merely satisfy the
    laws is a dialect — `examples/optimizer.braid` draws that line.)

    **Transport** is the same mechanism pointed at composition itself,
    and it needs no keyword of its own. When a model's theory has a
    hom-object (`theory Arrow(k(_, _))`) and declares slots at the
    composition and embedding *shapes* — `k(a,b) k(b,c) ⇒ k(a,c)` and
    `Fn⟨a ⇒ b⟩ ⇒ k(a,b)`, read off the written types, never off a slot's
    name — then `use Circuits ; add1 ; dbl` elaborates every stage to
    that model's embedding and every `;` to its composition, so a block
    reads as the ordinary program it is and comes out a circuit. A third
    shape, the **strength** `k(a,b) ⇒ k(P(a,c), P(b,c))`, names the
    pairing that packs a wider stage, so `use Circuits ; dup ; *` is a
    circuit that squares: `_`-padding with `first` in place of `_`.
    That shape rule is the base's own doctrine — a Freyd category,
    Hughes' `arr`/`>>>`/`first` — made declarable, so "a target must
    have the structure the source has" is checked rather than assumed.
    The receipt is an ordinary label with a *carrier* — at the base the
    word is `• ⇒ Circuit(Int, Int)` carrying `Circuits`, and the display
    folds the two into `Int =Circuits Recursive> Int`. Entering is a marker,
    leaving is a model: the theory's eliminators are refused inside the
    scope, which makes a theory with no eliminator a **sealed**
    category — abstract types for free. A morphism that is not the
    transport of any base program — a stateful circuit, say — is
    declared instead of transported: `def sum0 = over Circuits ; 0 ;
    sumFrom`, recognized by its carrier, and it composes under `use
    Circuits` like any other (`examples/circuits.braid`).

    `Code ⇒ Code` functors come **last** in that list on purpose. The
    rungs above are by generators, checked once, free at every use; the
    `functor` keyword names the non-tabular case — a program on syntax,
    re-inferred at the splice — and it is the escape hatch, not the
    front door.
15. **A file is a presentation, an import is the inclusion.**
    `import "geometry.braid"` puts one file's declarations — defs,
    types, resources, theories, models (including models of
    `Base`) and functors — in another file's
    scope. Objects are added, never merged: a clash is an error naming
    both files, a diamond includes the shared file once, a cycle is
    reported. What does not travel is the imported file's main program,
    so a library keeps its own demo. Nothing needed machinery of its
    own; the composite is checked as a single module.
16. **Differentiation is a model.** Not a library, not a macro, not a
    `Code ⇒ Code` pass. Differentiation is a functor into pairs of a
    value and a linear map (Elliott), a model of a theory *is* a
    functor out of the free category on that theory's generators —
    so writing arithmetic as a `theory` and AD as a `model` of it
    leaves the chain rule with nothing to do. It appears nowhere in
    `examples/autodiff.braid`. What appears instead is one slot per
    generator, each saying what the derivative of that **one**
    operation is; composition is the language's.
    ```text
    theory Smooth(a) = add : a a ⇒ a ; mul : a a ⇒ a ; … ; observe : a ⇒ Float

    def dmul = unDual _ ; _ _ unDual
             ; (a da b db -> (a b ; fmul) ((a db ; fmul) (da b ; fmul) ; fadd) ; Dual)

    def poly = over Smooth ; (x -> …)      # written once
    def polyD = use Fwd ; poly             # Dual =Fwd> Dual
    ```
    Three models of the one theory: `Floats` evaluates, `Fwd` carries a
    tangent (forward mode), `Rev` carries the **transpose** of that same
    linear map as a continuation (reverse mode) — so forward and reverse
    are two representations of one map rather than two algorithms, and
    fan-out needs no special case because continuations are linear.
    `transformation Value : Fwd ⇒ Floats = value, zeroTangent` says *AD
    computes the right value*, and all nine of its squares are
    **proved**, not sampled.  The theory's gradient exit is
    `gradient : a ⇒ g` — an exit whose result varies by model is a
    theory **parameter**, filled `Float` by `Fwd` and `Grad` by `Rev` —
    so a transformation carries one component per parameter and
    `Transpose`'s gradient square is decided like any other.
    Newton's method comes along under `use Recursive`, and a fourth
    model threads the adjoint through a `resource` instead of summing
    it. `Float` itself arrived for this (a base type beside `Int`,
    sharing no word with it), and the file says plainly what is not
    built: second derivatives want a model parameterized by a model.

## Examples

`examples/` is the guided tour: start with `fizzbuzz`, `validate`
(railway), `ladder` (every guard idiom), `iterate` (while), then `nat`
and `tree` (data types and folds), `lists`, `conditionals` and `case`
(rows, deferred sums, `case3`), `tag` (naming wires in passing),
`resources` (threaded wires and `use`),
`lifting` (every functor is `Fn⟨a ⇒ b⟩ ⇒ something better`:
the logged version of a function, game rules as lifted moves),
`index` (Fin(n) and a small dataframe),
`sniff` (typed CSV-cell refinement), `sac` (split-apply-combine),
`laws`, `theories` (theories, models, laws that run),
`build` (one pipeline as a template, instantiated by two configurations),
`arrows` (Control.Arrow's interface, as plain syntax), `circuits`
(the arrows that aren't: stream transducers as ordinary data, and the
`over Doctrine` declaration that transports base programs into them),
`reified` (the same doctrine over a carrier that is the program AND its
Code — `getCode` and `evalAs` as one model's embedding and exit) and
`transformations` (a natural transformation between two models, its
squares generated and decided — proved for an internal functor, sampled for a fold),
`payroll` (a whole small program: a resource, a theory and a grade
meeting in one pass over data),
`parallel`, `matrices`, `gla` (bundles and the bialgebra),
`code`, `transpose`, `io`, `witness` (the program as its own witness),
`traced` and `metered` (functors: a tracer that lifts at every cut,
a resource metered by one checked interposition),
`autodiff` (the flagship: automatic differentiation as three models of
one theory of arithmetic — no `Code`, no chain rule),
`imports` (one file's declarations in another file's scope) — and finish with
`registrar`, which uses most of the language in forty lines about
grade school.

## Extending it

There is **one arrow** — no `Arrow` class, no `Monad`, no higher kinds —
so "a new kind of computation" is never a new arrow. It is a `data`
(a new carrier, codata included), a `resource` (state threaded through a
region), a plain `def` (a new combinator — loops and guards are already
values), a `theory` + `model` (a swappable interface with runnable
laws), or, for a genuinely different category like a stream transducer,
a `data` plus your own composition word. MANUAL §15 is the table, with a
worked example for each row.

## Status

A design-driven prototype: one Haskell module for the whole language
(typechecker, interpreter, REPL), a 1072-case test suite, a full
reference (`MANUAL.md` — every feature, with checker-verified types),
and design notes recording each decision and the theorems that forced
it —
`expanded-spec.md`, `spec-sums.md`, `spec-code.md`,
`design-control-flow.md` (why guard syntax kept getting built and torn
out, and what replaced it), `design-exponents.md` (dimension-indexed
segments: why exponents not stars, why unary successors suffice, why
the eliminator is a fold and not an unroll), and `design-macros.md`
(elaboration as a library: functors over `Code`, the five invariants,
and the transport of `⇒` into other categories). `READING.md` is the
annotated bibliography behind all of them. Deliberately absent so
far: labeled record fields, totality checking (`Recursive` marks
what *may* recurse without bound — provenance, not a proof), and the
last stage of the effects staging —
`resource` wires, `use` scopes, and theories/models with runnable
laws have shipped, but there is no resource mark, no linear `World`
and no handlers (`design-effects.md` has the position, the staging,
and the two decisions implementation reversed).
