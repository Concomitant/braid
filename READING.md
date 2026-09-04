# Reading list

The papers behind the design notes, organized by which part of Braid
they ground. One line each on why it matters here. Links are to open
copies where they exist.

## Premonoidal categories, arrows, effects

- Power & Robinson, *Premonoidal categories and notions of
  computation* — the state construction `C(E⊗Σ, E⊗Θ)` that every
  resource fiber is; non-interchange is our left-to-right decree.
- Hughes, *Generalising monads to arrows* (2000) and
  [*Programming with Arrows*](https://www.cse.chalmers.se/~rjmh/afp-arrows.pdf)
  — the machinery `examples/arrows.braid` shows is already syntax, and
  the transformer stacking the graded arrow dissolves.
- Atkey, [*What is a Categorical Model of
  Arrows?*](https://bentnib.org/arrows.pdf) — Arrows vs Freyd
  categories, with the two-input caveat.
- Staton, [*Freyd categories are Enriched Lawvere
  Theories*](https://www.cs.ox.ac.uk/people/samuel.staton/papers/freyd-lawvere-2014.pdf)
  — arrows, theories, and effects are one object; why `theory` and the
  effect system kept converging.
- Plotkin & Power, *Notions of Computation Determine Monads* — effects
  are algebraic theories.
- Plotkin & Pretnar, [*Handlers of Algebraic
  Effects*](https://homepages.inf.ed.ac.uk/gdp/publications/Effect_Handlers.pdf)
  — a handler is a model; Braid's instances already are models, so
  discharge is a wrapping functor, not a new construct.

## Grading, coeffects, cost

- Katsumata, *Parametric effect monads and semantics of effect
  systems* (POPL 2014) — grades from an ordered monoid; the `⇒!` row
  is the two-element case.
- Gaboardi, Katsumata, Orchard & Breuvart, [*Combining effects and
  coeffects via
  grading*](https://www.cs.kent.ac.uk/people/staff/dao7/publ/combining-effects-and-coeffects-icfp16.pdf)
  — the effect/coeffect duality and graded distributive laws; the
  functor-interaction-law question lands here.
- Petricek, Orchard & Mycroft, *Coeffect calculus* — what image
  membership and capabilities are (graded comonads, intersection where
  effects union).
- Danielsson, [*Lightweight semiformal time complexity analysis for
  purely functional data
  structures*](https://www.cse.chalmers.se/~nad/publications/danielsson-popl2008.pdf)
  — the tick/`Thunk` monad; the quantitative grade the `a ⇒ a`
  counterpoint argues for.
- [nLab: graded monad](https://ncatlab.org/nlab/show/graded+monad).

## String diagrams, free categories, decidable rewriting

- [nLab: Lawvere theory](https://ncatlab.org/nlab/show/Lawvere+theory)
  and [PROP](https://ncatlab.org/nlab/show/PROP) — what a `theory`
  presents, and why the string-diagram syntax is the SMT one.
- Baez, Coya & Rebro, [*Props in network
  theory*](https://math.ucr.edu/home/baez/prop.pdf) — the
  multi-output generalization.
- Lafont, [*Towards an algebraic theory of Boolean
  circuits*](https://www.i2m.univ-amu.fr/perso/yves.lafont/pub/circuits.pdf)
  — presentations with canonical forms; where `sameCode` grows next.
- Bonchi, Sobociński & Zanasi, [*Interacting Hopf
  Algebras*](https://arxiv.org/abs/1403.7048) — complete axioms for
  linear relations; the GLA fragment's normal forms.

## Metaprogramming and staging

- Sheard & Peyton Jones, *Template metaprogramming for Haskell* — the
  untyped-code-with-checked-splices position `Code` shares.
- Taha et al., MetaML — via [Oleg Kiselyov's staging
  page](https://okmij.org/ftp/meta-programming/index.html): typed code
  forbids intensional analysis, the obstruction that makes `Code` the
  quotient of typed code.
- Moura et al., [*The Lean 4 theorem prover and programming
  language*](https://lean-lang.org/papers/lean4.pdf) and Ullrich &
  de Moura, [*Beyond notations: hygienic macro expansion for theorem
  proving languages*](https://arxiv.org/pdf/2001.10490) — the nearest
  relative for `functor`/`use`, and the hygiene machinery Braid gets
  structurally. Also the community
  [metaprogramming book](https://leanprover-community.github.io/lean4-metaprogramming-book/).
- Jang, Gélineau, Monnier & Pientka, [*Mœbius: metaprogramming using
  contextual types*](https://arxiv.org/pdf/2111.08099) — the price of
  typing AND inspecting code at once; declined.
- Elliott, [*Compiling to
  categories*](http://conal.net/papers/compiling-to-categories/) — the
  transport vision as a GHC plugin; here a user-level word.
- Pestov, Ehrenberg & Groff, [*Factor: a dynamic stack-based
  programming language*](https://factorcode.org/littledan/dls.pdf) —
  `MACRO:` and quotations-as-lists: this design minus types, grades,
  and audits.

## Multimodal type theory (the "every arrow in its own category" direction)

- Gratzer, Kavvos, Nuyts & Birkedal, [*Multimodal Dependent Type
  Theory*](https://dl.acm.org/doi/10.1145/3373718.3394736)
  ([pdf](http://www.danielgratzer.com/papers/multimodal-dependent-type-theory.pdf))
  — judgments indexed by a mode theory (a strict 2-category: modes =
  categories, modalities = functors, 2-cells = laws).
- Gratzer, [*Normalization for multimodal type
  theory*](https://arxiv.org/pdf/2106.01414) — conversion decidable
  when 2-cell equality is; the condition lands on the
  `sameCode`/fragment story.
- Licata & Shulman, [*Adjoint logic with a 2-category of
  modes*](https://dlicata.wescreates.wesleyan.edu/pubs/ls15adjoint/ls15adjoint.pdf),
  and Licata, Shulman & Riley, *A fibrational framework for
  substructural and modal logics* (see also
  [nLab: adjoint logic](https://ncatlab.org/nlab/show/adjoint+logic))
  — per-mode structural rules (linearity as a mode) and crossing by
  adjunctions (install/reify as unit/counit).
- Melliès & Zeilberger, [*Functors are type refinement
  systems*](http://noamz.org/papers/funts.pdf) — a type system IS a
  functor over a category of terms; the Braid picture with `Code` as
  the base.
- Jang & Pientka, [*Polymorphic metaprogramming with memory
  management — an adjoint analysis of
  metaprogramming*](https://arxiv.org/abs/2411.00752) — code and
  programs as modes `C ≥ P`; our phase distinction as a mode preorder.
- [*Semantics of multimodal adjoint type
  theory*](https://arxiv.org/pdf/2303.02572) — the model theory.

## Verified rewriting (where the audited optimizer sits)

- GHC rewrite `RULES` — user rules, trusted; the pole `sameCode`
  improves on.
- Lopes et al., *Alive/Alive2* — verified peephole rules for LLVM; the
  other pole (external logic, full generality).
- Willsey et al., *egg: fast and extensible equality saturation* — the
  upgrade path if rule sets grow.
