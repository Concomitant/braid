# Design note: flexible arity — the map of the territory (CONVERGED)

Consolidates the 2026-08-19…22 discussions (splice removal, sandwich
proposals, literature audit). Status: design position. The unifier is
at a known optimum; this note records why, and the three priced routes
beyond it.

## The invariant, named

Braid's stack types are Kutsia's **sequence unification** restricted to
the tame fragment: sequence variables (ρ, and width-open exponents) in
**last position only**. General sequence unification is decidable but
INFINITARY; the last-position restriction is the fragment the
literature identifies as finitary-unification / unitary-matching.
Braid stays fully unitary by anchoring BOTH sides of every equation at
the tail. Tail-only is not a house idiosyncrasy — it is the published
boundary, and every relaxation we probed lands outside it.

## Experiments run (all in-session, 08-19…22)

- **One region, any position** (= the splice, `P ρ S`). Unitary against
  ground stacks (arithmetic fixes the cut). NON-unitary under
  composition: `ρ Int ~ Int σ` has two incomparable MGUs (overlap
  `ρ=σ=•` vs bridge `ρ:=Int b, σ:=b Int`). spliceSplit implemented only
  the bridge — the documented "sound, not complete", and the cause of
  the `1 ... >> rotLast` empty-stack rejection. Deleted 08-20 (b474973).
- **Same variable both sides**: `ρ Int ~ Int ρ` has solution set
  {Intᵏ} — infinitely many incomparable; the textbook witness that
  A-unification is infinitary. (Amusingly ρ := Intⁿ captures exactly
  this family — the exponent sort is a parametric-solution language for
  the same-var case, which is what expSplit's linear chain exploits.)
- **Variable flanks** (`ρ a ~ b σ`): worse, not better — variables make
  every alignment consistent, so the full set of incomparable solutions
  survives every time. The multiplicity is positional (an unknown
  integer), and substitutions cannot express arithmetic choice.
- **Rigid sandwich** (`a ρ b ~ c σ d`, same template both sides):
  genuinely unitary — both region-ends pinned at identical offsets, no
  case split. But the template is not closed under the language's own
  algebra: tensor assembly manufactures (2,1)- and (1,2)-forms, whose
  cross-unification is ambiguous again and whose solutions need
  splice-shaped bindings (`ρ := ρ' d`). Also: minimum width 2 kills
  `pass`/`forget`/n=0. Unitary but not compositional.
- **Zero-width closure** (5c9b64f): non-final open words close
  (ρ := •, n := 0) as an instantiation policy — position decides before
  unification runs, so principality is untouched. The placement error
  survives only where closure is impossible (recursive calls: the open
  tail is the def's own monomorphic variable) or a silent lie (`...`,
  open binders: a vacuous remainder marker). `pass` non-final is the
  honest spelling of the closed reading.

## The anchoring principle

An anchor is sustainable exactly where the algebra never disturbs it.
Braid's remainder rides on TOP and stage pushes go UNDERNEATH, so the
top is the operation-invariant end — hence tail-only. A SECOND anchor
is sound iff nothing is ever inserted on its far side: that is the
effects design's linear World wire, pinned deepest forever
(design-effects.md; Clean/Mercury precedent). Fixed-offset anchors
anywhere else are destroyed by the first tensor stage.

Rigid same-template unification being unitary is general (no alignment
freedom); the question is never the template, it is closure under
append/instantiate/bind. {closed prefix ++ tail} is closed under all
three; that is the whole theorem.

## The three routes beyond, priced

1. **Width arithmetic** (n+m, n·m, reshape — design-exponents Level 2).
   Kennedy's units-of-measure: abelian-group unification over ℤ,
   principal types, composes with HM, shipped (F# 2.0). Widths differ
   from units in one way: no negatives — so the AG solution carries a
   non-negativity residue, i.e. DML-style index constraints discharged
   by a linear-arithmetic solver. Cost: `:t` output grows side
   conditions. License: the laws of exponents (A^(n+m) ≅ Aⁿ Aᵐ,
   A^(n·m) ≅ (Aⁿ)ᵐ) — index-type algebra, not ad-hoc type math.
2. **Mid-stack freedom = labels, not position tricks.** Record-row
   systems (Rémy; Leijen scoped labels; Morris–McKinna ROSE) get "one
   variable anywhere" because NAMES anchor what position cannot.
   Commutativity + labels dissolves the arithmetic. This upgrades
   "labeled record fields" from convenience to the only principled
   route to positional freedom.
3. **Value-directed width** (tabulate/Fin(n), unpack, zeroN): the
   intensional half of Aⁿ ≅ Fin(n)→A that erasure forecloses. Needs
   the index type as data — DML/ATS territory. Same qualified-type
   price as (1); do together or not at all.

## Recommendation

Do nothing to the unifier. When Level 2 earns a concrete need, do it
Kennedy-style with the ℕ residue. Count mid-stack pressure as an
argument for record fields, not unfinished stack business. Let the
effects work claim the bottom anchor — it is the one expansion this
theory positively endorses.

## Peer calibration

Kleffner's λc (sequence types + inference), Pöial's Forth stack-effect
calculus, Factor's row-polymorphic checker, Wasm stack polymorphism:
all tail-only-or-weaker, none with a width-indexed bundle tier. On
this axis Braid is past the published systems, not behind them.

## References (checked 2026-08-22)

- T. Kutsia, *Unification with Sequence Variables and Flexible Arity
  Symbols and Its Extension with Pattern-Terms*, AISC/Calculemus 2002
  (general theory infinitary; last-position fragment tame).
- A. Kennedy, *Types for Units-of-Measure: Theory and Practice*, CEFP
  2009; A. Gundry, *Type Inference for Units of Measure*, 2011.
- H. Xi, F. Pfenning, DML (index types, constraint-based inference).
- D. Rémy; D. Leijen (scoped labels); J. G. Morris & J. McKinna, ROSE
  (row theories, ECOOP/POPL lineage).
- R. Kleffner, *A Foundation for Typed Concatenative Languages*, 2017.
- J. Pöial, stack-effect calculi, EuroForth; Wasm stack-polymorphism
  with subtyping, APLAS 2022.
- Makanin; Plandowski; Jeż (word equations: decidable, A infinitary).
