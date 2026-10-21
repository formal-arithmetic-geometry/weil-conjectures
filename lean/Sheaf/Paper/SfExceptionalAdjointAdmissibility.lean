/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NP
-/
module

public import Sheaf.Paper.FiniteFieldFiber
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Compactification.Refinement
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Sheaf.Paper.SfDerivedDirectImage
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.AlgebraicGeometry.SfIntrinsicCompactSupport
public import Sheaf.AlgebraicGeometry.SfFullCohomologicalDimension
public import Sheaf.AlgebraicGeometry.IntrinsicConstructibleIntervals
public import Sheaf.Paper.FiniteTorAmplitude
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Exceptional-adjoint admissibility at a finite coefficient stage

Source: Weil blueprint main-20261015, sec-six-functors-basics,
`sk-def-sf-admissible/_section.md`, order 1702 (blueprint: sk-def-sf-admissible).

The ambient condition is only the existence of a full cohomological-dimension bound.
Admissibility additionally requires preservation of bounded constructibility, uniform
signed interval shifts, and finite Tor amplitude by every right adjoint of the candidate
attached to the specified compactification. These are predicates, not automatic hypotheses.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The ambient exceptional right adjoint datum at the positive finite coefficient stage:
a nonnegative FullCD bound for the proper part of the chosen compactification. The
predicate is defined on any compactified morphism; admissibility below restricts it to
the finite-field setting. FullCD quantifies over all source module sheaves and their
restrictions to every pro-etale base change, without a finiteness condition on that
site object. Existence of a right adjoint is a consequence, not an extra defining clause.
Source: main-20261015, `sk-def-sf-admissible/_section.md`, clause (1), order 1702
(blueprint: sk-def-sf-admissible). -/
noncomputable def HasSfAmbientExceptionalDatum
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (n : ℕ) (_hn : 1 ≤ n)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) : Prop :=
  ∃ cCD : ℕ, sfFullCohomologicalDimension c.g (Padic.coefficientExtensionRing l E n) cCD

/-- Exceptional-adjoint admissibility at `A_(E,n)` for the chosen compactification.
The first conjunct is the ambient datum. The second is preservation of `Dᵇ_c` by every
right adjoint. The third chooses signed bounds once, before quantifying over right
adjoints and input intervals. Its output interval may be empty. The fourth is
preservation of `Dᵇ_ctf`. Adjunctions encode the natural Hom bijections on the ordinary
unbounded derived categories of constant-ring module sheaves. There is no refinement
coherence or integral/rational coefficient condition in this definition.
Source: main-20261015, `sk-def-sf-admissible/_section.md`, clauses (1)--(3), order 1702
(blueprint: sk-def-sf-admissible). -/
noncomputable def IsSfExceptionalAdjointAdmissible
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (_hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n) (X Y : Scheme.{u})
    [X.Over (Spec (CommRingCat.of D.k))] [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) : Prop :=
  letI := Padic.finite_coefficientExtensionRing l E n hn
  HasSfAmbientExceptionalDatum l E n hn c ∧
    (∀ (G : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n) ⥤
        proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)),
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E n) ⊣ G) →
        ∀ L, intrinsicFiniteTorsionConstructible l E n hn Y L →
          intrinsicFiniteTorsionConstructible l E n hn X (G.obj L)) ∧
    (∃ cMinus cPlus : ℤ,
      ∀ (G : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n) ⥤
          proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)),
        (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E n) ⊣ G) →
          ∀ a b : ℤ, a ≤ b → ∀ L, constructibleInterval l E n hn Y a b L →
            constructibleInterval l E n hn X (a + cMinus) (b + cPlus) (G.obj L)) ∧
    ∀ (G : proEtaleDerivedCategory Y (Padic.coefficientExtensionRing l E n) ⥤
        proEtaleDerivedCategory X (Padic.coefficientExtensionRing l E n)),
      (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E n) ⊣ G) →
        ∀ L, finiteTorConstructible l E n hn Y L →
          finiteTorConstructible l E n hn X (G.obj L)

end WeilConjectures
