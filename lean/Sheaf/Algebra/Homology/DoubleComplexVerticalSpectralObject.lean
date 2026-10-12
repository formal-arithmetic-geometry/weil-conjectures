/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E2
-/
module

public import Sheaf.Algebra.Homology.DoubleComplexVerticalWindow
public import Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Homology.SpectralObject.SpectralSequence

/-!
# The vertical truncation spectral object of a first-quadrant double complex

Source: the construction and graded-piece calculation of blueprint
thm-sp-double-complex-spectral-sequences; Stacks, Homology, Section 12.25.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.ComposableArrows

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The smart vertical truncations determine a first-quadrant spectral object.
Source: blueprint thm-sp-double-complex-spectral-sequences, construction in proof step 1;
Stacks, Homology, Section 12.25, the filtration construction.
(blueprint: lem-sp-double-complex-vertical-spectral-object).

Proof: regard the transpose of K, extended by zero in the vertical direction, as a
bounded-below complex in the abelian category of nonnegative horizontal complexes.
Evaluation in a horizontal degree is exact, so its smart truncations are the columnwise
smart truncations used in verticalWindow. Totalization of bounded-below complexes in
this category takes values in integer cochain complexes and preserves triangles.
It also preserves vertical quasi-isomorphisms. Indeed their cones have acyclic columns;
in each degree the diagonal has finite support, and a cycle is eliminated one horizontal
component at a time using vertical exactness. The remaining horizontal component moves
one step to the right and one step down, so the uniform lower bound makes this procedure
terminate. This is the ordinary finite diagonal chase, equivalently a chase of kernels
and images in the abelian category. Hence totalization descends to a triangulated functor
on the bounded-below derived category of horizontal complexes.

Apply the standard t-structure spectral-object construction to the transpose of K,
then the descended totalization functor and the homology functor. This supplies the
interval functors, natural connecting maps and exactness axioms. Finite intervals are
the total complexes of verticalWindow; infinite endpoints use one-sided truncations;
the whole interval is the original total complex. Intervals ending at or below zero
vanish, while those starting at a have no total terms below a. These give the two
first-quadrant conditions. The displayed comparisons are the construction identifications.
No second-page calculation or convergence assertion is part of this lemma. -/
theorem exists_verticalSpectralObject
    [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ),
      L.HasTotal (ComplexShape.up ℕ)]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    ∃ Y : CategoryTheory.Abelian.SpectralObject C EInt,
      Y.IsFirstQuadrant ∧
      (∀ (a b : ℤ) (hab : a ≤ b) (n : ℕ),
        Nonempty ((Y.H n).obj (mk₁ (homOfLE
          (show (a : EInt) ≤ (b : EInt) from WithBotTop.coe_le_coe.mpr hab))) ≅
          (HomologicalComplex₂.total
            (((verticalWindow a b).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)
            (ComplexShape.up ℕ)).homology n)) ∧
      (∀ n : ℕ, Nonempty ((Y.H n).obj (mk₁ (homOfLE
        (bot_le : (⊥ : EInt) ≤ ⊤))) ≅ (K.total (ComplexShape.up ℕ)).homology n)) := by
  sorry

end HomologicalComplex₂
