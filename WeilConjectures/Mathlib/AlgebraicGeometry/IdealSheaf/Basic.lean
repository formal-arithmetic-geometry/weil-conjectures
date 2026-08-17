/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# The ideal of sections on an affine open disjoint from the support

On an affine open disjoint from the support of a quasi-coherent ideal, the ideal of
sections is the unit ideal.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- On an affine open disjoint from the support, the ideal is the unit ideal.
(blueprint: `lemma:nagata-ideal-unit-off-support`) -/
lemma ideal_eq_top_of_disjoint_support {U : X.affineOpens}
    (hU : Disjoint (U.1 : Set X) (I.support : Set X)) : I.ideal U = ⊤ := by
  have hsub : X.zeroLocus (U := U.1) (I.ideal U) ∩ U.1 ⊆ (∅ : Set X) := fun x hx ↦
    (Set.disjoint_left.mp hU hx.2 (I.zeroLocus_inter_subset_supportSet U hx)).elim
  have h := (U.2.fromSpec_image_zeroLocus _).trans_subset hsub
  simp only [Set.subset_empty_iff, Set.image_eq_empty] at h
  exact PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp h

end AlgebraicGeometry.Scheme.IdealSheafData
