/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# The ideal of sections on an affine open disjoint from the support

On an affine open disjoint from the support of a quasi-coherent ideal, the ideal of
sections is the unit ideal.

We also record `AlgebraicGeometry.Scheme.IdealSheafData.le_ker_iff_range_subset_support`:
an ideal sheaf is contained in the kernel of a morphism from a reduced scheme if and only
if the range of the morphism lies in its support; and
`AlgebraicGeometry.Scheme.IdealSheafData.coe_support_sup_subset`, the set-level form of
`support_sup`.
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

/-- An ideal sheaf is contained in the kernel of a morphism from a reduced scheme exactly
when the range of the morphism lies in its support. -/
lemma le_ker_iff_range_subset_support {W : Scheme.{u}} (g : W ⟶ X) [IsReduced W] :
    I ≤ g.ker ↔ Set.range g ⊆ (I.support : Set X) := by
  rw [← map_bot, le_map_iff_comap_le, le_bot_iff, ← support_eq_top_iff, support_comap]
  simp [TopologicalSpace.Closeds.ext_iff, Set.preimage_eq_univ_iff]

/-- The support of a sum of ideal sheaves is contained in the intersection of the
supports. -/
lemma coe_support_sup_subset (I₁ I₂ : X.IdealSheafData) :
    ((I₁ ⊔ I₂).support : Set X) ⊆ (I₁.support : Set X) ∩ (I₂.support : Set X) := by
  rw [support_sup, TopologicalSpace.Closeds.coe_inf]

end AlgebraicGeometry.Scheme.IdealSheafData
