/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.AlgebraicGeometry.Properties

/-!
# The ideal of sections on an affine open disjoint from the support

On an affine open disjoint from the support of a quasi-coherent ideal, the ideal of
sections is the unit ideal.

We also record `AlgebraicGeometry.Scheme.IdealSheafData.le_ker_of_range_subset_support`:
an ideal sheaf is contained in the kernel of any morphism from a reduced scheme whose
range lies in its support.
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

/-- An ideal sheaf is contained in the kernel of any morphism from a reduced scheme
whose range lies in its support: a section of the ideal pulls back to a section of the
reduced scheme vanishing at every point, hence to zero. -/
lemma le_ker_of_range_subset_support {W : Scheme.{u}} (g : W ⟶ X) [IsReduced W]
    (hg : Set.range g ⊆ (I.support : Set X)) : I ≤ g.ker := by
  refine le_ofIdeals_iff.mpr fun U s hs ↦ ?_
  rw [RingHom.mem_ker]
  refine eq_zero_of_basicOpen_eq_bot _ ?_
  have hbo : ∀ w : W, g w ∉ X.basicOpen s := fun w ↦
    (X.mem_zeroLocus_iff _ _).mp (I.mem_support_iff.mp (hg ⟨w, rfl⟩) U) s hs
  rw [← Scheme.preimage_basicOpen]
  exact TopologicalSpace.Opens.ext
    (Set.eq_empty_iff_forall_notMem.mpr fun w hw ↦ hbo w hw)

end AlgebraicGeometry.Scheme.IdealSheafData
