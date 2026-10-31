/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalDifferenceFrameData
import Mathlib.AlgebraicGeometry.Gluing

/-! # Uniqueness of the divided-coordinate map on centred opens

Source: the chart proof, Steps 1--3, and Step 8 of
lem-pur-diagonal-difference-rees-frame.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Etale.FiniteSmoothPurity

namespace AlgebraicGeometry.DiagonalDifferenceReesFrame

private theorem rees_chart_range {X : Scheme.{u}} (I : X.IdealSheafData)
    (A : X.AffineZariskiSite) :
    Set.range (colimit.ι (Scheme.AffineZariskiSite.relativeGluingData
      I.coequifibered_toReesPresheaf).functor A) =
        I.deformationSpaceProj ⁻¹' (A.1 : Set X) := by
  simpa using (Scheme.AffineZariskiSite.relativeGluingData
    I.coequifibered_toReesPresheaf).preimage_toBase_eq_range_ι A |>.symm

private theorem chart_lift {X : Scheme.{u}} (I : X.IdealSheafData)
    (A : X.AffineZariskiSite) (T : X.Opens) (hAT : A.1 ≤ T) :
    ∃ j : Spec (I.reesPresheaf.obj (op A)) ⟶ (I.deformationSpaceProj ⁻¹ᵁ T).toScheme,
      j ≫ (I.deformationSpaceProj ⁻¹ᵁ T).ι =
        colimit.ι (Scheme.AffineZariskiSite.relativeGluingData
          I.coequifibered_toReesPresheaf).functor A := by
  let a := colimit.ι (Scheme.AffineZariskiSite.relativeGluingData
    I.coequifibered_toReesPresheaf).functor A
  have ha : Set.range a ⊆ Set.range (I.deformationSpaceProj ⁻¹ᵁ T).ι := by
    rw [Scheme.Opens.range_ι, rees_chart_range]
    exact Set.preimage_mono hAT
  exact ⟨IsOpenImmersion.lift _ a ha, IsOpenImmersion.lift_fac ..⟩

set_option backward.isDefEq.respectTransparency false in
/-- Any two centred divided-coordinate maps agree on a common smaller neighbourhood.
Source: the chart proof under open restriction (blueprint:
lem-pur-diagonal-difference-chart-restriction).

Proof: the Rees spectra over affine opens contained in the common neighbourhood cover
its inverse image in the deformation. Their inclusions factor through both charts.
On each such spectrum both maps pull t back to the same Rees parameter and each v_i
to the same Laurent representative f_i/t. The universal property of affine space,
first for the base affine line and then for its relative affine space, makes the maps
equal. The covering open immersions then give equality globally. -/
theorem CentredChart.restrict_eq {U V : Scheme.{u}} {d : ℕ} {h : U ⟶ V}
    [IsSeparated h] {x : ULift.{u} (Fin d) → Γ(U, ⊤)} {N : NormalFrame d h x}
    (C C' : CentredChart d h x N) (T : (pullback h h).Opens)
    (ht : T ≤ C.O) (ht' : T ≤ C'.O) :
    ((pullback.diagonal h).ker.deformationSpace).homOfLE
        ((pullback.diagonal h).ker.deformationSpaceProj.preimage_mono ht) ≫ C.deformation =
      ((pullback.diagonal h).ker.deformationSpace).homOfLE
        ((pullback.diagonal h).ker.deformationSpaceProj.preimage_mono ht') ≫
          C'.deformation := by
  let I := (pullback.diagonal h).ker
  let D := I.deformationSpace
  let π := I.deformationSpaceProj
  let R := π ⁻¹ᵁ T
  let f := D.homOfLE (π.preimage_mono ht) ≫ C.deformation
  let g := D.homOfLE (π.preimage_mono ht') ≫ C'.deformation
  change f = g
  apply Scheme.hom_ext_of_forall
  intro z
  obtain ⟨A, hA, hzA, hAT⟩ := exists_isAffineOpen_mem_and_subset
    (show π (R.ι z) ∈ T from z.property)
  let a : (pullback h h).AffineZariskiSite := ⟨A, hA⟩
  obtain ⟨j, hj⟩ := chart_lift I a T hAT
  obtain ⟨jC, hjC, _, hvC⟩ := C.charts a (hAT.trans ht)
  obtain ⟨jC', hjC', _, hvC'⟩ := C'.charts a (hAT.trans ht')
  have hjCeq : j ≫ D.homOfLE (π.preimage_mono ht) = jC := by
    apply (cancel_mono (π ⁻¹ᵁ C.O).ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι]
    exact hj.trans hjC.symm
  have hjC'eq : j ≫ D.homOfLE (π.preimage_mono ht') = jC' := by
    apply (cancel_mono (π ⁻¹ᵁ C'.O).ι).mp
    rw [Category.assoc, Scheme.homOfLE_ι]
    exact hj.trans hjC'.symm
  have heq : j ≫ f = j ≫ g := by
    dsimp only [f, g]
    rw [← Category.assoc, ← Category.assoc, hjCeq, hjC'eq]
    apply AffineSpace.hom_ext
    · calc
        _ = (jC ≫ (π ⁻¹ᵁ C.O).ι) ≫
            Scheme.Hom.deformationSpaceProj (pullback.fst h h) (pullback.diagonal h) := by
          rw [Category.assoc, C.deformation_over, Category.assoc]
        _ = (jC' ≫ (π ⁻¹ᵁ C'.O).ι) ≫
            Scheme.Hom.deformationSpaceProj (pullback.fst h h) (pullback.diagonal h) := by
          rw [hjC, hjC']
        _ = _ := by
          simpa only [Category.assoc] using
            (congrArg (jC' ≫ ·) C'.deformation_over).symm
    · intro i
      obtain ⟨hi, hvi⟩ := hvC i
      obtain ⟨hi', hvi'⟩ := hvC' i
      exact hvi.trans hvi'.symm
  have : IsOpenImmersion j := by
    have : IsOpenImmersion (j ≫ R.ι) := by rw [hj]; infer_instance
    exact IsOpenImmersion.of_comp j R.ι
  have hzj : z ∈ j.opensRange := by
    change z ∈ Set.range j
    have hz : R.ι z ∈ Set.range (j ≫ R.ι) := by
      rw [hj]
      exact (rees_chart_range I a).symm ▸ hzA
    obtain ⟨w, hw⟩ := hz
    exact ⟨w, R.ι.injective hw⟩
  refine ⟨j.opensRange, hzj, ?_⟩
  rw [← j.isoOpensRange_inv_comp]
  simpa only [Category.assoc] using congrArg (j.isoOpensRange.inv ≫ ·) heq

end AlgebraicGeometry.DiagonalDifferenceReesFrame
