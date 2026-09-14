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
`AlgebraicGeometry.Scheme.IdealSheafData.coe_support_sup`, the set-level form of
`support_sup`; and
`AlgebraicGeometry.Scheme.IdealSheafData.pow_eq_zero_iff_of_isAffine`: on an affine scheme a
power of an ideal sheaf vanishes exactly when the corresponding power of the ideal of global
sections does.
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

/-- On an affine scheme, a power of an ideal sheaf vanishes exactly when the corresponding
power of the ideal of global sections does. -/
lemma pow_eq_zero_iff_of_isAffine [IsAffine X] {n : ℕ} :
    I ^ n = 0 ↔ I.ideal ⟨⊤, isAffineOpen_top X⟩ ^ n = ⊥ := by
  rw [← Pi.pow_apply, ← ideal_pow]
  refine ⟨fun h ↦ ?_, fun h ↦ ext_of_isAffine ?_⟩
  · rw [h, zero_eq_bot, ideal_bot, Pi.bot_apply]
  · rw [h, zero_eq_bot, ideal_bot, Pi.bot_apply]

/-- The support of a sum of ideal sheaves is the intersection of the supports: the
set-level form of `support_sup`. -/
lemma coe_support_sup (I₁ I₂ : X.IdealSheafData) :
    ((I₁ ⊔ I₂).support : Set X) = (I₁.support : Set X) ∩ (I₂.support : Set X) := by
  rw [support_sup, TopologicalSpace.Closeds.coe_inf]

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Hom

/-- If the kernel of a ring homomorphism `φ` has vanishing `n`-th power, so does the kernel
ideal sheaf of `Spec φ`. -/
lemma pow_ker_SpecMap_eq_zero {R S : CommRingCat.{u}} {n : ℕ} (φ : R ⟶ S)
    (hφ : RingHom.ker φ.hom ^ n = ⊥) : (Spec.map φ).ker ^ n = 0 := by
  have he : (Spec.map φ).appTop = (ΓSpecIso R).hom ≫ φ ≫ (ΓSpecIso S).inv := by
    rw [ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  have hk : RingHom.ker (Spec.map φ).appTop.hom =
      (RingHom.ker φ.hom).comap (ΓSpecIso R).hom.hom := by
    rw [he]
    simp only [CommRingCat.hom_comp, RingHom.comp_assoc]
    rw [← RingHom.comap_ker]
    exact RingHom.ker_comp_of_injective _
      (ΓSpecIso S).symm.commRingCatIsoToRingEquiv.injective
  have hcomap : (RingHom.ker φ.hom).comap (ΓSpecIso R).hom.hom ^ n = ⊥ := by
    refine le_bot_iff.mp ((Ideal.le_comap_pow _ n).trans ?_)
    rw [hφ, ← RingHom.ker_eq_comap_bot]
    exact le_of_eq (RingHom.ker_coe_equiv (ΓSpecIso R).commRingCatIsoToRingEquiv)
  rw [IdealSheafData.pow_eq_zero_iff_of_isAffine, ker_of_isAffine]
  simp only [IdealSheafData.ofIdealTop_ideal, hk, ← Ideal.map_pow, hcomap, Ideal.map_bot]

end AlgebraicGeometry.Scheme.Hom
