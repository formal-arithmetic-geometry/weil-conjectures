/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.LinearAlgebra.Contraction
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Projective
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Finite projective modules are dualizable

A finite projective module `Q` over a commutative ring `R` is dualizable in `ModuleCat R`, with
dual `Hom_R(Q, R)`: writing `∑ⱼ ξⱼ ≫ mⱼ = 𝟙` with `ξⱼ : Q ⟶ R` and `mⱼ : R ⟶ Q`, the
coevaluation is `1 ↦ ∑ⱼ mⱼ(1) ⊗ ξⱼ` and the evaluation is the contraction `φ ⊗ q ↦ φ(q)`.
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory TensorProduct

namespace ModuleCat

variable {R : Type u} [CommRing R]

section

variable {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ} (ξ : Fin n → Module.Dual R M)
  (m : Fin n → M) (h : ∀ q, ∑ j, ξ j q • m j = q)
include h

private lemma contractLeft_zig (q : M) :
    LinearMap.lTensor M (contractLeft R M)
      (TensorProduct.assoc R M (Module.Dual R M) M ((∑ j, m j ⊗ₜ[R] ξ j) ⊗ₜ[R] q)) =
      q ⊗ₜ[R] (1 : R) := by
  simp only [sum_tmul, map_sum, TensorProduct.assoc_tmul, LinearMap.lTensor_tmul,
    contractLeft_apply]
  conv_rhs => rw [← h q, sum_tmul]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [smul_tmul, smul_eq_mul, mul_one]

private lemma contractLeft_zag (φ : Module.Dual R M) :
    LinearMap.rTensor (Module.Dual R M) (contractLeft R M)
      ((TensorProduct.assoc R (Module.Dual R M) M (Module.Dual R M)).symm
        (φ ⊗ₜ[R] ∑ j, m j ⊗ₜ[R] ξ j)) = (1 : R) ⊗ₜ[R] φ := by
  simp only [tmul_sum, map_sum, TensorProduct.assoc_symm_tmul, LinearMap.rTensor_tmul,
    contractLeft_apply]
  have hφ : ∑ j, φ (m j) • ξ j = φ := by
    ext q
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    conv_rhs => rw [← h q, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  conv_rhs => rw [← hφ, tmul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← smul_tmul, smul_eq_mul, mul_one]

end

/-- A finite projective module is dualizable in `ModuleCat R`. -/
theorem isDualizable_of_projective (Q : ModuleCat.{u} R) [Module.Finite R Q]
    [Module.Projective R Q] : IsDualizable Q := by
  obtain ⟨n, ξ, m, h⟩ := exists_sum_comp_eq_id_of_projective Q
  have h' (q : Q) : ∑ j, (ξ j).hom q • (m j).hom 1 = q := by
    have := congr($h q)
    simp only [hom_sum, LinearMap.sum_apply, hom_comp, LinearMap.comp_apply, hom_id,
      LinearMap.id_apply] at this
    refine Eq.trans (Finset.sum_congr rfl fun j _ ↦ ?_) this
    rw [← map_smul, smul_eq_mul, mul_one]
  let t : Q ⊗ ModuleCat.of R (Module.Dual R Q) :=
    ∑ j, (m j).hom 1 ⊗ₜ[R] (show Module.Dual R Q from (ξ j).hom)
  refine ⟨{ rightDual := ModuleCat.of R (Module.Dual R Q)
            exact := { coevaluation' := ofHom (LinearMap.toSpanSingleton R _ t)
                       evaluation' := ofHom (contractLeft R Q)
                       coevaluation_evaluation' := ?_
                       evaluation_coevaluation' := ?_ } }⟩
  · apply MonoidalCategory.tensor_ext
    intro φ r
    have := contractLeft_zag (fun j ↦ (ξ j).hom) (fun j ↦ (m j).hom 1) h' φ
    simp only [t, hom_comp, LinearMap.comp_apply, hom_whiskerLeft, hom_inv_associator,
      hom_whiskerRight, hom_ofHom, hom_inv_leftUnitor, hom_hom_rightUnitor]
    rw [LinearMap.lTensor_tmul]
    erw [LinearMap.toSpanSingleton_apply]
    erw [tmul_smul]
    rw [LinearEquiv.coe_coe, map_smul, map_smul, this]
    erw [TensorProduct.rid_tmul]
    rw [LinearEquiv.coe_coe, TensorProduct.lid_symm_apply, tmul_smul]
  · apply MonoidalCategory.tensor_ext
    intro r q
    have := contractLeft_zig (fun j ↦ (ξ j).hom) (fun j ↦ (m j).hom 1) h' q
    simp only [t, hom_comp, LinearMap.comp_apply, hom_whiskerLeft, hom_hom_associator,
      hom_whiskerRight, hom_ofHom, hom_hom_leftUnitor, hom_inv_rightUnitor]
    rw [LinearMap.rTensor_tmul]
    erw [LinearMap.toSpanSingleton_apply]
    erw [← smul_tmul']
    rw [LinearEquiv.coe_coe, map_smul, map_smul, this]
    erw [TensorProduct.lid_tmul]
    rw [LinearEquiv.coe_coe, TensorProduct.rid_symm_apply, smul_tmul']

end ModuleCat
