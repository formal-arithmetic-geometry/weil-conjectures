/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
/-! # Dehomogenizing a symmetric algebra

Source: Stacks Project, Constructions, Tags 01OA and 01NG.
(blueprint: lem-amb-symmetric-algebra-dehomogenization).
-/

@[expose] public section
set_option autoImplicit false
open scoped Pointwise
universe u v w
noncomputable section
namespace SymmetricAlgebra
variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
variable {B : Type w} [CommRing B] [Algebra R B]
variable (e : SymmetricAlgebra R (R × M) ≃ₐ[R] B)
local notation "A" => B
variable (G : ℕ → Submodule R B) [GradedAlgebra G]
variable (hG : ∀ n, G n = (LinearMap.range (e.toLinearMap.comp (ι R (R × M)))) ^ n)
local notation "t" => e (ι R (R × M) (1, 0))
omit [GradedAlgebra G] in
include hG in
omit [GradedAlgebra G] in
include hG in
include hG in
include hG in
end SymmetricAlgebra

namespace SymmetricAlgebra

private theorem t_mem : t ∈ G 1 := by
  rw [hG, pow_one]
  exact LinearMap.mem_range_self (e.toLinearMap.comp (ι R (R × M))) (1, 0)

private theorem x_mem (m : M) : e (ι R (R × M) (0, m)) ∈ G (1 • (1 : ℕ)) := by
  rw [hG]
  simp only [one_smul, pow_one]
  exact LinearMap.mem_range_self (e.toLinearMap.comp (ι R (R × M))) (0, m)

private def ratio (m : M) : HomogeneousLocalization.Away G t :=
  HomogeneousLocalization.Away.mk G (t_mem R M e G hG) 1
    (e (ι R (R × M) (0, m))) (x_mem R M e G hG m)

private theorem ratio_val (m : M) :
    (ratio R M e G hG m).val = algebraMap A (Localization.Away t) (e (ι R (R × M) (0, m))) *
      IsLocalization.Away.invSelf t := by
  simp only [ratio, HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_mul_mk'_one]
  simp only [pow_one]
  rfl

private def ratioLinear : M →ₗ[R] HomogeneousLocalization.Away G t where
  toFun := ratio R M e G hG
  map_add' m n := by
    apply HomogeneousLocalization.val_injective
    simp only [ratio_val, HomogeneousLocalization.val_add]
    rw [show ((0, m + n) : R × M) = (0, m) + (0, n) by simp]
    simp only [map_add, add_mul]
  map_smul' r m := by
    apply HomogeneousLocalization.val_injective
    simp only [ratio_val, HomogeneousLocalization.val_smul]
    rw [show ((0, r • m) : R × M) = r • (0, m) by simp]
    rw [map_smul, map_smul, Algebra.smul_def, map_mul]
    simp only [RingHom.id_apply, Algebra.smul_def]
    change _ = algebraMap R (Localization.Away t) r * _
    rw [IsScalarTower.algebraMap_apply R A (Localization.Away t), mul_assoc]

private def alpha : SymmetricAlgebra R M →ₐ[R] HomogeneousLocalization.Away G t :=
  lift (ratioLinear R M e G hG)

end SymmetricAlgebra
