/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
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
private theorem t_mem : t ∈ G 1 := by
  rw [hG, pow_one]
  exact LinearMap.mem_range_self (e.toLinearMap.comp (ι R (R × M))) (1, 0)
omit [GradedAlgebra G] in
include hG in
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
private theorem alpha_ι (m : M) :
    alpha R M e G hG (ι R M m) = ratio R M e G hG m :=
  lift_ι_apply _ _
private def evalOne : A →ₐ[R] SymmetricAlgebra R M :=
  (lift ((Algebra.linearMap R (SymmetricAlgebra R M)).comp (LinearMap.fst R R M) +
    (ι R M).comp (LinearMap.snd R R M))).comp e.symm.toAlgHom
private theorem evalOne_ι (r : R) (m : M) :
    evalOne R M e (e (ι R (R × M) (r, m))) = algebraMap R (SymmetricAlgebra R M) r + ι R M m := by
  simp [evalOne]
private theorem evalOne_t : evalOne R M e t = 1 := by simp [evalOne_ι]
private def beta : HomogeneousLocalization.Away G t →+* SymmetricAlgebra R M :=
  (Localization.awayLift (evalOne R M e).toRingHom t
    (by change IsUnit (evalOne R M e t); rw [evalOne_t]; exact isUnit_one)).comp
      (algebraMap (HomogeneousLocalization.Away G t) (Localization.Away t))
private theorem beta_mk (n : ℕ) (a : A) (ha : a ∈ G (n • (1 : ℕ))) :
    beta R M e G (HomogeneousLocalization.Away.mk G (t_mem R M e G hG) n a ha) =
      evalOne R M e a := by
  dsimp only [beta, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  rw [HomogeneousLocalization.Away.val_mk]
  have hu : (evalOne R M e).toRingHom t * 1 = 1 := by simp [evalOne_t]
  rw [Localization.awayLift_mk (evalOne R M e).toRingHom t a 1 hu n]
  simp
private theorem beta_alpha (a : SymmetricAlgebra R M) :
    beta R M e G (alpha R M e G hG a) = a := by
  induction a using SymmetricAlgebra.induction with
  | algebraMap r =>
      rw [AlgHom.commutes]
      change (Localization.awayLift (evalOne R M e).toRingHom t
        (by change IsUnit (evalOne R M e t); rw [evalOne_t]; exact isUnit_one))
        ((algebraMap R (HomogeneousLocalization.Away G t) r).val) = _
      rw [HomogeneousLocalization.val_algebraMap,
        Localization.mk_one_eq_algebraMap, IsLocalization.Away.lift_eq]
      exact (evalOne R M e).commutes r
  | ι m =>
      rw [alpha_ι, ratio, beta_mk R M e G hG, evalOne_ι]
      simp only [map_zero, zero_add]
  | mul a b ha hb => simp only [map_mul, ha, hb]
  | add a b ha hb => simp only [map_add, ha, hb]
private theorem alpha_evalOne_ι (r : R) (m : M) :
    (alpha R M e G hG (evalOne R M e (e (ι R (R × M) (r, m))))).val =
      algebraMap A (Localization.Away t) (e (ι R (R × M) (r, m))) *
        IsLocalization.Away.invSelf t := by
  rw [evalOne_ι, map_add, AlgHom.commutes, HomogeneousLocalization.val_add,
    HomogeneousLocalization.val_algebraMap, Localization.mk_one_eq_algebraMap]
  rw [alpha_ι]
  rw [ratio_val]
  have hpair : ((r, m) : R × M) = r • (1, 0) + (0, m) := by simp
  rw [hpair, map_add, map_smul, map_add, map_smul, Algebra.smul_def, map_add, map_mul, add_mul,
    mul_assoc, IsLocalization.Away.mul_invSelf, mul_one]
include hG in
private theorem alpha_evalOne_homogeneous (n : ℕ) (a : A) (ha : a ∈ G n) :
    (alpha R M e G hG (evalOne R M e a)).val =
      algebraMap A (Localization.Away t) a * (IsLocalization.Away.invSelf t) ^ n := by
  rw [hG] at ha
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
      rw [AlgHom.commutes, AlgHom.commutes, HomogeneousLocalization.val_algebraMap,
        Localization.mk_one_eq_algebraMap, pow_zero, mul_one]
  | add a b n ha hb hia hib =>
      simp only [map_add, HomogeneousLocalization.val_add, hia, hib, add_mul]
  | mem_mul m hm n a ha hi =>
      obtain ⟨⟨r, m⟩, rfl⟩ := hm
      change (alpha R M e G hG (evalOne R M e
        (e (ι R (R × M) (r,m)) * a))).val = _
      rw [map_mul, map_mul, HomogeneousLocalization.val_mul,
        alpha_evalOne_ι R M e G hG, hi, pow_succ]
      change _ = algebraMap B (Localization.Away t) (e (ι R (R × M) (r,m)) * a) * _
      rw [map_mul]
      ring
private theorem alpha_beta (z : HomogeneousLocalization.Away G t) :
    alpha R M e G hG (beta R M e G z) = z := by
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective G (t_mem R M e G hG) z
  rw [beta_mk R M e G hG]
  apply HomogeneousLocalization.val_injective
  rw [alpha_evalOne_homogeneous R M e G hG n a (by simpa using ha),
    HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.mk'_eq_mul_mk'_one]
  congr 1
  unfold IsLocalization.Away.invSelf
  rw [← IsLocalization.mk'_pow, one_pow]
  rfl
include hG in
/-- Setting the distinguished generator to one identifies the degree-zero localization
of the symmetric algebra of `R × M` with the symmetric algebra of `M`.
Source: Stacks Project, Constructions, Tags 01OA and 01NG.
(blueprint: lem-amb-symmetric-algebra-dehomogenization).

Proof: the forward map sends a generator `m` to `ι(0,m)/t` and fixes scalars.
The universal property of the symmetric algebra extends this linear map to an algebra map.
For the inverse, evaluate `ι(r,m)` at `r + ι(m)`. This sends `t = ι(1,0)` to one, so it
extends to the localization and restricts to its degree-zero part. The first composite
fixes scalars and generators. For the other composite, induction on the powers of the
span of the degree-one generators proves that a degree-n numerator evaluates back to
itself divided by `t^n`. Every degree-zero fraction has such a numerator. Thus both
composites are identities, including over the zero ring and for the zero module. -/
theorem exists_dehomogenization :
    ∃ a : SymmetricAlgebra R M ≃+* HomogeneousLocalization.Away G t,
      (∀ m : M, (a (ι R M m)).val =
        algebraMap B (Localization.Away t) (e (ι R (R × M) (0, m))) *
          IsLocalization.Away.invSelf t) ∧
      (∀ r : R, a (algebraMap R (SymmetricAlgebra R M) r) =
        algebraMap R (HomogeneousLocalization.Away G t) r) := by
  refine ⟨{ (alpha R M e G hG).toRingHom with
    invFun := beta R M e G
    left_inv := beta_alpha R M e G hG
    right_inv := alpha_beta R M e G hG }, ?_, ?_⟩
  · intro m
    exact (congrArg HomogeneousLocalization.val (alpha_ι R M e G hG m)).trans
      (ratio_val R M e G hG m)
  · exact (alpha R M e G hG).commutes
end SymmetricAlgebra
