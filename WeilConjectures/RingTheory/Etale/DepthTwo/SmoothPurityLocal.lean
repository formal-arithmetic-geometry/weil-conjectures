/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.DepthTwo.SmoothPurityFinite
public import Mathlib.RingTheory.Polynomial.ScaleRoots
public import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Integral closures which are étale over `D(a)`

Let `O` be a Noetherian integrally closed domain, `M` an `O`-algebra, `T` the integral closure of
`O` in `M` and `[a, b]` a regular sequence in `O` with `b ≠ 0` and `a` invertible in `M`. If
`T[1/a]` is finite étale over `O[1/a]`, then `T` is finite over `O` and `(a, b)` is a regular
pair on `T` (`RingTheory.DepthTwo.finite_and_isRegularPair_integralClosure`).

Indeed `T` is torsion free, so it embeds into `L = K ⊗_O T`, an étale algebra over the fraction
field `K` of `O`; `T` lies in the integral closure of `O` in `L`, which is finite and is its own
Hartogs extension along `(a, b)` (`RingTheory.DepthTwo.hartogs_integralClosure_eq`).

This is a step of the proof of purity for normal covers of a smooth algebra over a normal base
(`RingTheory.DepthTwo.exists_etale_integralClosure_of_smooth`), an input of blueprint
`sbc-thm-spreading-finite-etale-galois`.
-/

@[expose] public section

open TensorProduct Polynomial

namespace RingTheory.DepthTwo

variable {O M : Type*} [CommRing O] [IsDomain O] [IsIntegrallyClosed O] [IsNoetherianRing O]
  [CommRing M] [Algebra O M]

omit [IsIntegrallyClosed O] [IsNoetherianRing O] in
/-- If `a` is invertible in `M` and `T[1/a]` is flat over `O[1/a]`, the integral closure `T` of
the domain `O` in `M` is torsion free: it embeds into `K ⊗_O T`. -/
lemma injective_integralClosure_tensor {a : O} (ha : IsUnit (algebraMap O M a)) (ha0 : a ≠ 0)
    [Module.Flat (Localization.Away a) (Localization.Away a ⊗[O] integralClosure O M)] :
    Function.Injective (TensorProduct.mk O (FractionRing O) (integralClosure O M) 1) := by
  set T := integralClosure O M
  rw [injective_iff_map_eq_zero]
  intro t ht
  obtain ⟨⟨s, hs⟩, hst⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors O)
    (TensorProduct.mk O (FractionRing O) T 1)).1 ht
  simp only [Submonoid.mk_smul] at hst
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  -- `1 ⊗ t = 0` in `O[1/a] ⊗ T` by flatness
  have h1 : (TensorProduct.mk O (Localization.Away a) T 1) t = 0 := by
    have hreg : IsSMulRegular (Localization.Away a ⊗[O] T)
        (algebraMap O (Localization.Away a) s) := by
      refine Module.Flat.isSMulRegular_of_isRegular (IsRegular.of_ne_zero ?_)
      exact (map_ne_zero_iff _ (IsLocalization.injective (Localization.Away a)
        (powers_le_nonZeroDivisors_of_noZeroDivisors ha0))).2 hs0
    apply hreg
    simp only [smul_zero, TensorProduct.mk_apply]
    rw [algebraMap_smul, ← TensorProduct.tmul_smul, hst, TensorProduct.tmul_zero]
  obtain ⟨⟨_, k, rfl⟩, hk⟩ := (IsLocalizedModule.eq_zero_iff (Submonoid.powers a)
    (TensorProduct.mk O (Localization.Away a) T 1)).1 h1
  apply Subtype.ext
  rw [Submonoid.smul_def] at hk
  have hk' : a ^ k • (t : M) = 0 := by simpa using congrArg Subtype.val hk
  rw [Algebra.smul_def, map_pow] at hk'
  exact ((ha.pow k).mul_right_eq_zero).1 hk'

/-- **Integral closures which are étale over `D(a)`.** Let `O` be a Noetherian integrally closed
domain, `M` an `O`-algebra, `T` the integral closure of `O` in `M`, and `[a, b]` a regular
sequence in `O` with `b ≠ 0` and `a` invertible in `M`. If `T[1/a]` is étale over `O[1/a]`, then
`T` is finite over `O` and `(a, b)` is a regular pair on `T`. -/
theorem finite_and_isRegularPair_integralClosure {a b : O}
    (hab : RingTheory.Sequence.IsWeaklyRegular O [a, b]) (hb : b ≠ 0)
    (ha : IsUnit (algebraMap O M a))
    [Algebra.Etale (Localization.Away a) (Localization.Away a ⊗[O] integralClosure O M)] :
    Module.Finite O (integralClosure O M) ∧ IsRegularPair a b (integralClosure O M) := by
  set T := integralClosure O M
  obtain ⟨hra, -⟩ := RingTheory.Sequence.IsWeaklyRegular.isSMulRegular_and_mem_smul_top hab
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact one_ne_zero (hra (by simp))
  let K := FractionRing O
  have hinjK : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have haK : IsUnit (algebraMap O K a) :=
    isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hinjK).2 ha0)
  let : Algebra (Localization.Away a) K := (IsLocalization.Away.lift a haK).toAlgebra
  have : IsScalarTower O (Localization.Away a) K :=
    .of_algebraMap_eq fun x ↦ (IsLocalization.Away.lift_eq a haK x).symm
  let L := K ⊗[O] T
  have : Algebra.Etale K L := .of_equiv
    (Algebra.TensorProduct.cancelBaseChange O (Localization.Away a) K K T)
  let ι : T →ₐ[O] L := Algebra.TensorProduct.includeRight
  have hι : Function.Injective ι := injective_integralClosure_tensor ha ha0
  have hint (t : T) : ι t ∈ integralClosure O L := (Algebra.IsIntegral.isIntegral t).map ι
  have : Module.Finite O (integralClosure O L) := finite_integralClosure_of_etale K
  refine ⟨Module.Finite.of_injective ((ι.toLinearMap).codRestrict
    (integralClosure O L).toSubmodule hint)
    fun x y h ↦ hι (congrArg Subtype.val h), ?_, ?_, ?_⟩
  · intro x y h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    simp only [Algebra.smul_def] at h'
    exact ha.mul_left_cancel h'
  · intro x y h
    apply hι
    have h' : ι (b • x) = ι (b • y) := congrArg ι h
    rw [map_smul, map_smul, Algebra.smul_def, Algebra.smul_def] at h'
    have hbL : IsUnit (algebraMap O L b) := by
      rw [IsScalarTower.algebraMap_apply O K L]
      exact (isUnit_iff_ne_zero.2 ((map_ne_zero_iff _ hinjK).2 hb)).map _
    exact hbL.mul_left_cancel h'
  · intro t ht
    obtain ⟨s, -, hs⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 ht
    have haL : IsUnit (algebraMap O L a) := by
      rw [IsScalarTower.algebraMap_apply O K L]
      exact haK.map _
    set f : L := haL.unit⁻¹ * ι t
    have hft : algebraMap O L a * f = ι t := by
      rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]
    have hfs : algebraMap O L b * f = ι s := by
      apply haL.mul_left_cancel
      rw [← mul_assoc, mul_comm (algebraMap O L a), mul_assoc, hft, ← Algebra.smul_def,
        ← Algebra.smul_def, ← map_smul, ← map_smul, hs]
    have hf : f ∈ hartogs a b (integralClosure O L) := by
      refine ⟨⟨1, ?_⟩, ⟨1, ?_⟩⟩
      · rw [pow_one, Algebra.smul_def, hft]
        exact hint t
      · rw [pow_one, Algebra.smul_def, hfs]
        exact hint s
    rw [hartogs_integralClosure_eq K hab hb] at hf
    obtain ⟨p, hp, hpf⟩ := hf
    set m : M := ha.unit⁻¹ * (t : M)
    have hmt : algebraMap O M a * m = t := by
      rw [← mul_assoc, IsUnit.mul_val_inv, one_mul]
    have h1 : aeval (ι t) (p.scaleRoots a) = 0 := by
      rw [← hft]
      exact scaleRoots_aeval_eq_zero (by rwa [aeval_def])
    rw [aeval_algHom_apply, ← map_zero ι] at h1
    have h2 := congrArg Subtype.val (hι h1)
    rw [ZeroMemClass.coe_zero, aeval_subalgebra_coe] at h2
    have hm : IsIntegral O m := by
      refine ⟨p, hp, ?_⟩
      have h3 : (algebraMap O M a) ^ p.natDegree * eval₂ (algebraMap O M) m p = 0 := by
        rw [← scaleRoots_eval₂_mul, hmt, ← aeval_def]
        exact h2
      exact ((ha.pow _).mul_right_eq_zero).1 h3
    refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨⟨m, hm⟩, Submodule.mem_top, ?_⟩
    apply Subtype.ext
    simp only [Algebra.smul_def]
    exact hmt

end RingTheory.DepthTwo
