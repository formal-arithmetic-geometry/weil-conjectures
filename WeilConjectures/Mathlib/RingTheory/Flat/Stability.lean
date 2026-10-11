/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Flatness of a tensor product over an intermediate algebra

Let `S` be an `R`-algebra, `M` a flat `S`-module and `N` an `S`-module which is flat over `R`.
Then `M ⊗[S] N` is flat over `R`: tensoring over `R` with it is tensoring over `R` with `N`
followed by tensoring over `S` with `M`.
-/

@[expose] public section

universe u v w t

open TensorProduct

namespace Module.Flat

variable (R : Type u) (S : Type v) (M : Type w) (N : Type t) [CommRing R] [CommRing S]
  [Algebra R S] [AddCommMonoid M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- If `M` is a flat `S`-module and `N` an `S`-module flat over `R`, then `M ⊗[S] N` is flat over
`R`. -/
theorem tensorProduct_of_flat [Flat S M] [Flat R N] : Flat R (M ⊗[S] N) := by
  rw [Flat.iff_lTensor_injectiveₛ]
  intro P _ _ Q
  let e (P' : Type u) [AddCommMonoid P'] [Module R P'] :=
    AlgebraTensorModule.assoc R S S M N P'
  let g : N ⊗[R] Q →ₗ[S] N ⊗[R] P := AlgebraTensorModule.lTensor S N Q.subtype
  have key : (e P).toLinearMap.restrictScalars R ∘ₗ Q.subtype.lTensor (M ⊗[S] N) =
      (g.lTensor M).restrictScalars R ∘ₗ (e Q).toLinearMap.restrictScalars R := by
    refine LinearMap.ext fun x ↦ ?_
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add] at hx hy ⊢; rw [hx, hy]
    | tmul y q =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | add y y' hy hy' =>
        simp only [LinearMap.coe_comp, Function.comp_apply, add_tmul, map_add] at hy hy' ⊢
        rw [hy, hy']
      | tmul m n => rfl
  have hinj : Function.Injective
      ((g.lTensor M).restrictScalars R ∘ₗ (e Q).toLinearMap.restrictScalars R) :=
    (Flat.lTensor_preserves_injective_linearMap g
      (Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)).comp (e Q).injective
  rw [← key] at hinj
  intro a b hab
  exact hinj (by simp only [LinearMap.coe_comp, Function.comp_apply, hab])

end Module.Flat

namespace Ideal

open TensorProduct

/-- **Flat base change commutes with intersections of ideals.** For a flat `A`-algebra `B`,
`(I ⊓ J) B = I B ⊓ J B`. -/
theorem map_inf_of_flat {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [Module.Flat A B]
    (I J : Ideal A) :
    (I ⊓ J).map (algebraMap A B) = I.map (algebraMap A B) ⊓ J.map (algebraMap A B) := by
  refine le_antisymm (map_inf_le _) fun b ⟨hI, hJ⟩ ↦ ?_
  have hzero (K : Ideal A) (hb : b ∈ K.map (algebraMap A B)) :
      (Ideal.Quotient.mk K 1 ⊗ₜ[A] b : (A ⧸ K) ⊗[A] B) = 0 := by
    apply (quotTensorEquivQuotSMul B K).injective
    rw [quotTensorEquivQuotSMul_mk_tmul, one_smul, map_zero,
      Submodule.Quotient.mk_eq_zero, smul_top_eq_map]
    exact hb
  let ψ : (A ⧸ (I ⊓ J)) →ₗ[A] (A ⧸ I) × (A ⧸ J) :=
    LinearMap.prod (Submodule.factor inf_le_left) (Submodule.factor inf_le_right)
  have hψ : Function.Injective ψ := by
    refine (injective_iff_map_eq_zero ψ).mpr fun z hz ↦ ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective z
    have h1 := congrArg Prod.fst hz
    have h2 := congrArg Prod.snd hz
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact ⟨(Submodule.Quotient.mk_eq_zero _).mp h1, (Submodule.Quotient.mk_eq_zero _).mp h2⟩
  have h0 : (Ideal.Quotient.mk (I ⊓ J) 1 ⊗ₜ[A] b : (A ⧸ (I ⊓ J)) ⊗[A] B) = 0 := by
    apply Module.Flat.rTensor_preserves_injective_linearMap (M := B) ψ hψ
    rw [LinearMap.rTensor_tmul, map_zero]
    have : ψ (Ideal.Quotient.mk (I ⊓ J) 1) =
        LinearMap.inl A _ _ (Ideal.Quotient.mk I 1) +
          LinearMap.inr A _ _ (Ideal.Quotient.mk J 1) := by
      ext
      · simpa [ψ] using Submodule.factor_mk (inf_le_left : I ⊓ J ≤ I) (1 : A)
      · simpa [ψ] using Submodule.factor_mk (inf_le_right : I ⊓ J ≤ J) (1 : A)
    rw [this, add_tmul, ← LinearMap.rTensor_tmul, ← LinearMap.rTensor_tmul, hzero I hI,
      hzero J hJ, map_zero, map_zero, add_zero]
  have := congrArg (quotTensorEquivQuotSMul B (I ⊓ J)) h0
  rw [quotTensorEquivQuotSMul_mk_tmul, one_smul, map_zero, Submodule.Quotient.mk_eq_zero,
    smul_top_eq_map] at this
  exact this

end Ideal
