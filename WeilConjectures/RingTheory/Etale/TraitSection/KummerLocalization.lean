/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Smooth.Flat
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import WeilConjectures.RingTheory.Etale.TraitSection.BaseChange

/-!
# Adjoining an `n`-th root and localization

Let `A → B` be a ring map, `ϖ ∈ A`, `A₂ = A[t] ⧸ (tⁿ - ϖ)` and `B₂ = B ⊗[A] A₂`. For a
`B`-algebra `T`, `T ⊗[A] A₂` is `T[t] ⧸ (tⁿ - ϖ)` (`AdjoinRoot.tensorXPowSubCEquiv`); hence if
`T = S⁻¹B` then `T[t] ⧸ (tⁿ - ϖ)` is the localization `S⁻¹B₂`
(`AdjoinRoot.isLocalization_tensorXPowSubC`), and the integral closure of `T[t] ⧸ (tⁿ - ϖ)` in
`T[t] ⧸ (tⁿ - ϖ) ⊗[T] (T ⊗[B] L)` is the base change of the integral closure of `B₂` in
`B₂ ⊗[B] L` (`TensorProduct.integralClosureTensorEquivOfIsLocalization`).

We also record that the base change `B₁ ⊗[B] L` of a finite étale `B_K`-algebra `L` is finite
étale over `B₁ ⊗[B] B_K` of the same rank (`Algebra.TraitSection.etale_finite_cover`).

This is used in the trait case of blueprint `sbc-thm-spreading-finite-etale-galois`
([Stacks 0EYJ]).
-/

@[expose] public section

open Polynomial TensorProduct
namespace AdjoinRoot

/-- Adjoining an `n`-th root of `a` commutes with base change. -/
noncomputable def tensorXPowSubCEquiv (A T : Type*) [CommRing A] [CommRing T] [Algebra A T]
    (n : ℕ) (a : A) :
    T ⊗[A] AdjoinRoot (X ^ n - C a) ≃ₐ[T] AdjoinRoot (X ^ n - C (algebraMap A T a)) :=
  (tensorAlgEquiv (X ^ n - C a) _ rfl).trans
    (mapAlgEquiv (Algebra.TensorProduct.rid A T T) _ _ (by
      rw [Polynomial.map_map]
      simp [Algebra.algebraMap_eq_smul_one]))


variable {A B T : Type*} [CommRing A] [CommRing B] [Algebra A B] [CommRing T] [Algebra B T]
  [Algebra A T] [IsScalarTower A B T] (n : ℕ) (ϖ : A)

/-- The map `B ⊗[A] A[t]/(tⁿ - ϖ) → T[t]/(tⁿ - ϖ)` for a `B`-algebra `T`. -/
noncomputable def tensorXPowSubCMap :
    B ⊗[A] AdjoinRoot (X ^ n - C ϖ) →ₐ[B] AdjoinRoot (X ^ n - C (algebraMap A T ϖ)) :=
  Algebra.TensorProduct.lift (Algebra.ofId B _)
    (liftAlgHom _ (Algebra.ofId A _) (root _) (by
      have := AdjoinRoot.eval₂_root (X ^ n - C (algebraMap A T ϖ))
      simpa [eval₂_sub, Algebra.ofId_apply, IsScalarTower.algebraMap_apply A T
        (AdjoinRoot (X ^ n - C (algebraMap A T ϖ))), AdjoinRoot.algebraMap_eq] using this))
    fun _ _ ↦ Commute.all _ _

attribute [local instance] Algebra.TensorProduct.rightAlgebra

lemma tensorXPowSubCEquiv_cancel_tmul (x : B ⊗[A] AdjoinRoot (X ^ n - C ϖ)) :
    (tensorXPowSubCEquiv A T n ϖ) (Algebra.TensorProduct.cancelBaseChange A B T T _
      ((1 : T) ⊗ₜ[B] x)) = tensorXPowSubCMap (T := T) n ϖ x := by
  let f₁ : B ⊗[A] AdjoinRoot (X ^ n - C ϖ) →ₐ[B] AdjoinRoot (X ^ n - C (algebraMap A T ϖ)) :=
    (((tensorXPowSubCEquiv A T n ϖ).toAlgHom.comp
      (Algebra.TensorProduct.cancelBaseChange A B T T _).toAlgHom).restrictScalars B).comp
      Algebra.TensorProduct.includeRight
  have : f₁ = tensorXPowSubCMap (T := T) n ϖ := by
    refine Algebra.TensorProduct.ext ?_ ?_
    · ext
    · refine AdjoinRoot.algHom_ext ?_
      simp [f₁, tensorXPowSubCMap, tensorXPowSubCEquiv]
  exact congr($this x)


/-- The `B ⊗[A] A[t]/(tⁿ - ϖ)`-algebra structure on `T[t]/(tⁿ - ϖ)`. -/
@[instance_reducible]
noncomputable def tensorXPowSubCAlgebra :
    Algebra (B ⊗[A] AdjoinRoot (X ^ n - C ϖ)) (AdjoinRoot (X ^ n - C (algebraMap A T ϖ))) :=
  (tensorXPowSubCMap n ϖ).toRingHom.toAlgebra

lemma isScalarTower_tensorXPowSubCAlgebra :
    letI := tensorXPowSubCAlgebra (B := B) (T := T) n ϖ
    IsScalarTower B (B ⊗[A] AdjoinRoot (X ^ n - C ϖ))
      (AdjoinRoot (X ^ n - C (algebraMap A T ϖ))) :=
  letI := tensorXPowSubCAlgebra (B := B) (T := T) n ϖ
  .of_algebraMap_eq fun b ↦ ((tensorXPowSubCMap n ϖ).commutes b).symm

/-- `T[t]/(tⁿ - ϖ)` is the localization of `B ⊗[A] A[t]/(tⁿ - ϖ)` at `S` if `T = S⁻¹B`. -/
theorem isLocalization_tensorXPowSubC (S : Submonoid B) [IsLocalization S T] :
    letI := tensorXPowSubCAlgebra (B := B) (T := T) n ϖ
    IsLocalization (Algebra.algebraMapSubmonoid (B ⊗[A] AdjoinRoot (X ^ n - C ϖ)) S)
      (AdjoinRoot (X ^ n - C (algebraMap A T ϖ))) := by
  let := tensorXPowSubCAlgebra (B := B) (T := T) n ϖ
  have := isScalarTower_tensorXPowSubCAlgebra (B := B) (T := T) n ϖ
  have h : Algebra.IsPushout B T (B ⊗[A] AdjoinRoot (X ^ n - C ϖ))
      (AdjoinRoot (X ^ n - C (algebraMap A T ϖ))) :=
    Algebra.IsPushout.of_equiv ((Algebra.TensorProduct.cancelBaseChange A B T T _).trans
      (tensorXPowSubCEquiv A T n ϖ)) (RingHom.ext fun x ↦ tensorXPowSubCEquiv_cancel_tmul n ϖ x)
  exact (Algebra.isLocalization_iff_isPushout S _).2 h.symm

end AdjoinRoot

/-- **Integral closure and localization of the base.** Let `B → T → D` and `B → B₂ → D` be
compatible, with `D` the localization of `B₂` at the image of `S ⊆ B`. Then the integral closure
of `D` in `D ⊗[T] (T ⊗[B] L)` is the base change of the integral closure of `B₂` in `B₂ ⊗[B] L`.
-/
noncomputable def TensorProduct.integralClosureTensorEquivOfIsLocalization {B B₂ T D : Type*}
    [CommRing B] [CommRing B₂] [CommRing T] [CommRing D] [Algebra B B₂] [Algebra B T]
    [Algebra T D] [Algebra B D] [IsScalarTower B T D] [Algebra B₂ D] [IsScalarTower B B₂ D]
    (S : Submonoid B) [IsLocalization (Algebra.algebraMapSubmonoid B₂ S) D]
    (L : Type*) [CommRing L] [Algebra B L] :
    D ⊗[B₂] integralClosure B₂ (B₂ ⊗[B] L) ≃ₐ[D] integralClosure D (D ⊗[T] (T ⊗[B] L)) :=
  (AlgEquiv.ofBijective _ (TensorProduct.toIntegralClosure_bijective_of_isLocalization
    (Algebra.algebraMapSubmonoid B₂ S))).trans
    (AlgEquiv.mapIntegralClosure
      ((Algebra.TensorProduct.cancelBaseChange B B₂ D D L).trans
        (Algebra.TensorProduct.cancelBaseChange B T D D L).symm))

namespace Algebra.TraitSection

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {B B₁ Bk L : Type*} [CommRing B] [CommRing B₁] [Algebra B B₁] [CommRing Bk]
  [Algebra B Bk] [CommRing L] [Algebra Bk L] [Algebra B L] [IsScalarTower B Bk L]
  [Module.Finite Bk L] [Algebra.Etale Bk L]

/-- The base change `B₁ ⊗[B] L` of a finite étale `B_K`-algebra `L` is finite étale over
`B₁ ⊗[B] B_K`, of the same constant rank. -/
theorem etale_finite_cover :
    letI := (coverMap (B := B) (B₁ := B₁) (Bk := Bk) (L := L)).toRingHom.toAlgebra
    Algebra.Etale (B₁ ⊗[B] Bk) (B₁ ⊗[B] L) ∧ Module.Finite (B₁ ⊗[B] Bk) (B₁ ⊗[B] L) ∧
      ∀ k : ℕ, (∀ p, Module.rankAtStalk (R := Bk) L p = k) →
        ∀ p, Module.rankAtStalk (R := B₁ ⊗[B] Bk) (B₁ ⊗[B] L) p = k := by
  let := (coverMap (B := B) (B₁ := B₁) (Bk := Bk) (L := L)).toRingHom.toAlgebra
  let eL := coverEquiv (B := B) (B₁ := B₁) (Bk := Bk) (L := L)
  refine ⟨.of_equiv eL, .equiv eL.toLinearEquiv, fun k hk p ↦ ?_⟩
  rw [← Module.rankAtStalk_eq_of_equiv eL.toLinearEquiv, Module.rankAtStalk_baseChange]
  exact hk _

end Algebra.TraitSection
