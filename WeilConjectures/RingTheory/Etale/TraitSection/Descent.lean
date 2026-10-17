/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Etale.TraitSection.Reduction
public import Mathlib.RingTheory.Flat.Localization

/-!
# Descent of finite étaleness at a prime along a flat base change

If `B → B₁` is flat, `P₁` is a prime of `B₁` over the prime `P` of `B` and `T₁ ≅ B₁ ⊗[B] T₀`,
then finite étaleness of `(B₁)_{P₁} ⊗[B₁] T₁` over `(B₁)_{P₁}` implies finite étaleness of
`B_P ⊗[B] T₀` over `B_P` (`Algebra.etale_and_finite_localization_of_baseChange`): the map
`B_P → (B₁)_{P₁}` is a flat local homomorphism, so `Algebra.etale_and_finite_of_isLocalHom`
applies.

This is the final step of the reduction of the trait case of blueprint
`sbc-thm-spreading-finite-etale-galois` to a base containing the roots of unity.
-/

@[expose] public section

open TensorProduct

/-- Finite étaleness at a prime descends along a flat base change: if `B → B₁` is flat, `P₁` is a
prime of `B₁` over the prime `P` of `B`, and `T₁ ≅ B₁ ⊗[B] T₀`, then finite étaleness of
`(B₁)_{P₁} ⊗[B₁] T₁` over `(B₁)_{P₁}` implies that of `B_P ⊗[B] T₀` over `B_P`. -/
theorem Algebra.etale_and_finite_localization_of_baseChange {B B₁ T₀ T₁ : Type*} [CommRing B]
    [CommRing B₁] [CommRing T₀] [CommRing T₁] [Algebra B B₁] [Module.Flat B B₁] [Algebra B T₀]
    [Algebra B₁ T₁] (P : Ideal B) [P.IsPrime] (P₁ : Ideal B₁) [P₁.IsPrime]
    (hP : P = P₁.comap (algebraMap B B₁)) (e : B₁ ⊗[B] T₀ ≃ₐ[B₁] T₁)
    (hE : Algebra.Etale (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[B₁] T₁))
    (hF : Module.Finite (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[B₁] T₁)) :
    Algebra.Etale (Localization.AtPrime P) (Localization.AtPrime P ⊗[B] T₀) ∧
      Module.Finite (Localization.AtPrime P) (Localization.AtPrime P ⊗[B] T₀) := by
  let R := Localization.AtPrime P
  let R₁ := Localization.AtPrime P₁
  let f := Localization.localRingHom P P₁ (algebraMap B B₁) hP
  let := f.toAlgebra
  have : IsScalarTower B R R₁ := .of_algebraMap_eq fun b ↦ by
    rw [RingHom.algebraMap_toAlgebra, Localization.localRingHom_to_map,
      IsScalarTower.algebraMap_apply B B₁ R₁]
  have : Module.Flat R R₁ :=
    (Module.flat_iff_of_isLocalization (S := R) (p := P.primeCompl) (M := R₁)).2 inferInstance
  have : IsLocalHom (algebraMap R R₁) := Localization.isLocalHom_localRingHom P P₁ _ hP
  let e' : R₁ ⊗[R] (R ⊗[B] T₀) ≃ₐ[R₁] R₁ ⊗[B₁] T₁ :=
    (Algebra.TensorProduct.cancelBaseChange B R R₁ R₁ T₀).trans <|
      (Algebra.TensorProduct.cancelBaseChange B B₁ R₁ R₁ T₀).symm.trans <|
        Algebra.TensorProduct.congr AlgEquiv.refl e
  exact Algebra.etale_and_finite_of_isLocalHom (.of_equiv e'.symm) (.equiv e'.symm.toLinearEquiv)
