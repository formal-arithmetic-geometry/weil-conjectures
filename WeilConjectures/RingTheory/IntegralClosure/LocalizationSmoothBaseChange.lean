/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Smooth.IntegralClosure
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Integral closure commutes with base change along a localization followed by a smooth map

Let `R₀ → A` be a localization and `A → A₁` a smooth map. For an `R₀`-algebra `B` and a
`B`-algebra `L`, the integral closure of `B` in `L` commutes with the base change
`B → B ⊗[R₀] A₁`: the map `B → B ⊗[R₀] A₁` factors as the localization `B → B ⊗[R₀] A`
followed by the smooth map `B ⊗[R₀] A → B ⊗[R₀] A₁` (a base change of `A → A₁`).

Used in the trait case of the spreading theorem (blueprint
`sbc-thm-spreading-finite-etale-galois`), where `A = (R₀)_q` and `A → A₁` adjoins roots of unity.
-/

@[expose] public section

open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Integral closure commutes with base change along `B → B ⊗[R₀] A₁`, where `R₀ → A` is a
localization and `A → A₁` is smooth. -/
theorem TensorProduct.toIntegralClosure_bijective_of_isLocalization_of_smooth
    {R₀ A A₁ B L : Type*} [CommRing R₀] [CommRing A] [CommRing A₁] [CommRing B] [CommRing L]
    [Algebra R₀ A] (M : Submonoid R₀) [IsLocalization M A]
    [Algebra A A₁] [Algebra R₀ A₁] [IsScalarTower R₀ A A₁] [Algebra.Smooth A A₁]
    [Algebra R₀ B] [Algebra B L] :
    Function.Bijective (toIntegralClosure B (B ⊗[R₀] A₁) L) := by
  let f : B ⊗[R₀] A →ₐ[B] B ⊗[R₀] A₁ :=
    Algebra.TensorProduct.map (AlgHom.id B B) (IsScalarTower.toAlgHom R₀ A A₁)
  let := f.toAlgebra
  let : Algebra A (B ⊗[R₀] A₁) := ((algebraMap A₁ _).comp (algebraMap A A₁)).toAlgebra
  have : IsScalarTower A A₁ (B ⊗[R₀] A₁) := .of_algebraMap_eq' rfl
  have : IsScalarTower B (B ⊗[R₀] A) (B ⊗[R₀] A₁) := .of_algebraMap_eq' f.comp_algebraMap.symm
  have : IsScalarTower A (B ⊗[R₀] A) (B ⊗[R₀] A₁) := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, f]
  have : IsScalarTower R₀ (B ⊗[R₀] A) (B ⊗[R₀] A₁) := .of_algebraMap_eq fun a ↦ by
    simp [RingHom.algebraMap_toAlgebra, f]
  have : Algebra.IsPushout A (B ⊗[R₀] A) A₁ (B ⊗[R₀] A₁) := .symm <|
    (Algebra.IsPushout.comp_iff (R := R₀) (S := A) (R' := B) (S' := B ⊗[R₀] A) (T := A₁)
      (T' := B ⊗[R₀] A₁)).1 inferInstance
  have : Algebra.Smooth (B ⊗[R₀] A) (B ⊗[R₀] A₁) :=
    .of_equiv (Algebra.IsPushout.equiv A (B ⊗[R₀] A) A₁ (B ⊗[R₀] A₁))
  exact toIntegralClosure_bijective_of_tower (S := B ⊗[R₀] A)
    (toIntegralClosure_bijective_of_isLocalization (Algebra.algebraMapSubmonoid B M))
    toIntegralClosure_bijective_of_smooth
