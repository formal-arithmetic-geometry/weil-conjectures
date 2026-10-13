/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.Excellent.Defs

/-!
# Transport of geometric regularity

We show that `Algebra.IsGeometricallyRegular k A` only depends on the pair `(k, A)` up to
compatible ring isomorphisms, and deduce that regularity of the generic formal fibre can be
checked with any choice of fraction field.

## Main results

- `Algebra.IsGeometricallyRegular.of_ringEquiv`
- `Algebra.IsGeometricallyRegular.iff_of_ringEquiv`
- `genericFormalFiber_geometricallyRegular_of_fractionField_transport`
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Algebra.IsGeometricallyRegular

/-- Geometric regularity is transported along a ring isomorphism `σ : k₁ ≃+* k₂` of base fields
and a compatible ring isomorphism `e : A₁ ≃+* A₂`. -/
theorem of_ringEquiv {k₁ k₂ : Type u} [Field k₁] [Field k₂] {A₁ : Type v} {A₂ : Type w}
    [CommRing A₁] [CommRing A₂] [Algebra k₁ A₁] [Algebra k₂ A₂] (σ : k₁ ≃+* k₂) (e : A₁ ≃+* A₂)
    (he : ∀ x, e (algebraMap k₁ A₁ x) = algebraMap k₂ A₂ (σ x))
    (h : IsGeometricallyRegular k₁ A₁) : IsGeometricallyRegular k₂ A₂ := by
  refine ⟨@isNoetherianRing_of_ringEquiv _ _ _ _ e h.1, fun k' _ _ _ _ ↦ ?_⟩
  let _ : Algebra k₁ k₂ := σ.toRingHom.toAlgebra
  let _ : Algebra k₁ k' := ((algebraMap k₂ k').comp σ.toRingHom).toAlgebra
  let _ : Algebra k₁ A₂ := ((algebraMap k₂ A₂).comp σ.toRingHom).toAlgebra
  have : IsScalarTower k₁ k₂ k' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k₁ k₂ A₂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Module.Finite k₁ k₂ :=
    Module.Finite.of_surjective (Algebra.linearMap k₁ k₂) σ.surjective
  have : Module.Finite k₁ k' := Module.Finite.trans k₂ k'
  have : IsPurelyInseparable k₁ k₂ := ⟨inferInstance, fun x _ ↦ σ.surjective x⟩
  have : IsPurelyInseparable k₁ k' := IsPurelyInseparable.trans k₁ k₂ k'
  have : TensorProduct.CompatibleSMul k₁ k₂ k' A₂ :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective _ _ σ.surjective
  have hreg := h.2 k'
  let e₁ : A₁ ≃ₐ[k₁] A₂ := AlgEquiv.ofRingEquiv (f := e) he
  let e₂ : k' ⊗[k₁] A₁ ≃ₐ[k₁] k' ⊗[k₁] A₂ := Algebra.TensorProduct.congr AlgEquiv.refl e₁
  let e₃ : k' ⊗[k₂] A₂ ≃ₐ[k₁] k' ⊗[k₁] A₂ :=
    Algebra.TensorProduct.equivOfCompatibleSMul k₁ k₂ k₁ k' A₂
  exact IsRegularRing.of_ringEquiv (e₂.toRingEquiv.trans e₃.symm.toRingEquiv)

/-- Geometric regularity is invariant under a ring isomorphism `σ : k₁ ≃+* k₂` of base fields
together with a compatible ring isomorphism `e : A₁ ≃+* A₂`. -/
theorem iff_of_ringEquiv {k₁ k₂ : Type u} [Field k₁] [Field k₂] {A₁ : Type v} {A₂ : Type w}
    [CommRing A₁] [CommRing A₂] [Algebra k₁ A₁] [Algebra k₂ A₂] (σ : k₁ ≃+* k₂) (e : A₁ ≃+* A₂)
    (he : ∀ x, e (algebraMap k₁ A₁ x) = algebraMap k₂ A₂ (σ x)) :
    IsGeometricallyRegular k₁ A₁ ↔ IsGeometricallyRegular k₂ A₂ :=
  ⟨of_ringEquiv σ e he, of_ringEquiv σ.symm e.symm fun x ↦ by
    rw [RingEquiv.symm_apply_eq, he, RingEquiv.apply_symm_apply]⟩

end Algebra.IsGeometricallyRegular

/-- Let `A` be a Noetherian domain with a chosen fraction field `K`, `P` a prime of `A` and
`C` the completion of `A_P`. If the generic formal fibre `κ(0) ⊗_A C` is geometrically regular
over the canonical generic residue field `κ(0)`, then `K ⊗_A C` is geometrically regular over `K`.
(blueprint: `lem-weil-pbc-generic-formal-fibre-fraction-field-transport`) -/
theorem genericFormalFiber_geometricallyRegular_of_fractionField_transport (A : Type u)
    [CommRing A] [IsDomain A] [IsNoetherianRing A] (K : Type u) [Field K] [Algebra A K]
    [IsFractionRing A K] (P : Ideal A) [P.IsPrime]
    (h :
      let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
        (Localization.AtPrime P)
      Algebra.IsGeometricallyRegular (⊥ : Ideal A).ResidueField ((⊥ : Ideal A).Fiber C)) :
    let C := AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (Localization.AtPrime P)
    Algebra.IsGeometricallyRegular K (TensorProduct A K C) := by
  intro C
  let σ : (⊥ : Ideal A).ResidueField ≃ₐ[A] K :=
    IsLocalization.algEquiv (nonZeroDivisors A) _ K
  let e : (⊥ : Ideal A).Fiber C ≃ₐ[A] K ⊗[A] C := Algebra.TensorProduct.congr σ AlgEquiv.refl
  refine Algebra.IsGeometricallyRegular.of_ringEquiv σ.toRingEquiv e.toRingEquiv (fun x ↦ ?_) h
  change Algebra.TensorProduct.map (σ : _ →ₐ[A] K) (AlgHom.id A C) (x ⊗ₜ[A] (1 : C)) = _
  simp
