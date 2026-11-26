/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.PopescuResolution

/-!
# Transferring a Popescu resolution along a smooth base

A resolution over a smooth finitely presented auxiliary base `R` gives a resolution over `k`,
provided the original extended singular ideal is contained in the auxiliary one.

## References

* [Stacks, Tag 07FE] (proof, the passage from `R = k[x]` back to `k`)
-/

@[expose] public section

universe u v w

namespace Algebra

private theorem singularIdeal_le_of_smooth_base
    {k R B : Type*} [CommRing k] [CommRing R] [CommRing B]
    [Algebra k R] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    [Smooth k R] : singularIdeal R B ≤ singularIdeal k B := by
  apply Ideal.radical_mono
  apply Ideal.span_mono
  intro b hb
  change Smooth R (Localization.Away b) at hb
  change Smooth k (Localization.Away b)
  have : Smooth R (Localization.Away b) := hb
  exact Smooth.comp k R (Localization.Away b)

/-- A resolution over a smooth finitely presented auxiliary base gives a resolution over
`k`, provided the original extended singular ideal is contained in the auxiliary one. -/
theorem canBePopescuResolved_of_smooth_base
    {k R : Type u} {A : Type v} {C : Type (max u v)} {Λ : Type w}
    [CommRing k] [CommRing R] [CommRing A] [CommRing C] [CommRing Λ]
    [Algebra k R] [Algebra k A] [Algebra k C] [Algebra k Λ]
    [Algebra R C] [Algebra R Λ] [IsScalarTower k R C] [IsScalarTower k R Λ]
    [IsNoetherianRing k] [IsNoetherianRing R]
    [FinitePresentation k A] [FinitePresentation R C] [Smooth k R]
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (β : A →ₐ[k] C) (γ : C →ₐ[R] Λ)
    (hcomp : (γ.restrictScalars k).comp β = α)
    (hideal : popescuIdeal α ≤ popescuIdeal γ)
    (hresolved : CanBePopescuResolved γ q) : CanBePopescuResolved α q := by
  obtain ⟨D, instD, algD, δ, ε, hfp, hδε, hCD, hDq⟩ := hresolved
  let : Algebra k D := ((algebraMap R D).comp (algebraMap k R)).toAlgebra
  have : IsScalarTower k R D := IsScalarTower.of_algebraMap_eq' rfl
  have : FinitePresentation R D := hfp
  have : FinitePresentation k R := inferInstance
  have : FinitePresentation k D := FinitePresentation.trans k R D
  have hD : popescuIdeal ε ≤ popescuIdeal (ε.restrictScalars k) := by
    apply Ideal.radical_mono
    exact Ideal.map_mono (singularIdeal_le_of_smooth_base (k := k) (R := R))
  refine ⟨D, inferInstance, inferInstance,
    (δ.restrictScalars k).comp β, ε.restrictScalars k, inferInstance, ?_,
    hideal.trans (hCD.trans hD), ?_⟩
  · ext a
    have h₁ := DFunLike.congr_fun hδε (β a)
    have h₂ := DFunLike.congr_fun hcomp a
    exact h₁.trans h₂
  · intro hle
    exact hDq (hD.trans hle)

end Algebra
