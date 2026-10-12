/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible

/-!
# Constructible étale sheaves of modules over a finite ring form a weak Serre subcategory

For a finite ring `Λ`, the constructible sheaves of `Λ`-modules on the small étale site of a
scheme are closed under kernels, cokernels and extensions
(`AlgebraicGeometry.Scheme.IsConstructibleSheaf.kernel`, `IsConstructibleSheaf.cokernel`,
`IsConstructibleSheaf.of_shortExact`, blueprint `thm-constructible-serre`). This file records
these closure properties as instances on the object property
`AlgebraicGeometry.Etale.constructibleSheaf`, so that the bounded constructible derived category
`Dᵇc(X, Λ)` is a triangulated subcategory of `D(X_ét)`
(`AlgebraicGeometry.Etale.DerivedCategory.boundedConstructible_isTriangulated`) without further
hypotheses.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

open Scheme

variable (Λ : Type (u + 1)) [Ring Λ] (X : Scheme.{u})

instance [IsNoetherianRing Λ] :
    (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).IsClosedUnderKernels where
  kernels_le := by
    rintro K _ ⟨_, k, hk, ⟨f, hF, hG⟩⟩
    have : IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) _ := hF
    have : IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) _ := hG
    have := IsConstructibleSheaf.kernel f
    exact IsConstructibleSheaf.of_iso (IsLimit.conePointUniqueUpToIso (kernelIsKernel f) hk)

instance : (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).IsClosedUnderCokernels where
  cokernels_le := by
    rintro K _ ⟨_, k, hk, ⟨f, hF, hG⟩⟩
    have : IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) _ := hF
    have : IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) _ := hG
    have := IsConstructibleSheaf.cokernel f
    exact IsConstructibleSheaf.of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)

instance [Finite Λ] :
    (Etale.constructibleSheaf (ModuleCat.{u + 1} Λ) X).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have : IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁ := h₁
    have : IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
        (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃ := h₃
    exact IsConstructibleSheaf.of_shortExact hS

end AlgebraicGeometry.Etale
