/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import WeilConjectures.ConstructibleSheaf.KernelCokernel

/-!
# Constructible sheaves form a weak Serre subcategory

Let `Λ` be a ring. We package constructibility of sheaves of `Λ`-modules on the small étale
site of `X` as an object property `AlgebraicGeometry.Scheme.constructibleSheaves X Λ` and show
that it is closed under isomorphisms, cokernels and finite direct sums, under kernels when `Λ` is
noetherian, and under extensions when `Λ` is finite. Consequently, for a finite ring `Λ`, the
constructible sheaves form a weak Serre subcategory of the category of sheaves of `Λ`-modules
(`AlgebraicGeometry.Scheme.constructibleSheaves_isWeakSerre`).
(blueprint: `thm-constructible-serre`)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) (Λ : Type (u + 1)) [Ring Λ]

/-- The property of a sheaf of `Λ`-modules on the small étale site of `X` of being
constructible (`AlgebraicGeometry.Scheme.IsConstructibleSheaf`).
(blueprint: `thm-constructible-serre`) -/
def constructibleSheaves : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fun F ↦ IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F

instance : (constructibleSheaves X Λ).IsClosedUnderIsomorphisms where
  of_iso e h := by
    have : IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) _ := h
    exact IsConstructibleSheaf.of_iso e

/-- **Cokernels of morphisms between constructible sheaves are constructible.**
(blueprint: `thm-constructible-serre`) -/
instance : (constructibleSheaves X Λ).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, ⟨hX, hY⟩⟩
    have : IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) _ := hX
    have : IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) _ := hY
    have := IsConstructibleSheaf.cokernel f
    exact IsConstructibleSheaf.of_iso (F := cokernel f)
      ((cokernelIsCokernel f).coconePointUniqueUpToIso hk)

/-- **Kernels of morphisms between constructible sheaves of modules over a noetherian ring are
constructible.** (blueprint: `thm-constructible-serre`) -/
instance [IsNoetherianRing Λ] : (constructibleSheaves X Λ).IsClosedUnderKernels where
  kernels_le := by
    rintro _ ⟨f, k, hk, ⟨hX, hY⟩⟩
    have : IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) _ := hX
    have : IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) _ := hY
    have := IsConstructibleSheaf.kernel f
    exact IsConstructibleSheaf.of_iso (F := kernel f) ((kernelIsKernel f).conePointUniqueUpToIso hk)

/-- **Extensions of constructible sheaves of modules over a finite ring are constructible.**
(blueprint: `thm-constructible-serre`) -/
instance [Finite Λ] : (constructibleSheaves X Λ).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have : IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₁ := h₁
    have : IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
      (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) S.X₃ := h₃
    exact IsConstructibleSheaf.of_shortExact hS

/-- **Finite direct sums of constructible sheaves are constructible.**
(blueprint: `thm-constructible-serre`) -/
theorem constructibleSheaves_biprod {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hF : constructibleSheaves X Λ F) (hG : constructibleSheaves X Λ G) :
    constructibleSheaves X Λ (F ⊞ G) := by
  have : IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) F := hF
  have : IsConstructibleSheaf (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N)
    (CA := fun M : ModuleCat.{u + 1} Λ ↦ M) G := hG
  exact IsConstructibleSheaf.biprod F G

/-- **Constructible sheaves form a weak Serre subcategory.** Let `Λ` be a ring. Kernels (for
`Λ` noetherian) and cokernels of morphisms between constructible sheaves of `Λ`-modules on the
small étale site of `X`, and finite direct sums of constructible sheaves, are constructible; if
`Λ` is finite, the middle term of a short exact sequence whose outer terms are constructible is
constructible. Hence, for `Λ` finite, the constructible sheaves are closed under isomorphisms,
kernels, cokernels and extensions. (blueprint: `thm-constructible-serre`) -/
theorem constructibleSheaves_isWeakSerre [Finite Λ] :
    (constructibleSheaves X Λ).IsClosedUnderIsomorphisms ∧
      (constructibleSheaves X Λ).IsClosedUnderKernels ∧
      (constructibleSheaves X Λ).IsClosedUnderCokernels ∧
      (constructibleSheaves X Λ).IsClosedUnderExtensions :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme
