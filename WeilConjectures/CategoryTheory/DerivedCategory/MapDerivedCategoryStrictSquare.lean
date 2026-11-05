/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Localizing a strict square of exact realizations

Consider additive functors `Φ₁ : C ⥤ A₁`, `Φ₀ : C ⥤ A₀`, `τ₁ τ₀ : C ⥤ C'`, a semilinear arrow
`δ : Φ₁ ⟶ Φ₀ ⋙ r` and exact functors `r, u₁, u₀, r', s₁, s₀, o` related by isomorphisms
`p : r ⋙ u₁ ≅ u₀ ⋙ r'`, `c : r' ⋙ s₁ ≅ s₀` and realizations `Bᵢ : Φᵢ ⋙ uᵢ ⋙ sᵢ ≅ τᵢ ⋙ o`.
If the evident square of ordinary functors commutes with `σ : τ₁ ⟶ τ₀`, then on every complex
`P` the localized square, formed with the derived comparison isomorphisms
`Functor.mapDerivedCategoryCompIso` and `Functor.mapDerivedCategoryNatIso`, commutes.
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C C' A₁ A₀ B₁ B₀ E : Type*} [Category C] [Category C'] [Category A₁] [Category A₀]
  [Category B₁] [Category B₀] [Category E] [Preadditive C] [Abelian C'] [Abelian A₁]
  [Abelian A₀] [Abelian B₁] [Abelian B₀] [Abelian E]
  [HasDerivedCategory C'] [HasDerivedCategory A₁] [HasDerivedCategory A₀]
  [HasDerivedCategory B₁] [HasDerivedCategory B₀] [HasDerivedCategory E]
  (Φ₁ : C ⥤ A₁) (Φ₀ : C ⥤ A₀) (τ₁ τ₀ : C ⥤ C') [Φ₁.Additive] [Φ₀.Additive]
  [τ₁.Additive] [τ₀.Additive]
  (r : A₀ ⥤ A₁) (u₁ : A₁ ⥤ B₁) (u₀ : A₀ ⥤ B₀) (r' : B₀ ⥤ B₁) (s₁ : B₁ ⥤ E) (s₀ : B₀ ⥤ E)
  (o : C' ⥤ E)
  [r.Additive] [PreservesFiniteLimits r] [PreservesFiniteColimits r]
  [u₁.Additive] [PreservesFiniteLimits u₁] [PreservesFiniteColimits u₁]
  [u₀.Additive] [PreservesFiniteLimits u₀] [PreservesFiniteColimits u₀]
  [r'.Additive] [PreservesFiniteLimits r'] [PreservesFiniteColimits r']
  [s₁.Additive] [PreservesFiniteLimits s₁] [PreservesFiniteColimits s₁]
  [s₀.Additive] [PreservesFiniteLimits s₀] [PreservesFiniteColimits s₀]
  [o.Additive] [PreservesFiniteLimits o] [PreservesFiniteColimits o]

variable {Φ₁ Φ₀ τ₁ τ₀ r u₁ u₀ r' s₁ s₀ o}

section Transport

variable {𝒜₁ 𝒜₀ ℬ₁ ℬ₀ ℰ : Type*} [Category 𝒜₁] [Category 𝒜₀] [Category ℬ₁] [Category ℬ₀]
  [Category ℰ] {R : 𝒜₀ ⥤ 𝒜₁} {U₁ : 𝒜₁ ⥤ ℬ₁} {U₀ : 𝒜₀ ⥤ ℬ₀} {R' : ℬ₀ ⥤ ℬ₁}
  {S₁ : ℬ₁ ⥤ ℰ} {S₀ : ℬ₀ ⥤ ℰ}

end Transport

end CategoryTheory.Functor
