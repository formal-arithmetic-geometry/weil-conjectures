/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryStrictSquare
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.UnitRetraction

/-!
# Universality of localized strict arrows

Let `adj : E ⊣ r` be an adjunction between abelian categories, where `r` is exact and `E`
preserves quasi-isomorphisms between K-flat complexes. On a K-flat complex `K`, the localized
unit `Q(K) ⟶ D(r)(Q(E(K)))` is a universal arrow to `D(r)`: it is the unit of the derived
adjunction, up to the counit of the left derived functor of `E` at `K`.

Consequently, for a termwise arrow `δ : Φ₁ ⟶ Φ₀ ⋙ r` whose transposes are invertible on the
terms of a complex `P` with `Φ₁(P)` K-flat, the localized arrow
`Functor.strictSquareArrow Φ₁ Φ₀ r δ P` is universal.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Abelian

namespace CategoryTheory.Functor

variable {A₁ A₀ : Type*} [Category A₁] [Category A₀] [Abelian A₁] [Abelian A₀]
  [MonoidalCategory A₁] [MonoidalPreadditive A₁]
  [HasCountableCoproducts A₁]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ A₁), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A₁), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ A₁), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ A₁] [HasExactColimitsOfShape ℤ A₁]
  [∀ (X : A₁), PreservesColimitsOfShape ℤ ((curriedTensor A₁).obj X)]
  [∀ (X : A₁), PreservesColimitsOfShape ℤ ((curriedTensor A₁).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution A₁]
  [HasDerivedCategory A₁] [HasDerivedCategory A₀] [HasKInjectiveResolutions A₀]
  {E : A₁ ⥤ A₀} {r : A₀ ⥤ A₁} [E.Additive] [r.Additive] [E.PreservesKFlatQuasiIso]
  [PreservesFiniteLimits r] [PreservesFiniteColimits r]

variable {C : Type*} [Category C] [Preadditive C] (Φ₁ : C ⥤ A₁) (Φ₀ : C ⥤ A₀)
  [Φ₁.Additive] [Φ₀.Additive]

end CategoryTheory.Functor
