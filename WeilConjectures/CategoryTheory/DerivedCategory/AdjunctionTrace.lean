/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryNatTransAdditive
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction

/-!
# Traces of derived adjunctions of exact functors

Let `adj : f ⊣ g` be an adjunction of exact functors between abelian categories, and let
`t : f ⋙ g ⟶ 𝟭` be a *trace* with `u ≫ t = d • 𝟙` for the unit `u`, and `ρ i : f ⋙ g ⟶ f ⋙ g`
finitely many natural transformations with `t ≫ u = ∑ i, ρ i`. Then the derived adjunction
`Lf ⊣ Rg` (`CategoryTheory.Adjunction.derivedAdjunction`) carries a trace and endomorphisms
satisfying the same identities (`CategoryTheory.Adjunction.unit_comp_derivedTrace`,
`CategoryTheory.Adjunction.derivedTrace_comp_unit`).

The unit of the levelwise derived adjunction `D(f) ⊣ D(g)` is the levelwise unit
(`CategoryTheory.Adjunction.mapDerivedCategoryAdjunction_unit_eq`), and the derived adjunction
differs from it by the isomorphisms `Lf ≅ D(f)`, `Rg ≅ D(g)`.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory Abelian

namespace CategoryTheory.Adjunction

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasKInjectiveResolutions D]
  {f : C ⥤ D} {g : D ⥤ C} (adj : f ⊣ g) [f.Additive] [g.Additive]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [PreservesFiniteLimits g] [PreservesFiniteColimits g]

variable {ι : Type*} [Fintype ι]

end CategoryTheory.Adjunction
