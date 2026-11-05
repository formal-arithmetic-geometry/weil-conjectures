/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit

/-!

# The derived unit on a single object, after an exact functor

Let `f ⊣ g` be an adjunction between abelian categories with `f` exact, and let `h` be an exact
functor out of the source of `f`. For an object `M`, the unit of the derived adjunction
`f.leftDerivedFunctor ⊣ g.rightDerivedFunctor` at `M[0]` is a morphism
`M[0] ⟶ Rg (Lf (M[0])) ≅ Rg ((f M)[0])`. Its cohomology in degree `0` is the unit
`M ⟶ g (f M)` of `f ⊣ g`, and its cohomology in degree `n > 0` has target `Rⁿg (f M)`.
Hence it becomes an isomorphism after applying `h` levelwise as soon as `h` inverts the unit
`M ⟶ g (f M)` and kills the higher derived functors `Rⁿg (f M)`
(`CategoryTheory.Adjunction.isIso_mapDerivedCategory_map_derivedAdjunction_unit_app`).

-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory Abelian

namespace CategoryTheory.Adjunction

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E]
  [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [HasKInjectiveResolutions D] [EnoughInjectives D]
  {f : C ⥤ D} {g : D ⥤ C} [f.Additive] [g.Additive] [f.PreservesKFlatQuasiIso]
  [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  (adj : f ⊣ g) (h : C ⥤ E) [h.Additive] [PreservesFiniteLimits h] [PreservesFiniteColimits h]

end CategoryTheory.Adjunction
