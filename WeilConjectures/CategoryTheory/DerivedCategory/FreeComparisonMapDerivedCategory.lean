/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.OfBijectiveCounit
public import WeilConjectures.CategoryTheory.ExactDerivedAdjunction
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Free comparisons of exact functors on derived categories

Let `free₁ ⊣ forget₁` and `free₂ ⊣ forget₂` be adjunctions of exact functors between abelian
categories, `L` and `L'` exact functors and `c : L ⋙ forget₂ ≅ forget₁ ⋙ L'`. On derived
categories, `c` induces `D(c) : D(L) ⋙ D(forget₂) ≅ D(forget₁) ⋙ D(L')`
(`CategoryTheory.Functor.mapDerivedCategoryCompForgetIso`), and the free comparison of `D(L)` for
the derived adjunctions is an isomorphism if the free comparison of `L` is an isomorphism on all
objects (`CategoryTheory.Adjunction.isIso_freeComparison_mapDerivedCategory`).
-/

@[expose] public section

universe w₁ w₂ w₃ w₄

open CategoryTheory Limits

namespace CategoryTheory

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B'] [Abelian A]
  [Abelian A'] [Abelian B] [Abelian B'] [HasDerivedCategory.{w₁} A]
  [HasDerivedCategory.{w₂} A'] [HasDerivedCategory.{w₃} B] [HasDerivedCategory.{w₄} B']
  {free₁ : A' ⥤ A} {forget₁ : A ⥤ A'} {free₂ : B' ⥤ B} {forget₂ : B ⥤ B'}
  [free₁.Additive] [PreservesFiniteLimits free₁] [PreservesFiniteColimits free₁]
  [forget₁.Additive] [PreservesFiniteLimits forget₁] [PreservesFiniteColimits forget₁]
  [free₂.Additive] [PreservesFiniteLimits free₂] [PreservesFiniteColimits free₂]
  [forget₂.Additive] [PreservesFiniteLimits forget₂] [PreservesFiniteColimits forget₂]
  {L : A ⥤ B} {L' : A' ⥤ B'} [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [L'.Additive] [PreservesFiniteLimits L'] [PreservesFiniteColimits L']

/-- The isomorphism `D(L) ⋙ D(forget₂) ≅ D(forget₁) ⋙ D(L')` induced by
`c : L ⋙ forget₂ ≅ forget₁ ⋙ L'`. -/
noncomputable def Functor.mapDerivedCategoryCompForgetIso (c : L ⋙ forget₂ ≅ forget₁ ⋙ L') :
    L.mapDerivedCategory ⋙ forget₂.mapDerivedCategory ≅
      forget₁.mapDerivedCategory ⋙ L'.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso L forget₂).symm ≪≫ Functor.mapDerivedCategoryNatIso c ≪≫
    Functor.mapDerivedCategoryCompIso forget₁ L'

/-- **Free comparisons of exact functors on derived categories.** If the free comparison
`free₂ (L' M) ⟶ L (free₁ M)` is an isomorphism for every object `M`, so is the free comparison of
`D(L)` for the derived adjunctions `D(free₁) ⊣ D(forget₁)` and `D(free₂) ⊣ D(forget₂)`. -/
theorem Adjunction.isIso_freeComparison_mapDerivedCategory (adj₁ : free₁ ⊣ forget₁)
    (adj₂ : free₂ ⊣ forget₂) (c : L ⋙ forget₂ ≅ forget₁ ⋙ L')
    (h : ∀ M, IsIso (freeComparison adj₁ adj₂ L L' c M)) (M : DerivedCategory A') :
    IsIso (freeComparison adj₁.mapExactDerivedCategory adj₂.mapExactDerivedCategory
      L.mapDerivedCategory L'.mapDerivedCategory (Functor.mapDerivedCategoryCompForgetIso c) M) :=
  sorry

end CategoryTheory
