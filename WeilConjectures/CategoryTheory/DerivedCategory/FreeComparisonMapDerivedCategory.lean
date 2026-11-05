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

section HomologicalComplex

variable {A A' B B' : Type*} [Category A] [Category A'] [Category B] [Category B']
  [Preadditive A] [Preadditive A'] [Preadditive B] [Preadditive B'] {ι : Type*}
  (cs : ComplexShape ι) {free₁ : A' ⥤ A} {forget₁ : A ⥤ A'} {free₂ : B' ⥤ B} {forget₂ : B ⥤ B'}
  [free₁.Additive] [forget₁.Additive] [free₂.Additive] [forget₂.Additive]
  {L : A ⥤ B} {L' : A' ⥤ B'} [L.Additive] [L'.Additive]

end HomologicalComplex

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

section Helpers

variable {C D E : Type*} [Category C] [Category D] [Category E] [Abelian C] [Abelian D]
  [Abelian E] [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]

namespace Functor

variable (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive] [PreservesFiniteLimits F]
  [PreservesFiniteColimits F] [PreservesFiniteLimits G] [PreservesFiniteColimits G]

end Functor

end Helpers

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

end CategoryTheory
