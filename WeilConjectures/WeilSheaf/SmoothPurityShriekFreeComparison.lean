/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedAdjunction
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraDerivedRightAdjointFree
public import WeilConjectures.CategoryTheory.Adjunction.FreeComparisonComp
public import WeilConjectures.CategoryTheory.DerivedCategory.FreeComparisonMapDerivedCategory
public import WeilConjectures.CategoryTheory.Endofunctor.IsoAlgebraFreeComparison

/-! # Free Weil objects and an exact functor followed by a derived direct image -/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

universe v

variable {C D E : Type*} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  [Abelian C] [IsGrothendieckAbelian.{v} C]
  [Abelian D] [IsGrothendieckAbelian.{v} D]
  [Abelian E] [IsGrothendieckAbelian.{v} E]
  {F : C ⥤ C} [F.Additive] [F.IsEquivalence]
  {G : D ⥤ D} [G.Additive] [G.IsEquivalence]
  {H : E ⥤ E} [H.Additive] [H.IsEquivalence]
  {L₁ : C ⥤ D} [L₁.Additive] [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
  [PreservesColimitsOfShape (Discrete ℤ) L₁]
  {L₂ : D ⥤ E} [L₂.Additive]
  (e₁ : L₁ ⋙ G ≅ F ⋙ L₁) (e₂ : L₂ ⋙ H ≅ G ⋙ L₂)
  [HasDerivedCategory.{v} C] [HasDerivedCategory.{v} D] [HasDerivedCategory.{v} E]
  [HasDerivedCategory.{v} (IsoAlgebra F)] [HasDerivedCategory.{v} (IsoAlgebra G)]
  [HasDerivedCategory.{v} (IsoAlgebra H)]
  [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions (IsoAlgebra G)]

end CategoryTheory.Endofunctor.IsoAlgebra
