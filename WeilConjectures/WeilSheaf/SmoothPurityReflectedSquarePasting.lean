/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityReflectedSquareComponents
public import WeilConjectures.CategoryTheory.Adjunction.FreeComparisonComp

/-! # Restriction commutes with pasting of compact-support exchange squares -/

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable {A B C A' B' C' : Type*}
  [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
  {PA : ObjectProperty A} {PB : ObjectProperty B} {PC : ObjectProperty C}
  {PA' : ObjectProperty A'} {PB' : ObjectProperty B'} {PC' : ObjectProperty C'}
  {F : A ⥤ B} {G : B ⥤ C} {F' : A' ⥤ B'} {G' : B' ⥤ C'}
  {TA : A ⥤ A'} {TB : B ⥤ B'} {TC : C ⥤ C'}
  {FR : PA.FullSubcategory ⥤ PB.FullSubcategory}
  {GR : PB.FullSubcategory ⥤ PC.FullSubcategory}
  {FR' : PA'.FullSubcategory ⥤ PB'.FullSubcategory}
  {GR' : PB'.FullSubcategory ⥤ PC'.FullSubcategory}
  (cF : FR ⋙ PB.ι ≅ PA.ι ⋙ F) (cG : GR ⋙ PC.ι ≅ PB.ι ⋙ G)
  (cF' : FR' ⋙ PB'.ι ≅ PA'.ι ⋙ F') (cG' : GR' ⋙ PC'.ι ≅ PB'.ι ⋙ G')
  (hA : ∀ K : PA.FullSubcategory, PA' ((PA.ι ⋙ TA).obj K))
  (hB : ∀ K : PB.FullSubcategory, PB' ((PB.ι ⋙ TB).obj K))
  (hC : ∀ K : PC.FullSubcategory, PC' ((PC.ι ⋙ TC).obj K))
  (eF : F ⋙ TB ≅ TA ⋙ F') (eG : G ⋙ TC ≅ TB ⋙ G')

end CategoryTheory.ObjectProperty

namespace CategoryTheory.Adjunction

variable {A B C A' B' C' : Type*}
  [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
  {F : A ⥤ B} {G : B ⥤ C} {F' : A' ⥤ B'} {G' : B' ⥤ C'}
  {TA SA : A ⥤ A'} {TB SB : B ⥤ B'} {TC SC : C ⥤ C'}
  (aA : SA ≅ TA) (aB : SB ≅ TB) (aC : SC ≅ TC)
  (eF : F ⋙ TB ≅ TA ⋙ F') (eG : G ⋙ TC ≅ TB ⋙ G')

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  {F : A ⥤ B} {F' : A' ⥤ B'} {T S : A ⥤ A'} {U V : B ⥤ B'}

end CategoryTheory.Functor
