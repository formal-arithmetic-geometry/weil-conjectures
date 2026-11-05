/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityReflectedSquareComponents

/-! # Reflected squares in all four comparison coordinates -/

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  {PA : ObjectProperty A} {PB : ObjectProperty B}
  {PA' : ObjectProperty A'} {PB' : ObjectProperty B'}
  {F : A ⥤ B} {F' : A' ⥤ B'} {T : A ⥤ A'} {T' : B ⥤ B'}
  {FR : PA.FullSubcategory ⥤ PB.FullSubcategory}
  {FR' : PA'.FullSubcategory ⥤ PB'.FullSubcategory}
  {TR : PA.FullSubcategory ⥤ PA'.FullSubcategory}
  {TR' : PB.FullSubcategory ⥤ PB'.FullSubcategory}
  (cF : FR ⋙ PB.ι ≅ PA.ι ⋙ F) (cF' : FR' ⋙ PB'.ι ≅ PA'.ι ⋙ F')
  (cT : TR ⋙ PA'.ι ≅ PA.ι ⋙ T) (cT' : TR' ⋙ PB'.ι ≅ PB.ι ⋙ T')
  (e : F ⋙ T' ≅ T ⋙ F')

end CategoryTheory.ObjectProperty
