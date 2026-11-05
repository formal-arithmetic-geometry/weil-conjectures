/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurityUnitBaseChangeComp
public import WeilConjectures.CategoryTheory.Adjunction.FreeComparisonComp

/-! # Unit base change for specified factorizations of the left adjoints -/

@[expose] public section

namespace CategoryTheory.Adjunction

variable {A B C A' B' C' : Type*}
  [Category A] [Category B] [Category C] [Category A'] [Category B'] [Category C']
  {F : A ⥤ B} {FR : B ⥤ A} (adjF : F ⊣ FR)
  {G : B ⥤ C} {GR : C ⥤ B} (adjG : G ⊣ GR)
  {H : A ⥤ C} {HR : C ⥤ A} (adjH : H ⊣ HR)
  {F' : A' ⥤ B'} {FR' : B' ⥤ A'} (adjF' : F' ⊣ FR')
  {G' : B' ⥤ C'} {GR' : C' ⥤ B'} (adjG' : G' ⊣ GR')
  {H' : A' ⥤ C'} {HR' : C' ⥤ A'} (adjH' : H' ⊣ HR')
  {TA : A ⥤ A'} {TB : B ⥤ B'} {TC : C ⥤ C'}
  (eF : F ⋙ TB ≅ TA ⋙ F') (eG : G ⋙ TC ≅ TB ⋙ G')
  (h : H ≅ F ⋙ G) (h' : H' ≅ F' ⋙ G')
  {U : C} {U' : C'} (ε : TC.obj U ⟶ U')

end CategoryTheory.Adjunction
