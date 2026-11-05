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

/-- The reflection of an ambient square through specified inclusion comparisons. -/
noncomputable def preimageIso_comparisonSquare : FR ⋙ TR' ≅ TR ⋙ FR' :=
  (PB'.fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ cT' ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight cF _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft PA.ι e ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight cT.symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ cF'.symm ≪≫
      (Functor.associator _ _ _).symm)

/-- The inverse reflected square keeps the four inclusion comparisons explicit. -/
lemma preimageIso_comparisonSquare_inv_app_hom (K : PA.FullSubcategory) :
    ((preimageIso_comparisonSquare cF cF' cT cT' e).inv.app K).hom =
      cF'.hom.app (TR.obj K) ≫ F'.map (cT.hom.app K) ≫ e.inv.app K.obj ≫
        T'.map (cF.inv.app K) ≫ cT'.inv.app (FR.obj K) := by
  simp [preimageIso_comparisonSquare]

end CategoryTheory.ObjectProperty
