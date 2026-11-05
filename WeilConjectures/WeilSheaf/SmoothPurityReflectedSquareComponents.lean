/-
Copyright (c) 2026 The Weil Conjectures contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.CategoryTheory.ObjectProperty.LiftSquareIso

/-! # Restricted squares with specified direct-image comparisons -/

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  {PA : ObjectProperty A} {PB : ObjectProperty B}
  {PA' : ObjectProperty A'} {PB' : ObjectProperty B'}
  {F : A ⥤ B} {F' : A' ⥤ B'} {T : A ⥤ A'} {T' : B ⥤ B'}
  {FR : PA.FullSubcategory ⥤ PB.FullSubcategory}
  {FR' : PA'.FullSubcategory ⥤ PB'.FullSubcategory}
  (cF : FR ⋙ PB.ι ≅ PA.ι ⋙ F) (cF' : FR' ⋙ PB'.ι ≅ PA'.ι ⋙ F')
  (hT : ∀ K : PA.FullSubcategory, PA' ((PA.ι ⋙ T).obj K))
  (hT' : ∀ K : PB.FullSubcategory, PB' ((PB.ι ⋙ T').obj K))
  (e : F ⋙ T' ≅ T ⋙ F')

/-- The ambient square reflected through the bounded inclusions. -/
noncomputable def preimageIso_liftSquareWithComparisons :
    FR ⋙ PB'.lift (PB.ι ⋙ T') hT' ≅ PA'.lift (PA.ι ⋙ T) hT ⋙ FR' :=
  (PB'.fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (PB'.liftCompιIso (PB.ι ⋙ T') hT') ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight cF _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft PA.ι e ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (PA'.liftCompιIso (PA.ι ⋙ T) hT).symm _ ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ cF'.symm ≪≫
      (Functor.associator _ _ _).symm)

end CategoryTheory.ObjectProperty
