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

/-- Restricting a pasted square gives the paste of the two restricted squares, using
exactly the pasted inclusion comparisons for the composite direct images. -/
lemma preimageIso_liftSquareWithComparisons_comp :
    preimageIso_liftSquareWithComparisons
        (Adjunction.compForgetIso cF cG) (Adjunction.compForgetIso cF' cG')
        hA hC (Adjunction.compForgetIso eF eG) =
      Adjunction.compForgetIso
        (preimageIso_liftSquareWithComparisons cF cF' hA hB eF)
        (preimageIso_liftSquareWithComparisons cG cG' hB hC eG) := by
  apply Iso.ext
  apply NatTrans.ext
  intro K
  apply PC'.ι.map_injective
  rw [show PC'.ι.map _ = _ from
    preimageIso_liftSquareWithComparisons_hom_app_hom
      (Adjunction.compForgetIso cF cG) (Adjunction.compForgetIso cF' cG')
      hA hC (Adjunction.compForgetIso eF eG) K]
  simp only [Adjunction.compForgetIso, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.map_comp, Functor.map_id,
    Functor.comp_obj, Functor.comp_map, Category.assoc]
  rw [preimageIso_liftSquareWithComparisons_hom_app_hom]
  rw [← cG'.hom.naturality_assoc]
  simp only [Functor.comp_map, Functor.comp_obj, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [preimageIso_liftSquareWithComparisons_hom_app_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← eG.hom.naturality_assoc]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc,
    ← G'.map_comp_assoc, Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]

end CategoryTheory.ObjectProperty
