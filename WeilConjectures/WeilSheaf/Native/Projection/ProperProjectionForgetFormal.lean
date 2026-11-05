/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.UncurriedComparison
public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionPasting
public import WeilConjectures.WeilSheaf.Native.Projection.GeometricProjectionNaturality

/-! # The proper projection square in abstract tensor coordinates -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Adjunction

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [MonoidalCategory C'] [MonoidalCategory D']
  {F : D ⥤ C} {G : C ⥤ D} {F' : D' ⥤ C'} {G' : C' ⥤ D'}
  {NC : C ⥤ C'} {ND : D ⥤ D'} {TC : C × C ⥤ C} {TD : D × D ⥤ D}

/-- Uncurry the proper projection square before specializing the categories. -/
lemma projectionForgetSquare_of_comparisonCompatible
    (adj : F ⊣ G) (adj' : F' ⊣ G') [F'.OplaxMonoidal]
    (α : ND ⋙ F' ≅ F ⋙ NC)
    (φ : (Functor.postcompose₂.obj F).obj (Functor.curry.obj TD) ⟶
      (((Functor.whiskeringLeft₂ C).obj F).obj F).obj (Functor.curry.obj TC))
    (tC : TC ⋙ NC ≅ NC.prod NC ⋙ Functor.uncurry.obj (curriedTensor C'))
    (tD : TD ⋙ ND ≅ ND.prod ND ⋙ Functor.uncurry.obj (curriedTensor D'))
    (h : ComparisonCompatible α φ (Functor.OplaxMonoidal.δNatTrans F')
      (Functor.curryCompIsoOfIso' tC) (Functor.curryCompIsoOfIso' tD))
    [IsIso (mateEquiv adj adj' α.hom).natTrans] :
    ProjectionForgetSquare (asIso (mateEquiv adj adj' α.hom).natTrans) α.symm tC tD
      (Functor.uncurryRightProjection (adj.rightAdjointProjectionMap φ))
      adj'.uncurriedProjectionMorphismNatTrans := by
  intro M N
  have hh := map_rightAdjointProjectionMap_comp_mateEquiv adj adj' h M N
  simpa only [Functor.uncurryRightProjection, uncurriedProjectionMorphismNatTrans,
    Functor.curryCompIsoOfIso', Functor.comp_obj, Functor.prod_obj, Functor.id_obj,
    asIso_hom, Iso.symm_hom, Functor.uncurry_obj_map, curriedTensor_map_app,
    curriedTensor_obj_map, id_whiskerRight, whiskerLeft_id, Category.comp_id,
    Category.id_comp] using hh

end CategoryTheory.Adjunction
