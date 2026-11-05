/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.WeilSheaf.Native.Projection.ProjectionPasting

/-! # Transport of projection squares between isomorphic realization functors -/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {I : C ⥤ D} {P : D ⥤ C} {I' : C' ⥤ D'} {P' : D' ⥤ C'}
  {NC FC : C ⥤ C'} {ND FD : D ⥤ D'}
  {TC : C × C ⥤ C} {TD : D × D ⥤ D}
  {TC' : C' × C' ⥤ C'} {TD' : D' × D' ⥤ D'}

/-- Change the realization functors in a pushforward comparison. -/
def projectionPushForgetIso (δ : I ⋙ ND ≅ NC ⋙ I') (aC : NC ≅ FC) (aD : ND ≅ FD) :
    I ⋙ FD ≅ FC ⋙ I' :=
  Functor.isoWhiskerLeft I aD.symm ≪≫ δ ≪≫ Functor.isoWhiskerRight aC I'

/-- Change the realization functor in a tensor comparison. -/
def projectionTensorForgetIso (tC : TC ⋙ NC ≅ NC.prod NC ⋙ TC') (aC : NC ≅ FC) :
    TC ⋙ FC ≅ FC.prod FC ⋙ TC' :=
  Functor.isoWhiskerLeft TC aC.symm ≪≫ tC ≪≫ Functor.isoWhiskerRight (NatIso.prod aC aC) TC'

set_option backward.isDefEq.respectTransparency false in
/-- Isomorphic realization functors carry the same projection-formula square. -/
theorem projectionForgetSquare_of_iso
    (δ : I ⋙ ND ≅ NC ⋙ I') (κ : P ⋙ NC ≅ ND ⋙ P')
    (tC : TC ⋙ NC ≅ NC.prod NC ⋙ TC') (tD : TD ⋙ ND ≅ ND.prod ND ⋙ TD')
    (aC : NC ≅ FC) (aD : ND ≅ FD)
    (p : I.prod (𝟭 D) ⋙ TD ⟶ (𝟭 C).prod P ⋙ TC ⋙ I)
    (p' : I'.prod (𝟭 D') ⋙ TD' ⟶ (𝟭 C').prod P' ⋙ TC' ⋙ I')
    (h : ProjectionForgetSquare δ κ tC tD p p') :
    ProjectionForgetSquare (projectionPushForgetIso δ aC aD)
      (projectionPushForgetIso κ aD aC) (projectionTensorForgetIso tC aC)
      (projectionTensorForgetIso tD aD) p p' := by
  intro M N
  have hn := p'.naturality (Prod.mkHom (aC.hom.app M) (aD.hom.app N))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.comp_obj, Functor.prod_obj,
    Functor.id_map, Functor.id_obj] at hn
  have hnD := aD.inv.naturality (p.app (M, N))
  dsimp only [Functor.comp_obj, Functor.prod_obj, Functor.id_obj] at hnD
  have hc : TC'.map (Prod.mkHom (aC.hom.app M) (aC.hom.app (P.obj N))) ≫
      TC'.map (Prod.mkHom (𝟙 _) (aC.inv.app (P.obj N) ≫ κ.hom.app N ≫
        P'.map (aD.hom.app N))) =
    TC'.map (Prod.mkHom (𝟙 _) (κ.hom.app N)) ≫
      TC'.map (Prod.mkHom (aC.hom.app M) (P'.map (aD.hom.app N))) := by
    simp only [← TC'.map_comp]
    congr 1
    ext <;> simp
  have hd : TD'.map (Prod.mkHom (aD.hom.app (I.obj M)) (aD.hom.app N)) ≫
      TD'.map (Prod.mkHom (aD.inv.app (I.obj M) ≫ δ.hom.app M ≫
        I'.map (aC.hom.app M)) (𝟙 _)) =
    TD'.map (Prod.mkHom (δ.hom.app M) (𝟙 _)) ≫
      TD'.map (Prod.mkHom (I'.map (aC.hom.app M)) (aD.hom.app N)) := by
    simp only [← TD'.map_comp]
    congr 1
    ext <;> simp
  simp only [projectionPushForgetIso, projectionTensorForgetIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, NatIso.prod,
    NatTrans.prod, Functor.comp_obj, Functor.prod_obj, Functor.id_obj, Category.assoc]
  rw [← reassoc_of% hnD]
  simp only [Functor.map_comp, Category.assoc]
  rw [← I'.map_comp_assoc, Iso.hom_inv_id_app, I'.map_id, Category.id_comp]
  rw [← I'.map_comp, hc, I'.map_comp]
  rw [← I'.map_comp_assoc, reassoc_of% (h M N), ← reassoc_of% hn]
  rw [← Category.assoc, ← Category.assoc, hd]
  simp only [Category.assoc]

end CategoryTheory
