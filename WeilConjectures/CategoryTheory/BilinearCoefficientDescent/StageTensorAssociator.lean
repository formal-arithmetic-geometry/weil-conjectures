/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent
public import WeilConjectures.CategoryTheory.StageSystem.IsoOfTransport

/-! # Associator representatives in a directed tensor family

Scalar-compatible natural associators at the finite stages descend to an isomorphism of the
common-stage tensor objects, with the prescribed representative at every common stage.
The derived-tensor application follows Stacks 06YS, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u v
open CategoryTheory

namespace CategoryTheory.BilinearCoefficientDescent

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  (S : StageSystem C) (U : Family S S S)
  (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
  (α : ∀ i (X Y Z : C i),
    (U.U i).obj ((U.U i).obj (X, Y), Z) ≅ (U.U i).obj (X, (U.U i).obj (Y, Z)))
  (hn : ∀ i {X X' Y Y' Z Z' : C i} (f : X ⟶ X') (g : Y ⟶ Y') (h : Z ⟶ Z'),
    (U.U i).map (Prod.mkHom ((U.U i).map (Prod.mkHom f g)) h) ≫ (α i X' Y' Z').hom =
      (α i X Y Z).hom ≫ (U.U i).map (Prod.mkHom f ((U.U i).map (Prod.mkHom g h))))
  (hc : ∀ {i j : I} (h : i ≤ j) (X Y Z : C i),
    (S.T h).map (α i X Y Z).hom ≫ (U.comparison h).hom.app (X, (U.U i).obj (Y, Z)) ≫
        (U.U j).map (Prod.mkHom (𝟙 _) ((U.comparison h).hom.app (Y, Z))) =
      (U.comparison h).hom.app ((U.U i).obj (X, Y), Z) ≫
        (U.U j).map (Prod.mkHom ((U.comparison h).hom.app (X, Y)) (𝟙 _)) ≫
        (α j ((S.T h).obj X) ((S.T h).obj Y) ((S.T h).obj Z)).hom)


set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.BilinearCoefficientDescent.output

omit [IsDirectedOrder I] in
/-- Transporting a common-stage endpoint identification along `k : L ≤ H`
(copied from `StageTensorBraiding`). -/
private theorem endpoint_tower (X Y : S.PairCategory) {L H : I}
    (h : join X.stage Y.stage ≤ L) (k : L ≤ H) :
    (S.assoc h k).hom.app (output U join left right (X, Y)).obj ≫
        (endpoint U join left right (X, Y) (h.trans k)).hom =
      (S.T k).map (endpoint U join left right (X, Y) h).hom ≫
        (U.comparison k).hom.app (X.toStage ((left _ _).trans h),
          Y.toStage ((right _ _).trans h)) ≫
        (U.U H).map (Prod.mkHom
          ((S.assoc ((left _ _).trans h) k).hom.app X.obj)
          ((S.assoc ((right _ _).trans h) k).hom.app Y.obj)) := by
  dsimp only [endpoint, output, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom,
    Iso.app_hom]
  rw [Functor.map_comp]
  simp only [Iso.prod_hom, Iso.app_hom, Category.assoc]
  have hn := (U.comparison k).hom.naturality
    (Prod.mkHom ((S.assoc (left X.stage Y.stage) h).hom.app X.obj)
      ((S.assoc (right X.stage Y.stage) h).hom.app Y.obj))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  rw [reassoc_of% hn]
  rw [← Functor.map_comp]
  have he :
      Prod.mkHom ((S.T k).map ((S.assoc (left X.stage Y.stage) h).hom.app X.obj))
        ((S.T k).map ((S.assoc (right X.stage Y.stage) h).hom.app Y.obj)) ≫
        Prod.mkHom ((S.assoc ((left X.stage Y.stage).trans h) k).hom.app X.obj)
          ((S.assoc ((right X.stage Y.stage).trans h) k).hom.app Y.obj) =
      Prod.mkHom ((S.assoc h k).hom.app (X.toStage (left _ _)))
        ((S.assoc h k).hom.app (Y.toStage (right _ _))) ≫
        Prod.mkHom ((S.assoc (left X.stage Y.stage) (h.trans k)).hom.app X.obj)
          ((S.assoc (right X.stage Y.stage) (h.trans k)).hom.app Y.obj) := by
    exact Prod.ext (S.cocycle _ _ _ _) (S.cocycle _ _ _ _)
  rw [he, Functor.map_comp]
  simp only [← Category.assoc]
  have ht := U.tower h k (X.toStage (left _ _)) (Y.toStage (right _ _))
  simp only [← Category.assoc] at ht
  rw [ht]

/-- The endpoint identification of the left-nested tensor `(X ⊗ Y) ⊗ Z` at a common stage. -/
private def leftEndpoint (X Y Z : S.PairCategory) {L : I}
    (hS : join (join X.stage Y.stage) Z.stage ≤ L) :
    (S.T hS).obj (output U join left right (output U join left right (X, Y), Z)).obj ≅
      (U.U L).obj ((U.U L).obj (X.toStage ((left _ _).trans ((left _ _).trans hS)),
        Y.toStage ((right _ _).trans ((left _ _).trans hS))),
        Z.toStage ((right _ _).trans hS)) :=
  endpoint U join left right (output U join left right (X, Y), Z) hS ≪≫
    (U.U L).mapIso (Iso.prod
      (endpoint U join left right (X, Y) ((left _ _).trans hS)) (Iso.refl _))

/-- The endpoint identification of the right-nested tensor `X ⊗ (Y ⊗ Z)` at a common stage. -/
private def rightEndpoint (X Y Z : S.PairCategory) {L : I}
    (hT : join X.stage (join Y.stage Z.stage) ≤ L) :
    (S.T hT).obj (output U join left right (X, output U join left right (Y, Z))).obj ≅
      (U.U L).obj (X.toStage ((left _ _).trans hT),
        (U.U L).obj (Y.toStage ((left _ _).trans ((right _ _).trans hT)),
          Z.toStage ((right _ _).trans ((right _ _).trans hT)))) :=
  endpoint U join left right (X, output U join left right (Y, Z)) hT ≪≫
    (U.U L).mapIso (Iso.prod (Iso.refl _)
      (endpoint U join left right (Y, Z) ((right _ _).trans hT)))

omit [IsDirectedOrder I] in
/-- The endpoint tower law for the left-nested endpoint `(X ⊗ Y) ⊗ Z`. -/
private theorem leftEndpoint_tower (X Y Z : S.PairCategory) {L H : I}
    (hS : join (join X.stage Y.stage) Z.stage ≤ L) (k : L ≤ H) :
    (S.assoc hS k).hom.app
        (output U join left right (output U join left right (X, Y), Z)).obj ≫
        (leftEndpoint S U join left right X Y Z (hS.trans k)).hom =
      (S.T k).map (leftEndpoint S U join left right X Y Z hS).hom ≫
        (U.comparison k).hom.app (_, _) ≫
        (U.U H).map (Prod.mkHom ((U.comparison k).hom.app (_, _)) (𝟙 _)) ≫
        (U.U H).map (Prod.mkHom
          ((U.U H).map (Prod.mkHom
            ((S.assoc ((left _ _).trans ((left _ _).trans hS)) k).hom.app X.obj)
            ((S.assoc ((right _ _).trans ((left _ _).trans hS)) k).hom.app Y.obj)))
          ((S.assoc ((right _ _).trans hS) k).hom.app Z.obj)) := by
  dsimp only [leftEndpoint, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
  simp only [Iso.prod_hom, Iso.refl_hom]
  rw [reassoc_of% (endpoint_tower S U join left right (output U join left right (X, Y)) Z hS k),
    Functor.map_comp, Category.assoc]
  have hnat := (U.comparison k).hom.naturality
    (Prod.mkHom (endpoint U join left right (X, Y) ((left _ _).trans hS)).hom
      (𝟙 (Z.toStage ((right _ _).trans hS))))
  dsimp only [Functor.comp_map, Functor.prod_map] at hnat
  rw [reassoc_of% hnat]
  simp only [← Functor.map_comp]
  congr 3
  refine Prod.ext ?_ ?_
  · dsimp
    rw [endpoint_tower S U join left right X Y ((left _ _).trans hS) k]
  · simp

omit [IsDirectedOrder I] in
/-- The endpoint tower law for the right-nested endpoint `X ⊗ (Y ⊗ Z)`. -/
private theorem rightEndpoint_tower (X Y Z : S.PairCategory) {L H : I}
    (hT : join X.stage (join Y.stage Z.stage) ≤ L) (k : L ≤ H) :
    (S.assoc hT k).hom.app
        (output U join left right (X, output U join left right (Y, Z))).obj ≫
        (rightEndpoint S U join left right X Y Z (hT.trans k)).hom =
      (S.T k).map (rightEndpoint S U join left right X Y Z hT).hom ≫
        (U.comparison k).hom.app (_, _) ≫
        (U.U H).map (Prod.mkHom (𝟙 _) ((U.comparison k).hom.app (_, _))) ≫
        (U.U H).map (Prod.mkHom
          ((S.assoc ((left _ _).trans hT) k).hom.app X.obj)
          ((U.U H).map (Prod.mkHom
            ((S.assoc ((left _ _).trans ((right _ _).trans hT)) k).hom.app Y.obj)
            ((S.assoc ((right _ _).trans ((right _ _).trans hT)) k).hom.app Z.obj)))) := by
  dsimp only [rightEndpoint, Iso.trans_hom, Functor.mapIso_hom, Iso.prod_hom, Iso.refl_hom]
  simp only [Iso.prod_hom, Iso.refl_hom]
  rw [reassoc_of% (endpoint_tower S U join left right X (output U join left right (Y, Z)) hT k),
    Functor.map_comp, Category.assoc]
  have hnat := (U.comparison k).hom.naturality
    (Prod.mkHom (𝟙 (X.toStage ((left _ _).trans hT)))
      (endpoint U join left right (Y, Z) ((right _ _).trans hT)).hom)
  dsimp only [Functor.comp_map, Functor.prod_map] at hnat
  rw [reassoc_of% hnat]
  simp only [← Functor.map_comp]
  congr 3
  refine Prod.ext ?_ ?_
  · simp
  · dsimp
    rw [endpoint_tower S U join left right Y Z ((right _ _).trans hT) k]

/-- The conjugated finite associator at a common stage. -/
private def associatorAt (X Y Z : S.PairCategory) (L : I)
    (hS : join (join X.stage Y.stage) Z.stage ≤ L)
    (hT : join X.stage (join Y.stage Z.stage) ≤ L) :
    (output U join left right (output U join left right (X, Y), Z)).toStage hS ≅
      (output U join left right (X, output U join left right (Y, Z))).toStage hT :=
  leftEndpoint S U join left right X Y Z hS ≪≫
    α L (X.toStage ((left _ _).trans ((left _ _).trans hS)))
      (Y.toStage ((right _ _).trans ((left _ _).trans hS)))
      (Z.toStage ((right _ _).trans hS)) ≪≫
    (rightEndpoint S U join left right X Y Z hT).symm

omit [IsDirectedOrder I] in
include hn hc in
private theorem associatorAt_transport (X Y Z : S.PairCategory) {L H : I}
    (hS : join (join X.stage Y.stage) Z.stage ≤ L)
    (hT : join X.stage (join Y.stage Z.stage) ≤ L) (k : L ≤ H) :
    S.tr k (associatorAt S U join left right α X Y Z L hS hT).hom =
      (associatorAt S U join left right α X Y Z H (hS.trans k) (hT.trans k)).hom := by
  apply (cancel_epi ((S.assoc hS k).hom.app
    (output U join left right (output U join left right (X, Y), Z)).obj)).1
  apply (cancel_mono (rightEndpoint S U join left right X Y Z (hT.trans k)).hom).1
  dsimp only [StageSystem.tr, associatorAt, Iso.trans_hom, Iso.symm_hom]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id,
    Category.comp_id]
  rw [rightEndpoint_tower S U join left right X Y Z hT k]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, Iso.map_inv_hom_id_assoc]
  have hck := hc k (X.toStage ((left _ _).trans ((left _ _).trans hS)))
    (Y.toStage ((right _ _).trans ((left _ _).trans hS))) (Z.toStage ((right _ _).trans hS))
  rw [reassoc_of% hck]
  erw [← hn H
    ((S.assoc ((left _ _).trans ((left _ _).trans hS)) k).hom.app X.obj)
    ((S.assoc ((right _ _).trans ((left _ _).trans hS)) k).hom.app Y.obj)
    ((S.assoc ((right _ _).trans hS) k).hom.app Z.obj)]
  erw [reassoc_of% (leftEndpoint_tower S U join left right X Y Z hS k)]

include hn hc in
/-- Scalar-compatible natural associators give isomorphisms of the common-stage tensor objects
with the prescribed representative at all common stages.
Source: the common-stage quotient calculation of the constraints node
(derived-tensor context: Stacks 06YS, 07A4, 0941)
(blueprint: lem-pur-derived-pullback-tensor-constraints).
Proof: conjugate the finite associator by the nested endpoint comparisons. The family tower
law, the scalar square and naturality show that this representative transports to the same
formula at every enlargement, so `StageSystem.PairCategory.exists_iso_of_tr` applies. -/
theorem associator_exists (X Y Z : S.PairCategory) :
    ∃ e : output U join left right (output U join left right (X, Y), Z) ≅
        output U join left right (X, output U join left right (Y, Z)),
      ∀ (L : I) (hS : join (join X.stage Y.stage) Z.stage ≤ L)
        (hT : join X.stage (join Y.stage Z.stage) ≤ L),
        e.hom = StageSystem.PairCategory.mkHom L hS hT
          ((endpoint U join left right (output U join left right (X, Y), Z) hS ≪≫
              (U.U L).mapIso (Iso.prod
                (endpoint U join left right (X, Y) ((left _ _).trans hS)) (Iso.refl _))).hom ≫
            (α L (X.toStage ((left _ _).trans ((left _ _).trans hS)))
              (Y.toStage ((right _ _).trans ((left _ _).trans hS)))
              (Z.toStage ((right _ _).trans hS))).hom ≫
            (endpoint U join left right (X, output U join left right (Y, Z)) hT ≪≫
              (U.U L).mapIso (Iso.prod (Iso.refl _)
                (endpoint U join left right (Y, Z) ((right _ _).trans hT)))).inv) := by
  obtain ⟨e, he⟩ := StageSystem.PairCategory.exists_iso_of_tr
    (fun L hS hT ↦ associatorAt S U join left right α X Y Z L hS hT)
    (fun L H hS hT k ↦ associatorAt_transport S U join left right α hn hc X Y Z hS hT k)
  exact ⟨e, he⟩

end CategoryTheory.BilinearCoefficientDescent
