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
  sorry

end CategoryTheory.BilinearCoefficientDescent
