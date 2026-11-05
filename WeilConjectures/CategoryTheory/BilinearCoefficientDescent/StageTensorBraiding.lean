/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent

/-! # Braiding representatives in a directed tensor family

Source: the agent-written common-stage representative construction.
The derived-tensor application follows Stacks 06YS, 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u v
open CategoryTheory

set_option allowUnsafeReducibility true in
attribute [local reducible] CategoryTheory.BilinearCoefficientDescent.output
namespace CategoryTheory.BilinearCoefficientDescent

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  (S : StageSystem C) (U : Family S S S)
  (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)

end CategoryTheory.BilinearCoefficientDescent

namespace CategoryTheory.BilinearCoefficientDescent
variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)]
  (S : StageSystem C) (U : Family S S S)
  (join : I → I → I) (left : ∀ i j, i ≤ join i j) (right : ∀ i j, j ≤ join i j)
  (β : ∀ i (X Y : C i), (U.U i).obj (X, Y) ≅ (U.U i).obj (Y, X))
  (hn : ∀ i {X X' Y Y' : C i} (f : X ⟶ X') (g : Y ⟶ Y'),
    (U.U i).map (Prod.mkHom f g) ≫ (β i X' Y').hom =
      (β i X Y).hom ≫ (U.U i).map (Prod.mkHom g f))
  (hc : ∀ {i j : I} (h : i ≤ j) (X Y : C i),
    (S.T h).map (β i X Y).hom ≫ (U.comparison h).hom.app (Y, X) =
      (U.comparison h).hom.app (X, Y) ≫
        (β j ((S.T h).obj X) ((S.T h).obj Y)).hom)

end CategoryTheory.BilinearCoefficientDescent
