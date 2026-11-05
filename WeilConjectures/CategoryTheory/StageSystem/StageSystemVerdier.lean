/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.StageSystemCommonStageCones
public import Mathlib.CategoryTheory.Triangulated.Triangulated
import WeilConjectures.CategoryTheory.Idempotents.Pretriangulated

/-! # The Verdier axioms for common-stage triangles

Source: blueprint `sec-proper-base-change/sk-thm-properbasechange`, Verdier axioms
(blueprint: thm-weil-pbc-verdier-axioms).
-/

@[expose] public section
set_option autoImplicit false

universe w v u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
  {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
  [∀ i, Preadditive (C i)] [∀ i, HasZeroObject (C i)]
  [∀ i, HasShift (C i) ℤ] [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive]
  [∀ i, Pretriangulated (C i)] [∀ i, IsTriangulated (C i)]
  [Preadditive S.PairCategory] [HasZeroObject S.PairCategory]
  [HasShift S.PairCategory ℤ] [∀ n : ℤ, (shiftFunctor S.PairCategory n).Additive]
  [∀ i, (S.ι i).Additive] [∀ i, (S.ι i).CommShift ℤ]
  [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift ℤ]
  [∀ (i j : I) (h : i ≤ j), (S.T h).IsTriangulated]
  [∀ (i j : I) (h : i ≤ j), NatTrans.CommShift (S.transIso h).hom ℤ]

set_option linter.unusedSectionVars false in
section

open CategoryTheory.Category

end

end CategoryTheory.StageSystem
