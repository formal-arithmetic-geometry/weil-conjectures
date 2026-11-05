/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # Transport of a module pullback comparison across a scheme isomorphism

Source: Stacks Project, Tags 06YJ, 08HY and 0D5S.
(blueprint: lem-pc-module-pullback-comparison-iso-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

private theorem postcompose_rightKanExtension
    {C D H H' : Type*} [Category C] [Category D] [Category H] [Category H']
    {L : C ⥤ D} {F : C ⥤ H} {LF : D ⥤ H} (ε : L ⋙ LF ⟶ F)
    [LF.IsRightKanExtension ε] (U : H ⥤ H') [U.IsEquivalence] :
    (LF ⋙ U).IsRightKanExtension
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight ε U) := by
  let γ : (Functor.whiskeringRight D H H').obj U ⋙
        (Functor.whiskeringLeft C D H').obj L ⟶
      (Functor.whiskeringLeft C D H).obj L ⋙
        (Functor.whiskeringRight C H H').obj U :=
    { app K := (Functor.associator L K U).inv }
  have (K : D ⥤ H) : IsIso (γ.app K) := by
    dsimp [γ]
    infer_instance
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  have : (Functor.RightExtension.postcompose₂ L F U).IsEquivalence := by
    change (CostructuredArrow.map₂ γ (𝟙 _)).IsEquivalence
    infer_instance
  exact ⟨⟨(IsTerminal.equivOfIso (Functor.RightExtension.postcompose₂ObjMkIso U ε))
    (IsTerminal.isTerminalObj _ _ (LF.isUniversalOfIsRightKanExtension ε))⟩⟩

end AlgebraicGeometry
