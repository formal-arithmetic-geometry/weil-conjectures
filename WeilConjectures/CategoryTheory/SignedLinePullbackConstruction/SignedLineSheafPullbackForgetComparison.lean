/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.Pullback
/-! # Forgetting algebraic structure in the constructed inverse image
Source: Stacks Project, Tags 00YV and 03D2.
(blueprint: lem-pur-signed-line-sheaf-pullback-forget).
-/
@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
universe u v w e
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory.SignedLinePullbackConstruction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (F : C ⥤ D) [F.IsContinuous J K]
  {E : Type e} [Category.{max u v w} E] (U : E ⥤ Type (max u v w))
  [∀ P : Cᵒᵖ ⥤ E, F.op.HasLeftKanExtension P]
  [HasWeakSheafify K E] [J.HasSheafCompose U] [K.HasSheafCompose U]
  [K.PreservesSheafification U] [U.PreservesLeftKanExtensions F.op]
end CategoryTheory.SignedLinePullbackConstruction
