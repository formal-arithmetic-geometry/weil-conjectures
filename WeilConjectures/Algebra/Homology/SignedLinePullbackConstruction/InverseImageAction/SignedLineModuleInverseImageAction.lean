/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Category.Grp.FilteredColimits
/-! # Scalar actions on the constructed abelian inverse image
Source: Stacks Project, Modules on Sites, Tags 03D2 and 03D3.
(blueprint: def-pur-signed-line-module-inverse-image-action).
-/
@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
universe u v w
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
namespace SheafOfModules.SignedLinePullbackConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {A : Sheaf J RingCat.{max u v w}} {B : Sheaf K RingCat.{max u v w}}
  (φ : A ⟶ (F.sheafPushforwardContinuous RingCat.{max u v w} J K).obj B)
  (M : SheafOfModules.{max u v w} A)
end SheafOfModules.SignedLinePullbackConstruction
