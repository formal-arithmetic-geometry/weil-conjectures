/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.SignedLinePullbackConstruction.InverseImageAction.SignedLineModuleInverseImageAction
public import WeilConjectures.CategoryTheory.SignedLinePullbackConstruction.SheafPullbackUnitPresentation.SignedLineSheafPullbackUnitPresentation
public import Mathlib.Algebra.Category.Ring.Limits
/-! # Constructing scalar actions from set inverse-image presentations
Source: Stacks Project, Modules on Sites, Tag 03D2.
(blueprint: lem-pur-signed-line-module-action-presentations).
-/
@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.sheafPullbackConstruction
namespace SheafOfModules.SignedLinePullbackConstruction
open CategoryTheory.SignedLinePullbackConstruction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
  [PreservesFiniteLimits (sheafPullback F (Type (max u v w)) J K)]
  [HasWeakSheafify K AddCommGrpCat.{max u v w}]
  {A : Sheaf J RingCat.{max u v w}} {B : Sheaf K RingCat.{max u v w}}
  (φ : A ⟶ (F.sheafPushforwardContinuous RingCat.{max u v w} J K).obj B)
  (M : SheafOfModules.{max u v w} A)
end SheafOfModules.SignedLinePullbackConstruction
