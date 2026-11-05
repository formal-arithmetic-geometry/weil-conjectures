/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
/-! # Testing maps on inverse-image units
Source: Stacks Project, Tags 00YV, 03D2 and 03D3.
(blueprint: lem-pur-signed-line-pullback-unit-presentation).
-/
@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSectionVars false
universe u v w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Functor.sheafPullbackConstruction
namespace CategoryTheory.SignedLinePullbackConstruction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]
namespace SheafPullbackUnitPresentation
variable {S S' S'' : Sheaf J (Type (max u v w))} {T T' T'' : Sheaf K (Type (max u v w))}

end SheafPullbackUnitPresentation
end CategoryTheory.SignedLinePullbackConstruction
