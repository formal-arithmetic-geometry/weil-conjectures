/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
public import Mathlib.CategoryTheory.Sites.CoverPreserving
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic

/-!
# Localization of module pullback

Source: Stacks Project, Modules on Sites, Tag 04J0.
(blueprint: lem-pur-ringed-site-pullback-localization-universes)
-/

@[expose] public section
open CategoryTheory CategoryTheory.Limits Opposite
universe u v w
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SheafOfModules.RingedSitePullback
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {U : C ⥤ D} [U.IsContinuous J K]
  {R : Sheaf J RingCat.{max u v w}} {S : Sheaf K RingCat.{max u v w}}
  (a : R ⟶ (U.sheafPushforwardContinuous RingCat J K).obj S)
  [HasFiniteLimits C] [HasFiniteLimits D] [PreservesFiniteLimits U]

end SheafOfModules.RingedSitePullback
