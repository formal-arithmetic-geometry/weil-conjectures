/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall

/-!
# Existence of module pullback in a universe containing the sites

Source: Stacks Project, Modules on Sites, Tag 03D7, and Mathlib's free-representable
presentation construction in `ModuleCat.Presheaf.Pullback`.
(blueprint: lem-pur-ringed-site-module-pullback-exists-universes)
-/

@[expose] public section
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

end SheafOfModules
