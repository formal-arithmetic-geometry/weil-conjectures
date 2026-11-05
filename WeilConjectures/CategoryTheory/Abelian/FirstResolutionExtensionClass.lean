/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# The first extension class of an injective resolution

Source: Stacks Project, Tags 06XR and 06XV, resolution computation and extension classes.
(blueprint: lem-amb-first-resolution-extension-class).
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
namespace CategoryTheory.InjectiveResolution

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {G : C} (R : InjectiveResolution G)
  (w₀ : R.ι.f 0 ≫ R.cocomplex.toCycles 0 1 = 0)
  (hS : (ShortComplex.mk (R.ι.f 0) (R.cocomplex.toCycles 0 1) w₀).ShortExact)

end CategoryTheory.InjectiveResolution

-- Check the axioms of the completed construction.
