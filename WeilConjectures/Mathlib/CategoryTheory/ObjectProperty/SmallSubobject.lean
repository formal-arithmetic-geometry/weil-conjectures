/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Subobject.WellPowered

/-!
# Essential smallness from monomorphisms into a small family

In a well-powered category, a property of objects is essentially small as soon as every object
satisfying it is a subobject of a member of a small family of objects: the subobjects of the
members of the family form a small set.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] [WellPowered.{w} C]

end CategoryTheory.ObjectProperty
