/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Composition law of descended tensor comparisons

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 0D6D
(auxiliary; not a blueprint node).

Derived tensor comparisons descended from representatives, as in
`tensorComparisonDescent`, inherit the composition law of their representative
comparisons, provided the derived compositor is the descent of the representative
compositor.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {KY : Type u₁} {KX : Type u₂} {KZ : Type u₃} {DY : Type u₄} {DX : Type u₅}
  {DZ : Type u₆} [Category.{v₁} KY] [Category.{v₂} KX] [Category.{v₃} KZ]
  [Category.{v₄} DY] [Category.{v₅} DX] [Category.{v₆} DZ]

end CategoryTheory
