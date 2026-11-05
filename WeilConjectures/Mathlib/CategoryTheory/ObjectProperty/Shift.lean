/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.Mathlib.CategoryTheory.EqToHom

/-! # Shift comparisons of inclusions and lifts of full subcategories -/

@[expose] public section

namespace CategoryTheory

namespace ObjectProperty

variable {C : Type*} [Category* C] {A : Type*} [AddMonoid A] [HasShift C A]
  (P : ObjectProperty C) [P.IsStableUnderShift A]

end ObjectProperty

end CategoryTheory
