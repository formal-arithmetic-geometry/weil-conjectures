/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Limits.FullSubcategory

/-! # Created limits and colimits of fixed pairs

Source: the universal-property argument in step 5 of the twisted action-site proof,
with the existing algebra-limit construction.
(blueprint: lem-sf-twisted-fixed-pair-created-limits)
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {A : Type u} [Category.{v} A] (T : A ⥤ A)

end CategoryTheory.Endofunctor.IsoAlgebra
