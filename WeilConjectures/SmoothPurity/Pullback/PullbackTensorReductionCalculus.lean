/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Products.Basic
public import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Adjunction.Basic

/-! # Reduction calculations for pullback tensor comparisons -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

open CategoryTheory CategoryTheory.Functor
namespace WeilConjectures

section ReductionCalculus
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

end ReductionCalculus

end WeilConjectures
