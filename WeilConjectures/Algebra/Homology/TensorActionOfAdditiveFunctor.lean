/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Tensor coefficient actions from an additive functor

Source: Stacks Project, Tag 06Y6, functorial coefficient actions
(blueprint: lem-pc-tensor-action-additive-functor).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe uR uA uB v

open CategoryTheory
open scoped TensorProduct

namespace ModuleCat

end ModuleCat
