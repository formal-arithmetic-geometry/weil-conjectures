/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
/-! # Scalar extension along equal coefficient maps
Source: Stacks Project, Tag 05G3, tensor associativity and scalar extension.
(blueprint: lem-pc-base-localization-dlinear-glue). -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat
end ModuleCat
