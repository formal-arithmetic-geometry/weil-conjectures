/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelMap
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyCofan
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyMapNaturality
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # The source coproduct for localized derived tensor comparison

Source: Stacks Project, Tags 06Y6 and 0DJA(1).
(blueprint: lem-pc-localized-comparison-coproduct-source). -/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

end ModuleCat
