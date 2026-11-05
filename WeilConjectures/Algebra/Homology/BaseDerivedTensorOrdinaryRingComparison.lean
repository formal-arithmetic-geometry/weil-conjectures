/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.Algebra.Homology.BaseDerivedTensorRestrictedRingComparison

/-! # Coefficient transport for the ordinary derived tensor comparison

Source: Stacks Project, Tag 06Y6, lemma-derived-base-change.
(blueprint: lem-pc-base-derived-tensor-ordinary-ring-comparison).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w w'
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

end ModuleCat
