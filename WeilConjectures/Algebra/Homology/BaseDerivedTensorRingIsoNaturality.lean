/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.BaseDerivedTensorRingTransport

/-! # Naturality of the localized tensor counit under ring isomorphisms

Source: Stacks Project, Tag 06Y6, derived change of rings; Tag 0DJ7, equation-bc.
(blueprint: lem-pc-base-derived-tensor-ring-iso-naturality).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
noncomputable section
namespace ModuleCat

end ModuleCat
