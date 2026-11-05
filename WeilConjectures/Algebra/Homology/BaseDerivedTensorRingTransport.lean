/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.BaseDerivedTensorOrdinaryRingComparison
import WeilConjectures.Algebra.Homology.SemilinearScalarExtensionHomologySquare

/-! # Change of all coefficient rings in the localized tensor comparison

Source: Stacks Project, Tags 06Y6 and 08IB, derived tensor functoriality.
(blueprint: lem-pc-base-derived-tensor-ring-transport).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

-- Lift the given additive isomorphism; its inverse comes from the component isomorphisms.

-- Canonical homology factors compose, independently of the chosen homology data.

end ModuleCat
