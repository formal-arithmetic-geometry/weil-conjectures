/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.DerivedExtensionRingEquivCohomology
import WeilConjectures.Algebra.Homology.BaseDerivedTensorRingCounitSquare

/-! # Derived tensor comparison after restriction to the second coefficient ring

Source: Stacks Project, Tag 06Y6, Lemma 15.61.1, independence of choices.
(blueprint: lem-pc-base-derived-tensor-restricted-ring-comparison).
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
