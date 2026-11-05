/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # Shift compatibility of the ordinary coefficient map

Source: Stacks Project, Tags 06Y6 and 08IB; an explicit shift reduction
for the tensor inheritance in Tag 0DJA(1).
(blueprint: lem-pc-tensor-coefficient-shift-homology).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

variable {A E C : Type u} [CommRing A] [CommRing E] [CommRing C]

end ModuleCat
