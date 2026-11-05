/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # The B-linear cohomological counit square under integer shift

Source: Stacks Project, Tags 05SU, 06Y6 and 08IB; the explicit square is an
explicit compatibility calculation for the ordinary shift model.
(blueprint: lem-pc-base-derived-tensor-counit-shift-square).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]

end ModuleCat
