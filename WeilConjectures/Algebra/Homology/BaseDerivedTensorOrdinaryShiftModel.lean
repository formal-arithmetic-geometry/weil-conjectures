/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
import WeilConjectures.Algebra.Homology.BaseTensorOrdinaryIso
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCounitShiftSquare

/-! # Transport of the ordinary derived tensor comparison

Source: Stacks Project, Tags 06Y6 and 08IB; an explicit shift reduction
for the tensor inheritance in Tag 0DJA(1).
(blueprint: lem-pc-base-derived-tensor-ordinary-shift-model).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings
namespace ModuleCat

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} B)]

end ModuleCat
