/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap

/-! # Scalar extension of an explicit mixed total tensor

The comparison is at the level of complexes, without derived-category or flatness assumptions.
Source: Stacks Project, Tag 06Y6, tensor associativity in the proof of derived change of rings.
(blueprint: new-lem-pc-mixed-total-tensor-scalar-extension).
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct ChangeOfRings

namespace RingTensorCohomology
variable (R A Aq : Type u) [CommRing R] [CommRing A] [CommRing Aq]
  [Algebra R A] [Algebra A Aq] [Algebra R Aq] [IsScalarTower R A Aq]

end RingTensorCohomology
