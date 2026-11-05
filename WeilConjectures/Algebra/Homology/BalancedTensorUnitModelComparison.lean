/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizationModelSemilinear
public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.Algebra.Homology.UniversalBalancedTensorComparison
import WeilConjectures.Algebra.Homology.MixedTensorUnderlyingHomology

/-! # Universal derived cohomology comparisons for a fixed balanced tensor complex

Source: Stacks Project, Tags 064L and 06Y6. The K-flat resolution is supplied explicitly.
(blueprint: new-lem-pc-balanced-tensor-unit-model-comparison).
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace RingTensorCohomology
variable (R A Aq : Type u) [CommRing R] [CommRing A] [CommRing Aq]
  [Algebra R A] [Algebra A Aq] [Algebra R Aq] [IsScalarTower R A Aq]

variable (B D : Type u) [CommRing B] [CommRing D] [Algebra R B]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

end RingTensorCohomology
