/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
import WeilConjectures.Algebra.Homology.BaseDerivedTensorModelQuasiIsoOrdinaryComparison

/-! # Transport of base-derived tensor models along quasi-isomorphisms

Source: Stacks Project, More on Algebra, Tags 06Y6 and 08IB.
(blueprint: lem-pc-base-derived-tensor-model-quasiiso-comparison).
-/

@[expose] public section

universe u w
open CategoryTheory
open scoped ChangeOfRings
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace ModuleCat

variable (R A B D : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

end ModuleCat
