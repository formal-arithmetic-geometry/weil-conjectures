/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseLocalizationMap

/-! # The A-action on the canonical base-localization cohomology map

Source: Stacks Project, Tags 06Y6 and 0DJ8.
(blueprint: lem-pc-base-localization-cohomology-action).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Functor
open scoped TensorProduct ChangeOfRings
attribute [local instance] Algebra.TensorProduct.rightAlgebra
namespace RingTensorCohomology

variable (R Rp B A D : Type u)
  [CommRing R] [CommRing Rp] [CommRing B] [CommRing A] [CommRing D]
  [Algebra R Rp] [Algebra R B] [Algebra Rp B] [IsScalarTower R Rp B]
  [Algebra R A] [Algebra Rp A] [IsScalarTower R Rp A]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[Rp] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

end RingTensorCohomology
