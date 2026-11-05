/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelMap
import WeilConjectures.Algebra.Homology.DerivedTensorSecondLocalizationModels
import WeilConjectures.Algebra.Homology.DerivedTensorBaseLocalizationModels
/-! # Localizing the base and second factor of a derived tensor

Source: Stacks Project, perfect.tex, Tag 0DJ8, localization of the base and
second coefficient ring; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-derived-tensor-base-second-localization-models).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A B Rp Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Rp] [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R Rp] [Algebra B Bp]
  [Algebra R Bp] [Algebra Rp A] [Algebra Rp Bp]
  [tRpA : IsScalarTower R Rp A]
  [tRB : IsScalarTower R B Bp] [tRpB : IsScalarTower R Rp Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[Rp] Bp) D]
  [Algebra A D] [Algebra B D] [Algebra Bp D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tApD : IsScalarTower A (A ⊗[Rp] Bp) D]
  [tBpD : IsScalarTower Bp (A ⊗[Rp] Bp) D]
  [tBBpD : IsScalarTower B Bp D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

end RingTensorCohomology
