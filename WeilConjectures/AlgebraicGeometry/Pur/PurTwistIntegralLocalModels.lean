/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheavesSupplement
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionDualLocalIso
import all WeilConjectures.AlgebraicGeometry.Pur.PurTwistCoefficientTensor
import all WeilConjectures.AlgebraicGeometry.Pur.PurInverseImageScalarComparison
import all Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # Integral and finite local models of the scalar-extended root line

Source: coefficient-twist blueprint, proof steps 6--8 and 10.
(blueprint: lem-pur-twist-integral-local-models)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u d
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped ChangeOfRings TensorProduct
namespace AlgebraicGeometry.Scheme

-- Sectionwise tensor cancellation for the coefficient pushout.

-- The prescribed completed action restricts to the original discrete action.

attribute [local irreducible] integralForgetIso

attribute [local irreducible] integralExtensionReverse

attribute [local irreducible] restrictionSheafificationComparison

attribute [local irreducible] integralRawForwardApp

attribute [local irreducible] integralRawForward

attribute [local irreducible] integralDiscreteIso

-- Identify the positive quotient tower, including its distinguished maps, with completion.

-- Finite targets see the same linear maps before and after completion.
section QuotientTransport
variable {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}]
  [HasWeakSheafify J AddCommGrpCat.{u + 1}]
variable {R B T Q : Sheaf J CommRingCat.{u + 1}}

end QuotientTransport

-- A point on a covering member detects the unit section.

end AlgebraicGeometry.Scheme
