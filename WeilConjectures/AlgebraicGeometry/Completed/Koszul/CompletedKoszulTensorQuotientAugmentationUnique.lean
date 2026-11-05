/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Completed.Koszul.CompletedKoszulTensorQuotientAugmentationData
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientsSupplement

/-! # Uniqueness of the finite strict completed Koszul tensor augmentation

Source: Stacks Project, Tags 091N and 099M.
(blueprint: new-y2-completed-koszul-tensor-quotient-augmentation-unique).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme

-- Fix the coefficient universe for the polymorphic sheafification instances.

variable (T : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)

-- Express the unit-constraint formula through the sheafification unit before
-- specializing it to the completed coefficients.

-- Carry out the scalar-extension calculation with symbolic coefficient rings.
-- This keeps elaboration from unfolding the concrete inverse-limit coefficient ring.

end AlgebraicGeometry.Scheme
