/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientRealizationScalarReduction
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientRealizationTowerTransition

/-! # Reduction of the consecutive realization comparison to the lower tower level

This is the geometric transport part of the consecutive quotient argument.  It
records the comparison before the supplied lower model is used; the latter is
then only a categorical cancellation in the parent theorem.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

end AlgebraicGeometry.Scheme
