/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientScalarComparison
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientModelRealizationExtensionIso
import WeilConjectures.AlgebraicGeometry.Constant.ConstantAdicQuotientRealizationReflectsIso

/-! # Algebraic extension isomorphism for consecutive constant quotient models

This is the algebraic derived reduction extracted from the universal-reduction
statement.  The geometric comparison hypotheses remain explicit so that the
statement is strictly smaller than the Hom-bijection conclusion.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] HasDerivedCategory.ofIsGrothendieckAbelian

end AlgebraicGeometry.Scheme
