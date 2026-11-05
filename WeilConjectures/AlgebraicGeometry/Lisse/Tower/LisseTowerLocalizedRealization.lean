/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerScalarRestriction
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizedConstants
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizedActual

/-! # Localizing a descended semilinear tower

Source: Stacks Project, Tags 03CY, 03DA, 06YY and 0H7J.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  pbcDerivedRestrict constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  localProEtaleNormalization normalizationConstantArrow lisseTowerAlgebraArrow
  lisseTowerFixedRealization

end AlgebraicGeometry.Scheme
