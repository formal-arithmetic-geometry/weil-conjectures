/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizedConstantsNormalization
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerConstantCoherence

/-! # Constant model comparisons and the coefficient identity on complexes

Source: Stacks Project, Modules on Sites, Tags 03CY and 03DA; Sites, Tag 0H7J;
Cohomology on Sites, Tag 06YY.

Only the identity semilinear arrow on a represented complex is checked here.
Localization and naturality extend this to arbitrary derived arrows in
`lisseTower_localized_constants_normalization`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicQuotientRealization constantAdicFiniteRealization
  constantAdicQuotientRightIso constantAdicFiniteProjection
  lisseTowerConstantInput lisseTowerConstantScalarIso lisseTowerConstantModelIso
  lisseTowerAlgebraRestrictIso

end AlgebraicGeometry.Scheme
