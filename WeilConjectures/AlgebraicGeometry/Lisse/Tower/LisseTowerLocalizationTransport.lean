/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerPulledScalar

/-! # Transport of localization through the finite-coefficient realization equivalence

Source: Stacks Project, Tags 03CY, 03D2, 03D3 and 0D6D.
The functors and scalar comparison are explicit transports across an equivalence.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace LisseTowerLocalizationTransport

end LisseTowerLocalizationTransport

open LisseTowerLocalizationTransport

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] HasDerivedCategory.standard pbcDerivedRestrict
  lisseTowerFixedRealization constantAdicFiniteProjection lisseTowerPulledScalarIso
  lisseTowerFixedScalarIso lisseTowerEtaleScalarIso localProEtaleNormalization

end AlgebraicGeometry.Scheme
