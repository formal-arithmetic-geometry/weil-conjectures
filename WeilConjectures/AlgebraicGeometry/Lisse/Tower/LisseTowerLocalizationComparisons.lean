/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerPulledScalar
import WeilConjectures.AlgebraicGeometry.Lisse.Tower.LisseTowerLocalizationBase

/-! # Functor comparisons for localization of finite coefficient modules

Source: Stacks Project, Modules on Sites, Tags 03CY, 03D2 and 03D3, and
Cohomology on Sites, Tag 0D6D. These comparisons concern inverse image and scalar restriction;
they do not involve a descended tower or choices of its level markings.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] HasDerivedCategory.standard
  lisseTowerFixedRealization constantAdicFiniteProjection localProEtaleNormalization
  adicTowerRestrictedTransition lisseTowerPulledScalarIso lisseTowerEtaleScalarIso
  constantAdicRestrictedStep

attribute [local irreducible] pbcDerivedRestrict
  lisseTowerInverseImageArrow lisseTowerProjectedArrow

end AlgebraicGeometry.Scheme
