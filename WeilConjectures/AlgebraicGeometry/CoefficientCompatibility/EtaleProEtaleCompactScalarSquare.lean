/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonNormalization
import all WeilConjectures.AlgebraicGeometry.Sp.SpDirectImageEtaleMate
import all WeilConjectures.AlgebraicGeometry.OpenScalarSite.OpenScalarSiteCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactScalarCoherence
import WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.RecordedCompactScalarNormalization

/-! # The normalized compact-support scalar/site equation

Source: Stacks Project, Tag 0GL6, and the proper/open mate pasting of the
Charts paragraph of the blueprint's reduction-exceptional proof.
(blueprint: lem-sp-transported-compact-scalar-site-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.CoefficientCompatibility

attribute [local irreducible] compactSupportSiteComparison comparisonUpperStar
  pbcComparisonReduction Etale.compactScalarMap Functor.mapDerivedCategory
  Functor.rightDerivedFunctor Functor.leftDerivedFunctor pbcFixedScalarExtension DerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.TStructure.t

-- The bounded-below compact comparison uses the same ambient proper counit mate.
end AlgebraicGeometry.ProEtale.CoefficientCompatibility
