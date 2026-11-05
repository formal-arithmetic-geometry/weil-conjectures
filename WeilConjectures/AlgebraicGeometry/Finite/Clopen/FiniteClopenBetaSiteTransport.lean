/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenMateData
public import WeilConjectures.AlgebraicGeometry.ClopenMateNormalization.EtaleClopenMateNormalization
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.FixSiteOpenExchangeSheaf
import WeilConjectures.SixFunctors.ProEtale.BaseChange.ComparisonSquareComponent
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates

/-! # Site comparison for cartesian open base change

Source: Stacks Project, Tags 09AF and 0F7B.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

namespace BetaSiteTransportProof

set_option backward.defeqAttrib.useBackward true

-- The Tag 09AF comparison preserves the open adjunction units for every ring.

-- Keep the Kan-extension constructions closed while checking the mate calculation.
attribute [local irreducible] upperStar Etale.upperStar openImmersionLowerShriek
  Etale.openImmersionLowerShriek comparisonUpperStar

attribute [local irreducible] openImmersionLowerShriekBaseChangeMap

end BetaSiteTransportProof

end AlgebraicGeometry.ProEtale
