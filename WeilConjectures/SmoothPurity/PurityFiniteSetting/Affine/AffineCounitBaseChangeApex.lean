/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumRightAdjointCoherenceSupplement
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
import WeilConjectures.SmoothPurity.PurityFiniteSetting.OrientationCounit.DiagonalCounitComparisonData
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumRightAdjointCoherenceSupplement
import WeilConjectures.Compactification.BaseChange
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationRestrictedChartCoefficientCore
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.AffineCounitMateUnitChange
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationBaseCoefficientComposition
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTatePullbackSquare
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit

/-! # Affine counit base change with an isomorphic Cartesian apex

Source: orientation-charts proof Step 4, equation (A).
Normalize the tower-counit base-change equation with its coefficient formula,
the ordered Tate square and unit conversion. The coordinate square identifies the
specified map; Cartesian-apex pasting and coefficient composition give the result.
(blueprint: new-lem-pur-affine-counit-base-change-apex).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] Scheme.Modules

set_option maxHeartbeats 800000 in
-- Kernel checking the fixed derived-category unit identifications needs this budget.
end WeilConjectures.PurityFiniteSetting
