/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ConstructibleExceptionalInverseImage
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekIso
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.AlgebraicGeometry.VectorIntegrationChart.VectorIntegrationChartCoordinates
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedIntegrationTransposes
import WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationIdentityUnit
import all WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationRankZeroLocal

/-! # Exceptional identity adjunction in ordered integration coordinates

Source: the rank-zero normalization in the diagonal chart proof.
(blueprint: lem-pur-vector-integration-identity-adjunct).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 128
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.VectorIntegrationChart

attribute [local irreducible] Etale.rightDerivedLowerShriek
  Etale.rightDerivedUpperShriek Etale.rightDerivedUpperShriekAdjunction
  Etale.affineLinearCompactComparison Functor.mapDerivedCategory
attribute [local semireducible] ProEtale.AffineSpacePurity.orderedSource
  ProEtale.AffineSpacePurity.exceptional
attribute [local implicit_reducible] affineTraceTower affineTraceProjection
  Etale.affineLinearBaseCoefficient

end AlgebraicGeometry.ProEtale.VectorIntegrationChart
