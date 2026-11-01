/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalCounitDescent
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalOrdinaryChart
import all WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
import all WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer

/-! # Canonical chart equation for the exceptional coefficient transpose -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  Functor.mapDerivedCategory
  AlgebraicGeometry.ProEtale.pbcFixedScalarExtension
  AlgebraicGeometry.Etale.upperStar AlgebraicGeometry.Etale.lowerStar
  AlgebraicGeometry.ProEtale.reductionSiteScalarIso
  AlgebraicGeometry.ProEtale.reductionSitePullbackIso
  AlgebraicGeometry.ProEtale.reductionSiteCompactSupportIso
  AlgebraicGeometry.ProEtale.reductionDirectImageComparison
  AlgebraicGeometry.ProEtale.reductionSite
  AlgebraicGeometry.Scheme.reductionDerivedChange
  AlgebraicGeometry.ProEtale.reductionEtaleChartRightIso
  AlgebraicGeometry.ProEtale.reductionEtaleChartScalarIso

end AlgebraicGeometry.ProEtale
