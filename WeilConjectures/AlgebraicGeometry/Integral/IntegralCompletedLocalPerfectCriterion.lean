/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionCriterion
import WeilConjectures.AlgebraicGeometry.Perfect.PerfectStrataUniformReductions
import WeilConjectures.AlgebraicGeometry.Completed.CompletedRealizationDerivedCohomology
import WeilConjectures.AlgebraicGeometry.Constant.ConstantModelStratificationTransportSupplement
import all WeilConjectures.AlgebraicGeometry.Perfect.PerfectLocalReductionModels
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.Integral.Perfect.IntegralPerfectChartComplete
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueStratumLift
import WeilConjectures.AlgebraicGeometry.Finite.Field.FiniteFieldStratifiedPerfectModels
import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement

/-! # The completed local perfect criterion
Source: Bhatt--Scholze, Proposition 6.6.11.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective
open ProEtale

end AlgebraicGeometry.Scheme
