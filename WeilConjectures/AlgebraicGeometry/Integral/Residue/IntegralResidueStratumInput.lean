/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueCoefficientModel
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import all WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueCoefficientCompleteness
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueFiniteChart
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcCompletedPullbackActualSupplement
import WeilConjectures.AlgebraicGeometry.Stratum.StratumCompletionUnitRestriction
import WeilConjectures.AlgebraicGeometry.Integral.IntegralPullbackScalarComparison
import all WeilConjectures.AlgebraicGeometry.Finite.Perfect.FinitePerfectQuotientModels
import WeilConjectures.CategoryTheory.Ringed.RingedDerivedRestrictionGeneralSupplement

/-! # Input comparison for residue lifting on one stratum

Source: Bhatt--Scholze, Lemma 6.5.8 and Proposition 6.6.11.
(blueprint: lem-weil-pbc-integral-residue-stratum-input).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

attribute [local instance 100000] inputBaseAbLocallyBijective inputOverAbLocallyBijective

end AlgebraicGeometry.Scheme
