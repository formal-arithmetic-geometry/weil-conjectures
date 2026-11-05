/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueCoefficientModel
public import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteCoefficientDirectImage
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
import all WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarCoefficientEquivalence
import all WeilConjectures.AlgebraicGeometry.Integral.IntegralPullbackScalarComparison
import all WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleCoefficientSerre

/-! # Finite reduction under normalized residue coefficients

Source: Bhatt--Scholze, Definition 6.5.1 and Lemma 6.5.8(1).
(blueprint: lem-weil-pbc-integral-residue-finite-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
