/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueCoefficientModel
public import WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
public import WeilConjectures.AlgebraicGeometry.Residue.ResidueLissePerfectLift
import all WeilConjectures.ProperBaseChange.IntegralCoefficientCompletenessTransportSupplement
import WeilConjectures.SixFunctors.Open.OpenDvrIntrinsicCriterion
import WeilConjectures.AlgebraicGeometry.Koszul.KoszulReconstructionModels

/-! # Completeness under normalized integral coefficient restriction

Source: Bhatt--Scholze, Lemma 6.5.8(1), Definition 6.5.1.
(blueprint: lem-weil-pbc-integral-residue-coefficient-completeness).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProEtale WeilConjectures
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
