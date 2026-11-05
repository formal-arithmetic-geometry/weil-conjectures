/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueStratumInput
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueStratumScalar
import all WeilConjectures.AlgebraicGeometry.Completed.Adic.CompletedAdicCoefficientDatumSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement

/-! # Ordinary constant modules under normalized stratum coefficient transport

Source: Bhatt--Scholze, Lemma 6.5.8(1) and Proposition 6.6.11.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

namespace IntegralResidueOrdinaryProof

end IntegralResidueOrdinaryProof

attribute [local irreducible] integralConstantModule completedAdicChange

end AlgebraicGeometry.Scheme
