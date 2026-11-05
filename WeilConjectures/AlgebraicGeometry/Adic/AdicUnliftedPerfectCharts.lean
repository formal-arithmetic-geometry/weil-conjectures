/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralUniformCoefficient
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharacterization
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectCharts
import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectTransportComplete
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionAlgEquiv
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformLocalModelCohomology
import WeilConjectures.AlgebraicGeometry.Pbc.PbcUniformReductionCriterion

/-! # Perfect charts for the actual unlifted Padic datum

Source: Bhatt--Scholze, Proposition 6.6.11 and Lemma 6.5.8.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
