/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels

/-! # Ambient scalar comparison on the good localization

Source: Stacks 06YY and 0941; the scalar quotient construction in the final
common-stage transport paragraph of the trace-transport blueprint.
(blueprint: new-trf-ambient-quotient-scalar-good-comparison)

The lower construction step is isolated here: balanced finite quotient tensor
association identifies the scalar change of a whole-system reduction with the
strict completed scalar tower on the flat-term K-flat localization.
-/

@[expose] public section
set_option autoImplicit false
universe t u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The balanced scalar comparison exists on the flat-term K-flat localization.
Source: Stacks 06YY and 0941; strict quotient scalar construction in the common-stage
transport argument.
(blueprint: new-trf-ambient-quotient-scalar-good-comparison) -/
theorem ambientQuotientScalarModel_good_comparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E X) :
    Nonempty ((integralOperationsGoodLocalization l E X) ⋙
      (S.reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι X ⋙
        coefficientSequenceLimit l L X) ≅
      integralScalarOnGood l E L ι X) := by
  sorry

end WeilConjectures
