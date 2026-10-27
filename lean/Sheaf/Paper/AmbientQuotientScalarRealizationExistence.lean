/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
import Sheaf.Paper.AmbientQuotientScalarGoodComparison

/-! # Ambient scalar quotient realization

Source: Stacks 06YY and 0941; the scalar quotient construction in the final
common-stage transport paragraph of the trace-transport blueprint.
(blueprint: new-trf-ambient-quotient-scalar-realization)

Proof: construct the scalar extension functor on flat-term K-flat complexes by
balanced finite quotient tensor association, identify its Roos tower with the
completed scalar tower, and descend the comparison through the localization.
-/

@[expose] public section
set_option autoImplicit false
universe t u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- The ambient scalar realization exists before imposing its representative
normalization. Source: Stacks 06YY and 0941; strict quotient scalar
construction in the common-stage transport argument.
(blueprint: new-trf-ambient-quotient-scalar-realization) -/
theorem ambientQuotientScalarModel_realization_exists (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
    (ι : E →ₐ[ℚ_[l]] L) (X : Scheme.{t})
    (S : CoefficientDerivedSystemCalculus l E X) :
    Nonempty (integralScalarExtensionOfUniverses l E L ι X ≅
      S.reduction ⋙ integralComparisonDerivedSequenceScalar l E L ι X ⋙
        coefficientSequenceLimit l L X) := by
  let V := integralComparisonDerivedSequenceScalar l E L ι X ⋙
    coefficientSequenceLimit l L X
  let Λ := integralOperationsGoodLocalization l E X
  obtain ⟨δ⟩ : Nonempty (Λ ⋙ (S.reduction ⋙ V) ≅
      integralScalarOnGood l E L ι X) :=
    ambientQuotientScalarModel_good_comparison l E L ι X S
  obtain ⟨r, hr, _⟩ :=
    (integralScalarExtensionWellDefined l E L ι X).2.choose_spec.choose_spec.2.2.1
      (S.reduction ⋙ V) δ
  change Functor.isoWhiskerLeft Λ r ≪≫ δ =
    integralScalarExtensionComparisonOfUniverses l E L ι X at hr
  exact ⟨r⟩

end WeilConjectures
