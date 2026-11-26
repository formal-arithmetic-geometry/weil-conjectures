/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensor
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionTensorDescent
import WeilConjectures.SixFunctors.Coefficient.CoefficientOrdinaryReductionComparison

/-! # Tensor comparison from the strict K-flat reduction model

## Implementation details

On flat-term K-flat representatives the strict model identifies reduction with ordinary
extension to the sequence ring, which has a natural total-tensor comparison obtained by
sheafifying `b ⊗ (x ⊗ y) ↦ (b ⊗ x) ⊗ (1 ⊗ y)`. Extension to the sequence ring preserves
K-flatness and flat terms, so `tensorComparisonDescent` applies to the two prescribed tensor
models. The resulting sequence extension is identified with `L` by uniqueness of left adjoints
to `coefficientSequenceLimit`. No unit/counit projection equation is needed, and no
invertibility of quotient ring maps is used.

## References

* [Stacks, Tag 06YS]
* [Stacks, Tag 06YY]
* [Stacks, Tag 07A4]
* [Stacks, Tag 0941]
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The simultaneous strict K-flat reduction model is compatible with tensor,
for a left adjoint of the specified total limit, before choosing tensor maps.
-/
theorem coefficientReductionModelTensor_exists
    (T : CoefficientDerivedSystemTensors l E W)
    (L : DerivedCategory (scalarReductionSource l E W) ⥤ coefficientSequenceDerived l E W)
    (adj : L ⊣ coefficientSequenceLimit l E W)
    (ρ : ∀ n : ℕ, L ⋙ coefficientSequenceDerivedEvaluation l E W n ≅
      coefficientFiniteDerivedExtension l E W n)
    (_hL : CoefficientReductionModels l E W L ρ) :
    Nonempty (T.integralClosed.tensor ⋙ L ≅ L.prod L ⋙ T.systemClosed.tensor) := by
  obtain ⟨M⟩ := OrdinaryQuotient.ordinaryModel_exists l E W
  obtain ⟨b, -⟩ := OrdinaryQuotient.OrdinaryModel.quotientTensor_exists l E W M
  obtain ⟨ε, -, hε, -⟩ := OrdinaryQuotient.reductionComparison_exists l E W M L adj
  obtain ⟨μ, -⟩ := OrdinaryQuotient.reductionTensor_descent l E W M T L ε hε b
    (OrdinaryQuotient.OrdinaryModel.quotient_isKFlat l E W M)
  exact ⟨μ⟩

end WeilConjectures
