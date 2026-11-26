/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Derived.CoefficientDerivedSystemEvaluationData
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionCore
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionNormalizations

/-! # Normalized coefficient reduction and quotient tensors

We construct the reduction of a coefficient system with its normalized tensor comparisons and
finite quotient calculus, before internal Hom or sections.

## Implementation details

The construction applies `SequenceProjection.pushforwardLimitProjections` to the completed
coefficient ring and its finite quotient tower and identifies strict systems with sequence-site
modules via `strictSystemSequenceEquivalence`. Canonical tensor pullback supplies the tensor
comparisons, whose maps on simultaneous K-flat representatives are ordinary pure-tensor maps.
Iterated scalar extension shows that every reduction is normalized. The tensor models are
retained verbatim.

## References

* [Stacks, Tags 06YS, 06YY, 07A4, 07A6, 08J9, 0941, 0FPT]
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The three tensor models retain the ordinary associator, unit and symmetry formulas.
These are the coherence witnesses of the existing ringed-site tensor theorem. -/
def CoefficientDerivedSystemTensorCoherence (T : CoefficientDerivedSystemTensors l E W) :
    Prop :=
  (∃ β : @SymmetricCategory (DerivedCategory (scalarReductionSource l E W))
      _ T.integralClosed.monoidal,
    Nonempty (RingedDerivedTensorCoherence.{t+1, t, u} (Scheme.ProEt.topology W)
      (completedIntegralCommRingSheafUnrestricted l E W)
      T.integralClosed T.integralTensorModel β)) ∧
  (∃ β : @SymmetricCategory (coefficientSequenceDerived l E W) _ T.systemClosed.monoidal,
    Nonempty (RingedDerivedTensorCoherence.{t+1, t, u}
      (coefficientSequenceTopology (Scheme.ProEt.topology W))
      (coefficientSequenceCommRingSheaf l E W) T.systemClosed T.systemTensorModel β)) ∧
  ∀ n : ℕ, ∃ β : @SymmetricCategory (normalizedDVRDerived l E W n)
      _ (T.finiteClosed n).monoidal,
    Nonempty (RingedDerivedTensorCoherence.{t+1, t, u} (Scheme.ProEt.topology W)
      (integralCoefficientCommRingSheaf l E W n) (T.finiteClosed n) (T.finiteTensorModel n) β)

attribute [local irreducible] CoefficientDerivedSystemTensorCoherence

/-- Reduction with its normalized tensor comparisons, before internal Hom or sections.
No internal-Hom fiber, global sections, or total-sections comparison is asserted. -/
theorem coefficientNormalizedReductionModels (T : CoefficientDerivedSystemTensors l E W) :
    ∃ R : CoefficientDerivedSystemReduction l E W,
      R.toCoefficientDerivedSystemTensors = T ∧
      CoefficientReductionTensorNormalization l E W R ∧
      CoefficientFiniteTensorNormalization l E W R ∧
      CoefficientEvaluationTensorNormalization l E W R ∧
      CoefficientReductionTensorEvaluation l E W R ∧
      Nonempty (CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors) :=
  by
  obtain ⟨R, hRT, hQ⟩ := coefficientNormalizedReductionCore l E W T
  obtain ⟨S, hSR, hR, hF, hE, hRE⟩ :=
    coefficientNormalizedReductionNormalizations l E W R
  have hST : S.toCoefficientDerivedSystemTensors = R.toCoefficientDerivedSystemTensors :=
    congrArg CoefficientDerivedSystemReductionModel.toCoefficientDerivedSystemTensors hSR
  exact ⟨S, hST.trans hRT, hR, hF, hE, hRE, hST.symm ▸ hQ⟩

end WeilConjectures
