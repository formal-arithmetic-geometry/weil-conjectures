/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedReductionModels
import WeilConjectures.SixFunctors.Coefficient.Normalized.CoefficientNormalizedTensorHorizontalTransport

/-! # Horizontal compatibility of normalized tensor comparisons

We show that horizontal reduction of a tensor is the tensor of the two reductions.

## Implementation details

Both systems are resolved on the sequence site by flat-term K-flat complexes. The ordinary
horizontal maps send a local pure tensor to the tensor of the two horizontal images, and the
ordinary quotient unit is `1 ⊗ x`, so both sides are the same balanced pure-tensor map. The
equality of chain maps is localized and transported to arbitrary unbounded systems by
naturality. No faithfulness of finite derived evaluation and no flatness of quotient rings is
used.

## References

* [Zheng, Construction 4.1]
* [Stacks, Tags 03EK, 06YY, 07A4, 08J9, 0941]
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u a b v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- Horizontal reduction of a tensor is the tensor of the two reductions.
There is no cartesianness or internal-Hom hypothesis here. -/
theorem coefficientNormalizedTensorHorizontal
    (R : CoefficientDerivedSystemReduction l E W)
    (hE : CoefficientEvaluationTensorNormalization l E W R)
    (Q : CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors)
    (P V : coefficientSequenceDerived l E W) {m n : ℕ} (h : n ≤ m) :
    (coefficientFiniteQuotientDerived l E W h).map
        ((R.evaluationTensor m).hom.app (P, V)) ≫
      (Q.tensor h).hom.app
        ((coefficientSequenceDerivedEvaluation l E W m).obj P,
          (coefficientSequenceDerivedEvaluation l E W m).obj V) ≫
      (R.finiteClosed n).tensor.map
        (Prod.mkHom
          (coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h P)
          (coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h V)) =
    coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h
        (R.systemClosed.tensor.obj (P, V)) ≫
      (R.evaluationTensor n).hom.app (P, V) := by
  apply coefficientNormalizedTensorHorizontalTransport l E W R hE Q
  intro P' V' hP' hV' m n h
  exact coefficientNormalizedTensorHorizontalRepresentative l E W R hE Q P' V' hP' hV' h

end WeilConjectures
