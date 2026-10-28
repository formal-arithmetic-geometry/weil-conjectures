/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientNormalizedReductionModels

/-! # Representative square for normalized tensor horizontality

Source: Stacks 07A4 and 0941; Zheng Construction 4.1.
(blueprint: lem-coef-normalized-tensor-horizontal-representative).
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

/-- The horizontal tensor square after choosing simultaneous K-flat representatives.
Source: Stacks 07A4 and 0941, and Zheng Construction 4.1.
(blueprint: lem-coef-normalized-tensor-horizontal-representative).

Proof: evaluate the two chosen K-flat complexes at level `m`, apply the ordinary
pure-tensor quotient comparison, and use the representative normalization fields of
`hE` and `Q.tensor_model`. The two chain maps agree on every local pure tensor; the
total-complex summand equations then give the displayed localized equality. -/
theorem coefficientNormalizedTensorHorizontalRepresentative
    (R : CoefficientDerivedSystemReduction l E W)
    (hE : CoefficientEvaluationTensorNormalization l E W R)
    (Q : CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors)
    (P V : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) P)
    (hV : CochainComplex.IsKFlatIndependentCoefficients
      (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
      (R := coefficientSequenceCommRingSheaf l E W) V)
    {m n : ℕ} (h : n ≤ m) :
    (coefficientFiniteQuotientDerived l E W h).map
        ((R.evaluationTensor m).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj V)) ≫
      (Q.tensor h).hom.app
        ((coefficientSequenceDerivedEvaluation l E W m).obj (DerivedCategory.Q.obj P),
          (coefficientSequenceDerivedEvaluation l E W m).obj (DerivedCategory.Q.obj V)) ≫
      (R.finiteClosed n).tensor.map
        (Prod.mkHom
          (coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h
            (DerivedCategory.Q.obj P))
          (coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h
            (DerivedCategory.Q.obj V))) =
    coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h
        (R.systemClosed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj V)) ≫
      (R.evaluationTensor n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj V) := by
  sorry

end WeilConjectures
