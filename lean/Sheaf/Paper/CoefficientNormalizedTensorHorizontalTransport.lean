/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefficientNormalizedTensorHorizontalRepresentative

/-! # Transport of normalized tensor horizontality from representatives

Source: Stacks 06YS and 07A4.
(blueprint: lem-coef-normalized-tensor-horizontal-transport).
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

/-- Equality of the normalized tensor square on K-flat representatives transports to
all objects of the unbounded derived coefficient category.
Source: Stacks 06YS, 07A4; the resolving-representative transport in the proof of
Zheng Construction 4.1.
(blueprint: lem-coef-normalized-tensor-horizontal-transport).

Proof: resolve each derived object by a flat-term K-flat complex, apply the assumed
representative square, and cancel the epimorphic maps induced by the two resolution
isomorphisms. Naturality of the evaluation tensor and of the quotient adjunction
transports the equality along those isomorphisms. -/
theorem coefficientNormalizedTensorHorizontalTransport
    (R : CoefficientDerivedSystemReduction l E W)
    (hE : CoefficientEvaluationTensorNormalization l E W R)
    (Q : CoefficientFiniteQuotientCalculus l E W R.toCoefficientDerivedSystemTensors)
    (hrep : ∀ (P V : CochainComplex (coefficientSequenceModules l E W) ℤ),
      CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) P →
      CochainComplex.IsKFlatIndependentCoefficients
        (J := coefficientSequenceTopology (Scheme.ProEt.topology W))
        (R := coefficientSequenceCommRingSheaf l E W) V →
      ∀ {m n : ℕ} (h : n ≤ m),
        (coefficientFiniteQuotientDerived l E W h).map
            ((R.evaluationTensor m).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj V)) ≫
          (Q.tensor h).hom.app
            ((coefficientSequenceDerivedEvaluation l E W m).obj (DerivedCategory.Q.obj P),
              (coefficientSequenceDerivedEvaluation l E W m).obj (DerivedCategory.Q.obj V)) ≫
          (R.finiteClosed n).tensor.map
            (Prod.mkHom
              (coefficientSequenceTransitionAdjoint l E W
                R.toCoefficientDerivedSystemTensors Q h (DerivedCategory.Q.obj P))
              (coefficientSequenceTransitionAdjoint l E W
                R.toCoefficientDerivedSystemTensors Q h (DerivedCategory.Q.obj V))) =
        coefficientSequenceTransitionAdjoint l E W R.toCoefficientDerivedSystemTensors Q h
            (R.systemClosed.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj V)) ≫
          (R.evaluationTensor n).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj V))
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
  sorry

end WeilConjectures
