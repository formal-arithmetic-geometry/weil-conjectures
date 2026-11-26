/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CanonicalCoefficient.CanonicalCoefficientReduction

/-! # Representative laws after changing closed tensor presentations

Conjugating the tensor-model comparisons keeps their ordinary strict representative
normalizations.

## Implementation details

Every new tensor-model comparison is the old one followed by the adjoint comparison; in each
representative square functoriality cancels the conjugation and naturality moves it past the
representative identifications, leaving the old square. These are identities in the derived
sequence category, not deductions from equality of evaluations.

## References

* Stacks Project, Tags 07A4 and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures.CanonicalCoefficient
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The representative normalization equations for the conjugated data. -/
structure RepresentativeLaws (S : CoefficientDerivedSystemFibers l E W) : Prop where
  reduction_tensor : CoefficientReductionTensorNormalization l E W
    (reduction l E W S.toCoefficientDerivedSystemReduction)
  finite_tensor : CoefficientFiniteTensorNormalization l E W
    (reduction l E W S.toCoefficientDerivedSystemReduction)
  evaluation_tensor : CoefficientEvaluationTensorNormalization l E W
    (reduction l E W S.toCoefficientDerivedSystemReduction)
  reduction_evaluation : CoefficientReductionTensorEvaluation l E W
    (reduction l E W S.toCoefficientDerivedSystemReduction)
  quotient_tensor : CoefficientFiniteQuotientTensorNormalization l E W
    (tensors l E W S.toCoefficientDerivedSystemTensors)
    (quotientData l E W S.toCoefficientDerivedSystemTensors
      S.quotientCalculus.toCoefficientFiniteQuotientData)

/-- Conjugating the comparisons keeps their ordinary strict representative normalizations. -/
theorem representativeLaws (S : CoefficientDerivedSystemFibers l E W) :
    RepresentativeLaws l E W S := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro P Q hP hQ hPf hQf
    obtain ⟨C, D, Z, hC, hD, eC, eD, eZ, κC, κD, κZ, ψ,
      hPC, hQD, hTZ, hψ, hSq⟩ :=
      S.reductionTensor_normalization P Q hP hQ hPf hQf
    refine ⟨C, D, Z, hC, hD, eC, eD, eZ, κC, κD, κZ, ψ, hPC, hQD, hTZ, hψ, ?_⟩
    dsimp only [reduction]
    exact tensorSquare _ _ _ _ _ _ _ _ _ _ _ _ _ hSq
  · intro n P Q hP hQ
    dsimp only [reduction]
    exact tensorSquare _ _ _ _ _ _ _ _ _ _ _ _ _
      (S.finiteTensor_normalization n P Q hP hQ)
  · intro n P Q hP hQ
    dsimp only [reduction]
    exact tensorSquare _ _ _ _ _ _ _ _ _ _ _ _ _
      (S.evaluationTensor_normalization n P Q hP hQ)
  · intro P Q n
    exact evaluation_transport _ _ _ _ _ _ _ _ _ _ _ _ _ P Q
      (S.reductionTensor_evaluation P Q n)
  · intro m n h P Q hP hQ
    obtain ⟨e, he, hSq⟩ := S.quotientCalculus.tensor_model h P Q hP hQ
    refine ⟨e, he, ?_⟩
    exact tensorSquare _ _ _ _ _ _ _ _ _ _ _ _ _ hSq

end WeilConjectures.CanonicalCoefficient
