/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionReductionData
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionOrdinaryStrictTensor
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionStrictDerivedComparison
import WeilConjectures.SmoothPurity.Coefficient.CoefficientExtensionStrictTensorNormalized
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients

/-! # Strict representatives for finite coefficient extension

Source: the integral-operations tensor associator; Stacks 03EK and 03D7.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe t u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

variable (A : CoefficientExtensionSystems l E L ι W)

/-- Simultaneous strict finite quotient representatives of derived coefficient extension.
Source: integral operations, Stacks 06YY, 07A6 and 0941
(blueprint: lem-pur-legacy-coefficient-extension-strict-representatives).
Proof: use the ringed sequence projection to form the ordinary strict system whose
nth term is tensor with the nth target quotient. Its tensor generators determine
its quotient transitions. Apply it degreewise to flat-term K-flat complexes.
The given balanced associations identify the evaluated complexes with the iterated
finite scalar models. Transpose the ordinary units, using the reduction unit and
scalar evaluation formulas, to obtain a natural comparison from the specified
derived extension. At each level this is the composite of the two universal
K-flat comparisons and the given association. Both scalar extensions preserve
K-flatness, so these comparisons are invertible. The jointly conservative
evaluations make the system comparison invertible. For m at least n, scalar
extension of the mth term to the nth quotient is identified with the nth term by
balanced tensor association. Its adjoint is precisely the specified quotient
transition. Thus the universal Hom criterion gives normalization, first on good
representatives and then on every derived object by a K-flat resolution. -/
theorem coefficientExtensionStrictRepresentative_exists_legacy
    (SE : CoefficientDerivedSystemCalculus l E W)
    (association : ∀ n : ℕ,
      scalarReductionExtension l E W n ⋙ (A.levels n).model.E ≅
        integralScalarReduction l E L ι W n)
    (hassociation : IsCoefficientExtensionAssociation l E L ι W A association) :
    ∃ (direct : (integralOperationsGoodComplex l E W).FullSubcategory ⥤
        CochainComplex (coefficientSequenceModules l L W) ℤ)
      (directEvaluation : ∀ n : ℕ,
        direct ⋙ (coefficientSequenceEvaluation l L W n).mapHomologicalComplex (.up ℤ) ≅
          (integralOperationsGoodComplex l E W).ι ⋙ integralScalarFiniteComplex l E L ι W n)
      (model : integralOperationsGoodLocalization l E W ⋙
        coefficientExtensionSystem l E L ι W SE A ≅ direct ⋙ DerivedCategory.Q),
      IsCoefficientExtensionStrictTransition l E L ι W direct directEvaluation ∧
      IsCoefficientExtensionModelEvaluation l E L ι W SE A association direct
        directEvaluation model ∧
      ∀ K : DerivedCategory (scalarReductionSource l E W),
        IsNormalizedCoefficientSequence l L W
          ((coefficientExtensionSystem l E L ι W SE A).obj K) := by
  classical
  obtain ⟨direct, directEvaluation, htransition⟩ :=
    coefficientExtensionOrdinaryStrictTensor_exists l E L ι W
  obtain ⟨model, hmodel⟩ := coefficientExtensionStrictDerivedComparison
    l E L ι W A SE association hassociation direct directEvaluation htransition
  refine ⟨direct, directEvaluation, model, htransition, hmodel, ?_⟩
  intro K
  obtain ⟨P, ⟨e⟩⟩ := coefficientExtensionGoodRepresentative l E W K
  have hP : IsNormalizedCoefficientSequence l L W
      (DerivedCategory.Q.obj (direct.obj P)) :=
    coefficientExtensionStrictTensor_normalized
      l E L ι W direct directEvaluation htransition P
  have hC : IsNormalizedCoefficientSequence l L W
      ((coefficientExtensionSystem l E L ι W SE A).obj
        ((integralOperationsGoodLocalization l E W).obj P)) :=
    coefficientSequenceNormalized_of_iso l L W (model.app P).symm hP
  intro m n h Z
  exact coefficientSequenceNormalized_of_iso l L W
    ((coefficientExtensionSystem l E L ι W SE A).mapIso e) hC h Z

end WeilConjectures
