/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionRoosCompletionData
import WeilConjectures.SixFunctors.OpenTensorAugmentation.OpenTensorAugmentationLimitSquare

/-! # Descent of the augmented open tensor square through completion

## References

* Bhatt–Scholze, *The pro-étale topology for schemes*, 6.5.5 and 6.5.8
* [Stacks, Tag 0940]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenProjectionRoos

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

variable
  (SX : CoefficientDerivedSystemCalculus l E X)
  (SU : CoefficientDerivedSystemCalculus l E U)
  (AX : OpenSemilinearTensor.OrdinaryReduction l E X)
  (AU : OpenSemilinearTensor.OrdinaryReduction l E U)
  (st : IntegralOpenReduction.TensorComparison l E j o)
  (m : OpenSemilinearTensor.Comparison l E j o SX SU AX AU st)
  (c : IntegralOpenReduction.Comparison l E j o SX SU st)
  (q : OpenTensorQuotient.Comparison l E j o SX SU AX AU st m c)

attribute [local irreducible] integralOperationsTensorTowerFunctor
  coefficientTotalTensor integralOperationsTensorLevel
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  unrestrictedIntegralComplexFunctor scalarReductionExistence unrestrictedIntegralReductionExistence

/-- The completed open tensor isomorphism and its actual augmentation square. -/
theorem openProjectionCompletedSquare
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [U.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [j.IsOver (Spec (.of D.k))]
    [restrictionLimits : PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [restrictionColimits : PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)]
    (extension : RoosComparison (IntegralOpenReduction.extension l E j o))
    (flat : ∀ (W : Scheme.{u}) (P : CochainComplex (scalarReductionSource l E W) ℤ),
    integralOperationsGoodComplex l E W P →
      proEtaleFlatRepresentatives W (completedIntegralCommRingSheafUnrestricted l E W) P)
    (extendGood : ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ),
    integralOperationsGoodComplex l E U P → integralOperationsGoodComplex l E X
      ((OpenSemilinearTensor.extensionComplex l E j o).obj P))
    (restrictGood : ∀ (P : CochainComplex (scalarReductionSource l E X) ℤ),
    integralOperationsGoodComplex l E X P → integralOperationsGoodComplex l E U
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj P))
    (ordinary : leftInputs l E j o ⋙ q.tensorX.ordinary.tensor ≅
    rightInputs l E j o ⋙ q.tensorU.ordinary.tensor ⋙ IntegralOpenReduction.shriek l E j o)
    (_ordinary_representative : OrdinaryRepresentative l E j o SX SU AX AU st m c q
      flat extendGood restrictGood ordinary)
    :
    ∃ (gamma : completedLeft l E j o ≅ completedRight l E j o),
    ∃ (_units : ∀ K : sfIntegralConstructibleCategory l E U × sfIntegralConstructibleCategory l E X,
    (q.tensorX.chi l E).app ((leftInputs l E j o).obj (K.1.obj, K.2.obj)) ≫
        gamma.hom.app K =
      ordinary.hom.app (K.1.obj, K.2.obj) ≫
        (IntegralOpenReduction.shriek l E j o).map
          ((q.tensorU.chi l E).app ((rightInputs l E j o).obj (K.1.obj, K.2.obj)))),
    ∃ (_invertibleUnits : ∀ K :
      sfIntegralConstructibleCategory l E U × sfIntegralConstructibleCategory l E X,
    IsIso ((q.tensorX.chi l E).app ((leftInputs l E j o).obj (K.1.obj, K.2.obj))) ∧
      IsIso ((q.tensorU.chi l E).app ((rightInputs l E j o).obj (K.1.obj, K.2.obj)))),
    CompletedRepresentative l E j o SX SU AX AU st m c q
      extension extendGood restrictGood gamma := by
  sorry

end WeilConjectures.OpenProjectionRoos
