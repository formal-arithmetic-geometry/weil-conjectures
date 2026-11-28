/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionRoosCompletionData
import WeilConjectures.SixFunctors.SfOpenRoos.SfOpenRoosRestrictionUnit
import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionRestrictionUnit

/-! # Restriction of the completed projection through the actual open unit

## References

* Stacks Project, Tags 09BP and 0941
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

/-- Restricting the completed representative gives the strict finite restriction
comparison of the same quotient towers. -/
theorem openProjectionRestrictionNormalization
    [restrictionLimits : PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o)]
    [restrictionColimits : PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o)]
    (extension : RoosComparison (IntegralOpenReduction.extension l E j o))
    (restriction : RoosComparison (IntegralOpenReduction.restriction l E j o))
    (moduleUnit : 𝟭 (scalarReductionSource l E U) ≅
    IntegralOpenReduction.extension l E j o ⋙ IntegralOpenReduction.restriction l E j o)
    (_moduleUnit_hom : moduleUnit.hom = (IntegralOpenReduction.ordinaryAdjunction l E j o).unit)
    (unit : 𝟭 (DerivedCategory (scalarReductionSource l E U)) ≅
    IntegralOpenReduction.shriek l E j o ⋙ IntegralOpenReduction.star l E j o)
    (_unit_hom : unit.hom = (IntegralOpenReduction.openAdjunction l E j o).unit)
    (extendGood : ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ),
    integralOperationsGoodComplex l E U P → integralOperationsGoodComplex l E X
      ((OpenSemilinearTensor.extensionComplex l E j o).obj P))
    (restrictGood : ∀ (P : CochainComplex (scalarReductionSource l E X) ℤ),
    integralOperationsGoodComplex l E X P → integralOperationsGoodComplex l E U
      ((OpenSemilinearTensor.restrictionComplex l E j o).obj P))
    (gamma : completedLeft l E j o ≅ completedRight l E j o)
    (_representative : CompletedRepresentative l E j o SX SU AX AU st m c q
      extension extendGood restrictGood gamma)
    :
    let tensorRestriction : completedLeft l E j o ⋙ IntegralOpenReduction.star l E j o ≅
        completedInside l E j o :=
      Functor.isoWhiskerRight gamma (IntegralOpenReduction.star l E j o) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (completedInside l E j o) unit.symm ≪≫
        Functor.rightUnitor _
    RestrictionRepresentative l E j o SX SU AX AU st m c q
      restriction moduleUnit extendGood restrictGood
      tensorRestriction := by
  intro tensorRestriction Q F hQ hF hK hP z hup hlow
  refine ⟨(onTowers _).mapIso z.gamma ≪≫ (towerUnitIso moduleUnit _).symm, fun n i ↦ ?_, ?_⟩
  · simp
  · exact unit_inv_comp_eq (IntegralOpenReduction.shriek l E j o)
      (IntegralOpenReduction.star l E j o) unit _ _ _ _ _ _ _ _ _ _ _
      (by simp [tensorRestriction]) (_representative Q F hQ hF hK hP z hup hlow)
      (roosComparison_derived_unit_inv (IntegralOpenReduction.ordinaryAdjunction l E j o)
        moduleUnit _moduleUnit_hom unit _unit_hom extension restriction _ _ z.gamma)
      (derivedQ_map_integralOperationsRoosMap_hom_inv z.gamma)

end WeilConjectures.OpenProjectionRoos
