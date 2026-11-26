/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionRoosCompletionData
import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionOrdinaryRoos
import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionCompletedSquare
import WeilConjectures.SixFunctors.OpenProjectionRoos.OpenProjectionRestrictionNormalization

/-! # Assembly of the augmented open projection Roos completion

We assemble the ordinary Roos comparison, the completed square and the restriction
normalization into the augmented open projection Roos completion `Completion`.

## Implementation details

The completion supplies only the integral open tensor component of the exchange projection;
it asserts none of the independent proper or other coefficient-stage data.

## References

* Stacks Project, Tag 09BP
* Bhatt--Scholze, Lemmas 6.5.5 and 6.5.8, pp. 49--50
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.OpenProjectionRoos

section RestrictIso
universe a b c v₁ v₂ v₃
variable {A : Type a} {B : Type b} {C : Type c}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  {L : A ⥤ B} {I : A ⥤ C}

private def restrictIso (S : C ⥤ B) (R : B ⥤ C)
    (unit : 𝟭 C ≅ S ⋙ R) (gamma : L ≅ I ⋙ S) : L ⋙ R ≅ I :=
  Functor.isoWhiskerRight gamma R ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft I unit.symm ≪≫ Functor.rightUnitor _

private theorem restrictIso_hom_app (S : C ⥤ B) (R : B ⥤ C)
    (unit : 𝟭 C ≅ S ⋙ R) (gamma : L ≅ I ⋙ S) (K : A) :
    (restrictIso S R unit gamma).hom.app K =
      R.map (gamma.hom.app K) ≫ unit.inv.app (I.obj K) := by
  simp only [restrictIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.rightUnitor_hom_app,
    Iso.symm_hom, Functor.id_obj, Category.id_comp]
  exact congrArg (fun f ↦ R.map (gamma.hom.app K) ≫ f)
    (Category.comp_id (unit.inv.app (I.obj K)))
end RestrictIso

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
  (o : IntegralOpenReduction.Operations l E j)

private theorem restrictionLimits :
    PreservesFiniteLimits (IntegralOpenReduction.restriction l E j o) := by
  have := SheafOfModules.localizedSystemRestrictionLimits.{u + 1, u, u}
    (completedIntegralCommRingSheafUnrestricted l E X) (IntegralOpenReduction.openObject j)
  exact comp_preservesFiniteLimits
    (SheafOfModules.localizedSystemRestriction.{u + 1, u, u}
      (completedIntegralCommRingSheafUnrestricted l E X) (IntegralOpenReduction.openObject j))
    o.integral.inverse

private theorem restrictionColimits :
    PreservesFiniteColimits (IntegralOpenReduction.restriction l E j o) := by
  have := SheafOfModules.localizedSystemRestrictionColimits.{u + 1, u, u}
    (completedIntegralCommRingSheafUnrestricted l E X) (IntegralOpenReduction.openObject j)
  exact comp_preservesFiniteColimits
    (SheafOfModules.localizedSystemRestriction.{u + 1, u, u}
      (completedIntegralCommRingSheafUnrestricted l E X) (IntegralOpenReduction.openObject j))
    o.integral.inverse

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
  unrestrictedIntegralComplexFunctor scalarReductionExistence unrestrictedIntegralReductionExistence

attribute [local irreducible] Completion CompletionData
  OrdinaryRepresentative CompletedRepresentative RestrictionRepresentative
  CategoryTheory.Limits.limit HasDerivedCategory.standard
  SheafOfModules.overFunctor SheafOfModules.extensionByZeroPresheaf
  SheafOfModules.monoidalCategory Functor.mapDerivedCategory
  Functor.mapDerivedCategoryFactors Functor.mapHomologicalComplex
  unrestrictedIntegralReductionFunctor integralCompletedTensor integralCompletedTensorComparison
  integralOperationsRoosFunctor integralOperationsRoosMap
  CochainComplex.mappingCone OpenFactorCoherence.Tensor.chi
  Classical.choose colimit.cocone colimit.isColimit
  Functor.map₂HomologicalComplex Functor.mapBifunctorHomologicalComplex
  Functor.mapBifunctorHomologicalComplexObj integralCompletedTensorDescent
  SheafOfModules.forget GradedObject.mapObj

set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
/-- The augmented open projection square has the specified Roos completion and actual
completion-unit normalization, naturally on the integral constructible domain. -/
theorem openProjectionRoosCompletion (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [U.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [j.IsOver (Spec (.of D.k))] :
    Completion l E j o SX SU AX AU st m c q := by
  have := restrictionLimits l E j o
  have := restrictionColimits l E j o
  have flat : ∀ (W : Scheme.{u}) (P : CochainComplex (scalarReductionSource l E W) ℤ),
      integralOperationsGoodComplex l E W P →
        proEtaleFlatRepresentatives W (completedIntegralCommRingSheafUnrestricted l E W) P :=
    fun _ P h ↦ ⟨(CochainComplex.isKFlatIndependentCoefficients_iff_isKFlat P).mp h.1, h.2⟩
  have extendGood : ∀ (P : CochainComplex (scalarReductionSource l E U) ℤ),
      integralOperationsGoodComplex l E U P → integralOperationsGoodComplex l E X
        ((OpenSemilinearTensor.extensionComplex l E j o).obj P) := by
    intro P hP
    exact ⟨m.kflat P hP.1 hP.2, m.preservesFlatTerms P hP.1 hP.2⟩
  obtain ⟨extension, restriction, moduleUnit, hmoduleUnit, unit, hunit,
    restrictGood, ordinary, hordinary⟩ :=
    openProjectionOrdinaryRoos l E j o SX SU AX AU st m c q D hl flat extendGood
  have square := openProjectionCompletedSquare l E j o SX SU AX AU st m c q D hl
    extension flat extendGood restrictGood ordinary
  obtain ⟨gamma, hunits, hinvertible, hrepresentative⟩ := square hordinary
  let tensorRestriction : completedLeft l E j o ⋙ IntegralOpenReduction.star l E j o ≅
      completedInside l E j o :=
    restrictIso (IntegralOpenReduction.shriek l E j o)
      (IntegralOpenReduction.star l E j o) unit gamma
  have hfinite := openProjectionRestrictionNormalization l E j o SX SU AX AU st m c q
    extension restriction moduleUnit hmoduleUnit unit hunit extendGood restrictGood
    gamma hrepresentative
  unfold Completion CompletionData
  refine ⟨inferInstance, inferInstance, extension, restriction, moduleUnit, hmoduleUnit,
    unit, hunit, flat, extendGood, restrictGood, ordinary, hordinary, gamma,
    hunits, hinvertible, hrepresentative, tensorRestriction, ?_, hfinite⟩
  intro K
  exact (restrictIso_hom_app (IntegralOpenReduction.shriek l E j o)
    (IntegralOpenReduction.star l E j o) unit gamma K).symm

end WeilConjectures.OpenProjectionRoos
