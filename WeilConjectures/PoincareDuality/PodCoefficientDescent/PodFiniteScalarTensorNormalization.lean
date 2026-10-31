/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Integral.IntegralOperationsScalarComparisons
import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeTensor

/-! # The prescribed finite scalar tensor comparison on arbitrary K-flat inputs

Source: blueprint dual-Tate compatibility, Step 5; Stacks 07A4 and 08J9.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.PodCoefficientDescent
attribute [local irreducible] HasDerivedCategory.standard
  completedIntegralCoefficientSheafUnrestricted scalarIntegralClosed scalarClosedTensor
  scalarReductionExistence scalarReductionDerivedExistence

attribute [-instance] integralOperationsSiteSmall
  GrothendieckTopology.hasSheafify_of_essentiallySmall
  GrothendieckTopology.hasSheafify_proEtTopology
  integralOperationsAbSheafify integralOperationsAbLocallyBijective
private local instance (W : Scheme.{u}) : EssentiallySmall.{u + 1} W.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
private local instance (W : Scheme.{u}) :
    HasSheafify (ProEt.topology W) AddCommGrpCat.{u + 1} :=
  integralCoefficientAbSheafify.{u, u} W
private local instance (W : Scheme.{u}) :
    (ProEt.topology W).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
  integralCoefficientAbLocallyBijective.{u, u} W

set_option maxHeartbeats 500000 in
-- Control elaboration of the exact scalar model and its representative equations.
/-- The prescribed scalar tensor comparison has its normalization on every K-flat pair.
Source: blueprint Step 5; Stacks 07A4, 08J9.
(blueprint: lem-pod-finite-scalar-tensor-all-kflat).
Proof: construct the cochain scalar model from the actual exact extension functor.
The finite-free tensor theorem supplies chain and derived tensor comparisons.
Their generator and good-representative equations identify them with the recorded
comparisons by uniqueness. The supplied normalization on all K-flat pairs then
becomes the displayed equation for those same recorded comparisons. -/
theorem scalarClosedTensor_allKFlat (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L)
    (W : Scheme.{u})
    (P Q : CochainComplex (integralTowerModules.{u, u} l E W) ℤ)
    (hP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        W.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} W.ProEt)
      (J := ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W) P)
    (hQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        W.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} W.ProEt)
      (J := ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l E W) Q) :
    ∃ (hEP : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        W.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} W.ProEt)
        (J := ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l L W)
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj P))
      (hEQ : @CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
        W.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} W.ProEt)
        (J := ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted.{u, u} l L W)
        (((integralOrdinaryScalar l E L ι W).mapHomologicalComplex (.up ℤ)).obj Q)),
      (integralOrdinaryDerivedScalar l E L ι W).map
          (CoefficientTensorModels.iso.{u, u + 1, u, u + 2} (ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted.{u, u} l E W) (scalarIntegralClosed l E W)
            (scalarIntegralModels l E W) P Q hP hQ).hom ≫
        (scalarClosedTensor l E L ι W).hom.app
          (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
        (scalarIntegralClosed l L W).tensor.map
          (Prod.mkHom ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app P)
            ((integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app Q)) =
      (integralOrdinaryScalar l E L ι W).mapDerivedCategoryFactors.hom.app
          ((coefficientTotalTensor.{u,u + 1,u} (ProEt.topology W)
            (completedIntegralCommRingSheafUnrestricted.{u, u} l E W)).obj (P, Q)) ≫
        DerivedCategory.Q.map ((scalarOrdinaryTensorChain l E L ι W).hom.app (P, Q)) ≫
        (CoefficientTensorModels.iso.{u, u + 1, u, u + 2} (ProEt.topology W)
          (completedIntegralCommRingSheafUnrestricted.{u, u} l L W) (scalarIntegralClosed l L W)
          (scalarIntegralModels l L W) _ _ hEP hEQ).hom := by
  classical
  let J : GrothendieckTopology W.ProEt := AlgebraicGeometry.Scheme.ProEt.topology W
  let R : Sheaf J CommRingCat.{u + 1} := completedIntegralCommRingSheafUnrestricted.{u, u} l E W
  let S : Sheaf J CommRingCat.{u + 1} := completedIntegralCommRingSheafUnrestricted.{u, u} l L W
  let φ : R ⟶ S := integralCompletedScalarMap l E L ι W
  let F := integralOrdinaryScalar l E L ι W
  have hobj : ∀ A, F.obj A = SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ A :=
    (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose
  have hmap : ∀ {A B} (f : A ⟶ B), F.map f = eqToHom (hobj A) ≫
      SheafOfModules.changeOfRingsHom.{u, u + 1, u + 1} φ A f ≫ eqToHom (hobj B).symm := by
    intro A B f
    exact (integralOrdinaryScalarWitness l E L ι W).choose_spec.choose_spec.choose f
  let D : SheafOfModules.DerivedChangeOfRingsCochainModel.{u + 1, u, u + 1,
      u + 2, u + 2} φ :=
    { E := F
      obj_eq := hobj
      map_eq := hmap
      preserves := by
        intro P Q f hP hQ hf
        let := hf
        infer_instance
      T := F.mapDerivedCategory
      pointwise := Functor.hasPointwiseLeftDerivedFunctor_of_inverts _
        (F.mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso (.up ℤ))
      ε := F.mapDerivedCategoryFactors.hom
      universal := Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactors
      triangulated := ⟨inferInstance, inferInstance⟩
      computes := fun _ _ ↦ inferInstance }
  obtain ⟨κ, μ, hκ, hμ⟩ := ringedFiniteFreeHomBaseChange_tensor.{u + 1, u, u, u + 2}
    J φ D (scalarIntegralClosed l E W) (scalarIntegralClosed l L W)
    (scalarIntegralModels l E W) (scalarIntegralModels l L W)
  have hs (A : integralTowerModules.{u, u} l E W) (U : W.ProEtᵒᵖ)
      (x : A.val.obj U) :
      ringedFiniteFreeScalarSection.{u + 1, u, u} J φ F hobj A U 1 x =
        integralOrdinaryTensorSection l E L ι W A U 1 x := by
    unfold ringedFiniteFreeScalarSection integralOrdinaryTensorSection
    have hη :=
      PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app.{u + 1, u,
        u + 1, u + 1} (J := J)
        (𝟙 (SheafOfModules.derivedChangeRingIndependentCoefficients J S).obj)
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ A)
    with_unfolding_all exact (congrArg ((eqToHom (hobj A).symm).val.app U)
      (ConcreteCategory.congr_hom (congr_app hη U) _))
  have hk : κ = scalarOrdinaryTensorChain l E L ι W := by
    apply (scalarOrdinaryTensorChain_existsUnique l E L ι W).unique
    · intro P Q p q U x y
      simpa only [D, hs] using hκ P Q p q U x y
    · exact (scalarOrdinaryTensorChain_existsUnique l E L ι W).exists.choose_spec
  have hm : μ = scalarClosedTensor l E L ι W := by
    apply (scalarClosedTensor_existsUnique l E L ι W).unique
    · intro P Q
      obtain ⟨hP, hQ, heq⟩ := hμ P.obj Q.obj P.property.1 Q.property.1
      simp only [D, hk, F, J, R, S, integralOrdinaryDerivedScalar] at heq ⊢
      exact heq
    · unfold scalarClosedTensor
      exact (scalarClosedTensor_existsUnique l E L ι W).exists.choose_spec
  obtain ⟨hEP, hEQ, heq⟩ := hμ P Q hP hQ
  refine ⟨hEP, hEQ, ?_⟩
  rw [hk, hm] at heq
  convert heq using 1
  rfl

end WeilConjectures.PodCoefficientDescent
