/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionEvaluationFactors
public import WeilConjectures.SixFunctors.FixProjectionCompactification.Coordinates.IntegralProjectionCoordinateData
import WeilConjectures.SixFunctors.IntegralPublishedPullback.IntegralPublishedCounitEvaluation
import all WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible

/-! # Unary completed-pullback evaluation

Source: fix-prop-projection-formula.proof.md, successive coefficient reductions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open Opposite CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures
open IntegralPublishedPullback
section StageModels
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
attribute [local irreducible] HasDerivedCategory.standard integralDerivedPullback
attribute [local implicit_reducible] integralOperationsGoodComplex
  integralOperationsGoodLocalization CochainComplex.IsKFlatResolutionIndependentCoefficients
private theorem level_intrinsic_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ) :
    pullbackTensorLevelIntrinsic l E f n =
      (coefficientProEtaleModuleAdjunction.{u, u} f
        (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1))))).leftAdjointUniq
      (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))) := by
  have h := pullbackTensorLevelIntrinsic_existsUnique l E f n
  apply h.unique h.exists.choose_spec
  intro M U x
  exact congrArg (fun a ↦ a.val.app (op U) x)
    (Adjunction.unit_leftAdjointUniq_hom_app
      (coefficientProEtaleModuleAdjunction.{u, u} f
        (CommRingCat.of (ULift.{u + 1} (finiteCoefficientRing l E (n + 1)))) )
      (sfIntrinsicConstantModuleAdjunction f (finiteCoefficientRing l E (n + 1))) M)

private theorem reduction_model_hom
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (m : ℕ) (Y : SixFunctorSpace D) (K : sfIntegralConstructibleCategory C.l E Y.obj.left)
    (P : (integralOperationsGoodComplex C.l E Y.obj.left).FullSubcategory)
    (e : DerivedCategory.Q.obj P.obj ≅ K.obj) :
    (sixFunctorIntegralReductionModel C E m Y K P e).hom =
      (scalarReductionDerivedExtension C.l E Y.obj.left m).map e.inv ≫
        (coefficientFiniteReductionModel C.l E Y.obj.left P.obj P.property.1 m).hom := by
  have hi : inv (DerivedCategory.Q.map (𝟙 P.obj)) = 𝟙 _ := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [DerivedCategory.Q.map_id, Category.id_comp]
  have hmi : (scalarReductionDerivedExtension C.l E Y.obj.left m).map
      (inv (DerivedCategory.Q.map (𝟙 P.obj))) = 𝟙 _ := by
    rw [hi]
    exact (scalarReductionDerivedExtension C.l E Y.obj.left m).map_id _
  have hx : DerivedCategory.Qh.map
      (((scalarReductionExtension C.l E Y.obj.left m).mapHomotopyCategoryFactors
        (.up ℤ)).hom.app P.obj) = 𝟙 _ := by
    dsimp only [Functor.mapHomotopyCategoryFactors]
    rw [Quotient.lift.isLift_hom]
    exact DerivedCategory.Qh.map_id _
  unfold sixFunctorIntegralReductionModel unrestrictedTowerResolutionIso
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom, asIso_inv,
    Iso.app_hom, Iso.app_inv]
  erw [hmi, Category.id_comp, hx, Category.id_comp]
  unfold coefficientFiniteReductionModel coefficientLocalizedCounitModel
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, asIso_hom,
    Iso.app_hom, Iso.app_inv]
  rfl

private theorem finite_model_hom
    {D : FiniteFieldDatum.{u}} (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E] [FiniteDimensional (Padic C.l) E]
    (m : ℕ) {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (P : CochainComplex (scalarReductionTarget C.l E Y.obj.left m) ℤ) :
    sixFunctorFinitePullbackModel C E m f P =
      (sfIntrinsicPullback (finiteCoefficientRing C.l E (m + 1)) f.hom.left
        ).mapDerivedCategoryFactors.hom.app P ≫
      DerivedCategory.Q.map
        ((NatIso.mapHomologicalComplex (pullbackTensorLevelIntrinsic C.l E f.hom.left m)
          (.up ℤ)).inv.app P) := by
  let := integralOperationsLevelPullback_additive C.l E f.hom.left m
  let := sfIntrinsicPullback_additive (finiteCoefficientRing C.l E (m + 1)) f.hom.left
  let : (coefficientProEtaleModulePullback.{u, u} f.hom.left
      (CommRingCat.of (ULift.{u + 1}
        (Padic.coefficientExtensionRing C.l E (m + 1))))).PreservesZeroMorphisms :=
    inferInstanceAs
      ((integralOperationsLevelPullback.{u, u} C.l E f.hom.left m).PreservesZeroMorphisms)
  exact congrArg (fun α ↦
    (sfIntrinsicPullback (finiteCoefficientRing C.l E (m + 1)) f.hom.left
      ).mapDerivedCategoryFactors.hom.app P ≫
    DerivedCategory.Q.map ((NatIso.mapHomologicalComplex α (.up ℤ)).inv.app P))
    (level_intrinsic_eq C.l E f.hom.left m).symm

end StageModels
end WeilConjectures
namespace WeilConjectures.IntegralProjectionReduction
open IntegralPublishedPullback

open IntegralSystemRealization

variable {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
  {E : Type u} [Field E] [Algebra (Padic C.l) E]
  [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
  (d : SixFunctorOperationDatum D C E n hn) (m : ℕ)

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus scalarReductionExistence scalarReductionDerivedExistence
  sixFunctorIntegralReductionModel sixFunctorFinitePullbackModel
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
attribute [local implicit_reducible] coefficientFiniteDerivedExtension
  coefficientFiniteDerivedRestriction integralOperationsGoodComplex
  integralOperationsGoodLocalization unrestrictedIntegralReductionFunctor
  integralPullbackFiniteComplex

/-- Evaluation of the completed pullback comparison agrees with the prescribed
finite pullback comparison. This is a unary comparison, with no tensor or support map.

Source: fix-prop-projection-formula.proof.md, successive coefficient reductions;
Stacks 07A4, 099N and the K-flat pullback model.
(blueprint: lem-sf-integral-projection-pull-evaluation).

Proof: choose a flat-term K-flat representative P of L. Compute the published
pullbackTensorIntegralPullbackModel directly on P. Its Roos normalization determines
the projection to each finite level, and naturality extends the K-injective calculation
to every tower. Expanding pullReduction gives reduction of that model comparison
followed by the actual reconstruction counit. Evaluate the counit using the calculus's
counit_projection equation. The whole-system reductionPull model is fixed on the
strict quotient word, and pullbackTensorDerivedEvaluation is fixed on that same word.
Consequently this evaluated composite is integralPullbackFiniteComparison on P.
The pullProjection field of d.integralNormalization identifies that comparison with
its directAdjunction.left followed by finitePullback and the representative
identifications. Cancel the common finitePullback and representative isomorphisms.
The full finite-Tor inclusion leaves every arrow unchanged, giving the stated form
with pullIso. K-flat localization extends the equality to L, including zero inputs;
no flatness of the quotient itself is assumed, including at m=0. -/
theorem integralProjectionPullEvaluation
    (hl : IsUnit (C.l : D.k)) (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (L : sfIntegralConstructibleCategory C.l E Y.obj.left) :
    (evaluation (C := C) (E := E) m X).map
        (((calculus C.l E X.obj.left).reduction.mapIso
          (FixProjectionCompactification.Coordinates.pullValue D C E d.higher hl f L) ≪≫
          FixProjectionCompactification.Coordinates.pullReduction D C E o z
            f.hom.left L.obj).hom) ≫
      (evaluatedPull d m f L).hom =
    (reductionEvaluation d m X ((d.higher.integral.pull f).obj L)).hom ≫
      (finiteTorConstructible C.l E (m + 1) (Nat.le_add_left 1 m) X.obj.left).ι.map
        (pullIso d m f L).hom := by
  classical
  let := FixProjectionCompactification.Coordinates.residueUnits hl X
  let := FixProjectionCompactification.Coordinates.residueUnits hl Y
  obtain ⟨P, ⟨e⟩⟩ := goodRepresentative C.l E Y.obj.left L.obj
  have hp := eq_of_heq (d.integralNormalization.pullProjection f L P e m)
  have h := published_counit_finite C.l E f.hom.left L P e m
  have hi : IsIso (sixFunctorFinitePullbackModel C E m f
      (unrestrictedTowerFiniteComplex C.l E Y.obj.left m P.obj)) := by
    rw [finite_model_hom]
    infer_instance
  dsimp only [evaluatedPull, pullIso, FixProjectionCompactification.Coordinates.pullValue,
    Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.symm_hom, eqToIso.hom]
  change _ = (reductionEvaluation d m X ((d.higher.integral.pull f).obj L)).hom ≫
    (intrinsicFiniteTorsionConstructible C.l E (m + 1)
      (Nat.le_add_left 1 m) X.obj.left).ι.map
      (((d.integralNormalization.reduction m).directAdjunction f).left.hom.app L)
  apply (cancel_mono (((stage d m).finitePullback f).hom.app ((reduction d m Y).obj L) ≫
    (sixFunctorFinitePullback D C E (m + 1) (Nat.le_add_left 1 m) f).map
      (sixFunctorIntegralReductionModel C E m Y L P e).hom ≫
    sixFunctorFinitePullbackModel C E m f
      (unrestrictedTowerFiniteComplex C.l E Y.obj.left m P.obj))).1
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [hp]
  dsimp only [FixProjectionCompactification.Coordinates.pullReduction,
    Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  simp only [finite_model_hom, reduction_model_hom, Functor.map_comp, Category.assoc]
  have h' := congrArg (fun a ↦
    ((calculus C.l E X.obj.left).reductionEvaluation m).hom.app
      ((integralDerivedPullback C.l E f.hom.left).obj L.obj) ≫ a) h
  simp only [Iso.hom_inv_id_app_assoc, Functor.map_comp, Category.assoc] at h'
  erw [h']
  have he := ((calculus C.l E X.obj.left).reductionEvaluation m).hom.naturality
    (eqToHom (congrArg (fun F ↦ (F.obj L).obj) (d.higher.integralPullback f)))
  exact (reassoc_of% he) _

end WeilConjectures.IntegralProjectionReduction
