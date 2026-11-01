/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.TraceFormula.Integral.IntegralComparisonRealizationModels
import all WeilConjectures.SmoothPurity.Integral.IntegralOperationsWellDefinedSupplement
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # The finite component of a strict normalized pullback comparison

Source: Stacks Tags 03D3, 099N(5), and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Replaying sectionwise transport proofs for tactic linting is expensive.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] HasDerivedCategory.standard
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.mapDerivedCategoryFactors
  CategoryTheory.Functor.mapDerivedCategoryCompIso
  CategoryTheory.Functor.mapDerivedCategoryNatIso
attribute [local implicit_reducible] WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.integralCoefficientSheaf
  WeilConjectures.integralCoefficientCommRingSheaf
attribute [local implicit_reducible] WeilConjectures.coefficientFiniteDerivedExtension
  WeilConjectures.coefficientFiniteDerivedRestriction
  WeilConjectures.coefficientConstantTowerEvaluation
  CategoryTheory.Functor.mapHomologicalComplex
  CategoryTheory.Functor.ofOpSequence CategoryTheory.Functor.ofSequence
  CategoryTheory.NatIso.mapHomologicalComplex CategoryTheory.NatTrans.mapHomologicalComplex
  HomologicalComplex.asFunctor
  HomologicalComplex.complexOfFunctorsToFunctorToComplex
attribute [local irreducible] CategoryTheory.constantSheaf CategoryTheory.presheafToSheaf
open CategoryTheory CategoryTheory.Limits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Exact evaluation after scalar restriction, computed on a complex of strict systems.
Source: Stacks 0941 (blueprint: lem-pod-integral-pullback-strict-finite-component). -/
@[irreducible] def integralComparisonRestrictedEvaluationFactors (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    (coefficientFiniteDerivedRestriction l E W n).obj
        ((coefficientSequenceDerivedEvaluation l E W n).obj (DerivedCategory.Q.obj C)) ≅
      DerivedCategory.Q.obj
        ((((coefficientSequenceRestriction l E W).mapHomologicalComplex
          (.up ℤ)).obj C).asFunctor.obj (op n)) :=
  ((coefficientRestrictedEvaluationIso l E W n).app (DerivedCategory.Q.obj C)).symm ≪≫
    (coefficientConstantTowerEvaluation l E W n).mapIso
      ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app C) ≪≫
    (coefficientConstantTowerEvaluationFactors l E W n).app
      (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)

section Proof
attribute [local irreducible] unrestrictedIntegralReductionFunctor scalarReductionExtension
attribute [local instance] scalarReductionRestrictionLimits scalarReductionRestrictionColimits
attribute [local irreducible] coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict
  integralOperationsLevelPullback coefficientProEtaleModuleDirectImage
  scalarReductionDerivedRestriction
  integralComparisonSequenceDirectImage
  integralComparisonSequenceGenerator

private theorem restrictedFactors_fac (W : Scheme.{u})
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    (integralComparisonRestrictedEvaluationFactors l E W C n).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom
            (.up ℤ)).app C) =
      (coefficientFiniteDerivedRestriction l E W n).map
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C) ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C) := by
  have h := exactSquare_fac
    (coefficientSequenceRestriction l E W)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))
    (coefficientSequenceEvaluation l E W n) (scalarReductionRestriction l E W n)
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) C
  change (coefficientRestrictedEvaluationIso l E W n).hom.app
      (DerivedCategory.Q.obj C) ≫ _ = _ at h
  unfold integralComparisonRestrictedEvaluationFactors
  change ((coefficientRestrictedEvaluationIso l E W n).inv.app (DerivedCategory.Q.obj C) ≫
      ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)).mapDerivedCategory.map
        ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app C) ≫
      ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)).mapDerivedCategoryFactors.hom.app
        (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C)) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom (.up ℤ)).app C) = _
  simp only [Category.assoc]
  rw [← h]
  simp only [Iso.inv_hom_id_app_assoc]
  rfl

private theorem restrictedFactors_square (W : Scheme.{u}) (n : ℕ)
    (D : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (A T : CochainComplex (normalizedDVRModules l E W n) ℤ)
    (q : (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj
      D).asFunctor.obj (op n) ⟶
        ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).obj A)
    (b : A ⟶ T)
    (c : ((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D ⟶ T)
    (h : q ≫ ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map b =
      (NatTrans.mapHomologicalComplex
        (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom (.up ℤ)).app D ≫
      ((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map c) :
    (integralComparisonRestrictedEvaluationFactors l E W D n).hom ≫
      DerivedCategory.Q.map q ≫
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.inv.app A ≫
      (coefficientFiniteDerivedRestriction l E W n).map (DerivedCategory.Q.map b) ≫
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app T =
    (coefficientFiniteDerivedRestriction l E W n).map
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app D) ≫
      (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
        (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj D) ≫
      DerivedCategory.Q.map
        (((scalarReductionRestriction l E W n).mapHomologicalComplex (.up ℤ)).map c) := by
  erw [(scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.naturality b]
  erw [Iso.inv_hom_id_app_assoc]
  dsimp only [Functor.comp_map]
  erw [← DerivedCategory.Q.map_comp, h, DerivedCategory.Q.map_comp]
  erw [← Category.assoc, restrictedFactors_fac l E W D n]
  simp only [Category.assoc]

private theorem map_iso_cancel_assoc {A B : Type*} [Category A] [Category B]
    (F : A ⥤ B) {X Y Z : A} (f : X ⟶ Y) (e : Z ≅ Y)
    {T : B} (h : F.obj Y ⟶ T) :
    F.map (f ≫ e.inv) ≫ F.map e.hom ≫ h = F.map f ≫ h := by
  rw [← F.map_comp_assoc, Category.assoc, e.inv_hom_id, Category.comp_id]

end Proof

attribute [local irreducible] unrestrictedIntegralReductionFunctor scalarReductionExtension
attribute [local irreducible] coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted
attribute [local implicit_reducible] integralOperationsPullbackTowerFunctor
  integralOperationsPullbackLevel integralOperationsRestrict
  integralOperationsLevelPullback coefficientProEtaleModuleDirectImage
  scalarReductionDerivedRestriction
  integralComparisonSequenceDirectImage
  integralComparisonSequenceGenerator

/-- The finite component of a strict tower comparison is fixed by its values on
inverse-image unit generators. This is a statement about the strict comparison q;
it has no integral realization or reduction/limit counit as an input.
Source: Stacks 03D3 (inverse-image adjunction), 099N(5), and 0941;
step 1 of lem-pod-integral-pullback-counit-projection.
(blueprint: lem-pod-integral-pullback-strict-finite-component).

Proof: evaluate the system inverse-image unit at level n. The defining property of
finiteSystemPullbackEvaluation identifies it with the ordinary finite inverse-image
unit. The defining property of integralFinitePullbackModel identifies the other
presentation with this same unit. After transporting by kappa, the hypothesis says
that both maps have the same values on these unit sections. The completed-to-finite
coefficient projection is locally surjective; thus completed-linear maps between
these restricted quotient modules are already quotient-linear. The inverse-image
adjunction, or equivalently its locally generating unit sections and scalar multiples,
therefore makes the two maps equal in every degree. The degreewise equalities commute
with the differentials. Apply Q, and use the exact-functor factorization comparisons
for restriction, evaluation and inverse image. This gives precisely the displayed
identity. The proof uses no flatness of a transition map, no effectivity, and no
invertibility of a derived reduction counit. It also covers zero complexes, empty
schemes, and n=0, where the coefficient exponent is one. -/
theorem integralPullbackStrictFiniteComponent {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (scalarReductionSource l E Y) ℤ)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (κ : ∀ n : ℕ,
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
        (unrestrictedIntegralFiniteComplex l E Y n).obj P)
    (q : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex
          (.up ℤ)).obj C)).asFunctor ≅
      (integralOperationsPullbackTowerFunctor l E f).obj P)
    (hq : ∀ (n : ℕ) (i : ℤ) (U : Y.ProEt)
        (x : (C.X i).val.obj (op (n, U))),
      ((q.hom.app (op n)).f i).val.app (op ((proEtaleBaseChange f).obj U))
        (integralComparisonRestrictedSection l E X
          ((integralComparisonSequencePullback l E f).obj (C.X i)) n
          (op ((proEtaleBaseChange f).obj U))
          (integralComparisonSequenceGenerator l E f (C.X i) n U x)) =
        integralOperationsPullbackGenerator l E f n
          (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) U
          (((κ n).hom.f i).val.app (op U)
            (coefficientEvaluationSection l E Y (C.X i) n (op U) x))) (n : ℕ) :
    (integralComparisonRestrictedEvaluationFactors l E X
      (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C)
      n).hom ≫
      DerivedCategory.Q.map (q.hom.app (op n)) ≫
      (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.inv.app
        (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj
          ((unrestrictedIntegralFiniteComplex l E Y n).obj P)) ≫
      (coefficientFiniteDerivedRestriction l E X n).map
        (DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n)
            (.up ℤ)).hom.app ((unrestrictedIntegralFiniteComplex l E Y n).obj P)) ≫
          (proEtaleConstantRingPullback
            (Padic.coefficientExtensionRing l E (n + 1)) f).mapDerivedCategoryFactors.inv.app
            ((unrestrictedIntegralFiniteComplex l E Y n).obj P)) =
    (coefficientFiniteDerivedRestriction l E X n).map
      ((coefficientSequenceDerivedEvaluation l E X n).map
          ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.inv.app C) ≫
        (finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
          (integralSystemTransition l E) f n).hom.app (DerivedCategory.Q.obj C) ≫
        (proEtaleConstantRingDerivedPullback
          (Padic.coefficientExtensionRing l E (n + 1)) f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C ≫
            DerivedCategory.Q.map (κ n).hom)) := by
  have := finiteEvaluation_zero l E f n
  let R := scalarReductionRestriction l E X n
  let B := proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f
  let V := coefficientSequenceEvaluation l E X n
  let F := integralComparisonSequencePullback l E f
  let Pn := (unrestrictedIntegralFiniteComplex l E Y n).obj P
  let D := (F.mapHomologicalComplex (.up ℤ)).obj C
  let qn : (((coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ)).obj
        D).asFunctor.obj (op n) ⟶ (R.mapHomologicalComplex (.up ℤ)).obj
          (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj Pn) :=
      q.hom.app (op n)
  let H : ((coefficientSequenceEvaluation l E X n).mapHomologicalComplex (.up ℤ)).obj D ⟶
      (B.mapHomologicalComplex (.up ℤ)).obj
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C) :=
      (NatTrans.mapHomologicalComplex (finiteEvaluation l E f n).hom (.up ℤ)).app C
  let γ := NatIso.mapHomologicalComplex (integralFinitePullbackModel l E f n) (.up ℤ)
  have hc := strictComponent_complex l E f P C κ q hq n
  let RD := coefficientFiniteDerivedRestriction l E X n
  let VD := coefficientSequenceDerivedEvaluation l E X n
  let BD := proEtaleConstantRingDerivedPullback
    (Padic.coefficientExtensionRing l E (n + 1)) f
  let β : F.mapDerivedCategory ⋙ VD ≅
      (coefficientSequenceEvaluation l E Y n).mapDerivedCategory ⋙ BD :=
    finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
      (integralSystemTransition l E) f n
  have hfinite := finiteEvaluation_fac_comp l E f C n Pn (κ n).hom
  have hl :
      (integralComparisonRestrictedEvaluationFactors l E X D n).hom ≫
        DerivedCategory.Q.map qn ≫
        R.mapDerivedCategoryFactors.inv.app
          (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj Pn) ≫
        RD.map (DerivedCategory.Q.map (γ.hom.app Pn) ≫
          B.mapDerivedCategoryFactors.inv.app Pn) ≫
        RD.map (B.mapDerivedCategoryFactors.hom.app Pn) ≫
        R.mapDerivedCategoryFactors.hom.app
          ((B.mapHomologicalComplex (.up ℤ)).obj Pn) =
      RD.map (V.mapDerivedCategoryFactors.hom.app D) ≫
        R.mapDerivedCategoryFactors.hom.app
          ((V.mapHomologicalComplex (.up ℤ)).obj D) ≫
        DerivedCategory.Q.map
          ((R.mapHomologicalComplex (.up ℤ)).map
            (H ≫ (B.mapHomologicalComplex (.up ℤ)).map (κ n).hom)) := by
    erw [map_iso_cancel_assoc RD (DerivedCategory.Q.map (γ.hom.app Pn))
      (B.mapDerivedCategoryFactors.app Pn)]
    exact restrictedFactors_square l E X n D
      (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj Pn)
      ((B.mapHomologicalComplex (.up ℤ)).obj Pn) qn (γ.hom.app Pn)
      (H ≫ (B.mapHomologicalComplex (.up ℤ)).map (κ n).hom) hc
  apply (cancel_mono (RD.map (B.mapDerivedCategoryFactors.hom.app Pn) ≫
    R.mapDerivedCategoryFactors.hom.app ((B.mapHomologicalComplex (.up ℤ)).obj Pn))).1
  change ((integralComparisonRestrictedEvaluationFactors l E X D n).hom ≫
    DerivedCategory.Q.map qn ≫
    R.mapDerivedCategoryFactors.inv.app
      (((integralOperationsLevelPullback l E f n).mapHomologicalComplex (.up ℤ)).obj Pn) ≫
    RD.map (DerivedCategory.Q.map (γ.hom.app Pn) ≫ B.mapDerivedCategoryFactors.inv.app Pn)) ≫
    (RD.map (B.mapDerivedCategoryFactors.hom.app Pn) ≫
      R.mapDerivedCategoryFactors.hom.app ((B.mapHomologicalComplex (.up ℤ)).obj Pn)) =
    RD.map (VD.map (F.mapDerivedCategoryFactors.inv.app C) ≫
      β.hom.app (DerivedCategory.Q.obj C) ≫
      BD.map ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C ≫
        DerivedCategory.Q.map (κ n).hom)) ≫
      (RD.map (B.mapDerivedCategoryFactors.hom.app Pn) ≫
        R.mapDerivedCategoryFactors.hom.app ((B.mapHomologicalComplex (.up ℤ)).obj Pn))
  simp only [Category.assoc]
  erw [hl]
  erw [← RD.map_comp_assoc]
  simp only [Category.assoc]
  erw [hfinite]
  rw [RD.map_comp]
  simp only [Category.assoc]
  have hn := R.mapDerivedCategoryFactors.hom.naturality
    (H ≫ (B.mapHomologicalComplex (.up ℤ)).map (κ n).hom)
  dsimp only [Functor.comp_map] at hn
  erw [hn]

end WeilConjectures
