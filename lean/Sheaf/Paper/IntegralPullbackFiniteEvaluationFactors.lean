/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
import all Sheaf.Paper.IntegralPullbackStrictFiniteGenerators

/-! # Exact finite evaluation on arbitrary complex maps

Source: Stacks Tag 015F.
(blueprint: lem-pod-integral-pullback-finite-evaluation-factors).
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- Internal proved comparison calculations, consumed with `import all`.
set_option linter.privateModule false
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

section Proof
attribute [local instance 30000] zeroOfFiniteLimits
attribute [local instance 50] additiveOfFiniteLimits
attribute [local instance]
  finitePullback_limits finitePullback_colimits nativeFinitePullback_limits
  nativeFinitePullback_colimits mixedFinitePullback_limits mixedFinitePullback_colimits
attribute [local irreducible] restrictionEvaluation finiteEvaluation strictLevel
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

private theorem finiteEvaluation_fac {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (n : ℕ) :
    (finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
        (integralSystemTransition l E) f n).hom.app (DerivedCategory.Q.obj C) ≫
      (proEtaleConstantRingDerivedPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).map
          ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C) ≫
      (proEtaleConstantRingPullback
        (Padic.coefficientExtensionRing l E (n + 1)) f).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C) =
    (coefficientSequenceDerivedEvaluation l E X n).map
        ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.hom.app C) ≫
      (coefficientSequenceEvaluation l E X n).mapDerivedCategoryFactors.hom.app
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (finiteEvaluation l E f n).hom (.up ℤ)).app C) := by
  have hb : finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
      (integralSystemTransition l E) f n =
      (Functor.mapDerivedCategoryCompIso (integralComparisonSequencePullback l E f)
        (coefficientSequenceEvaluation l E X n)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (finiteEvaluation l E f n) ≪≫
      Functor.mapDerivedCategoryCompIso (coefficientSequenceEvaluation l E Y n)
        (proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f) := by
    unfold finiteSystemDerivedPullbackEvaluation finiteEvaluation
    rfl
  rw [hb]
  exact exactSquare_fac
    (integralComparisonSequencePullback l E f) (coefficientSequenceEvaluation l E X n)
    (coefficientSequenceEvaluation l E Y n)
    (proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f)
    (finiteEvaluation l E f n) C


/-- The derived finite evaluation comparison, followed by an arbitrary map of finite
complexes, is computed by the ordinary evaluation comparison and the exact factors.
Source: Stacks Tag 015F; exact localization composition and naturality.
(blueprint: lem-pod-integral-pullback-finite-evaluation-factors).

Proof: the derived finite evaluation comparison is the composition of the inverse
factorization compositor, the derived ordinary evaluation isomorphism, and the other
compositor. Their factorization identities compute its value on Q(C). Naturality of
the finite pullback factor moves Q(k) across that factor. The inverse and forward
sequence pullback factors cancel, leaving Q of the ordinary comparison followed by
finite pullback of k. The argument applies to every finite target complex and every
chain map k, including zero maps, and uses neither a resolution nor flatness. -/
private theorem finiteEvaluation_fac_comp {X Y : Scheme.{u}} (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (n : ℕ)
    (N : CochainComplex (normalizedDVRModules l E Y n) ℤ)
    (k : ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ⟶ N) :
  letI := finiteEvaluation_zero l E f n
  let B : normalizedDVRModules l E Y n ⥤ normalizedDVRModules l E X n :=
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f
  let V := coefficientSequenceEvaluation l E X n
  let F := integralComparisonSequencePullback l E f
  let D := (F.mapHomologicalComplex (.up ℤ)).obj C
  let H : (V.mapHomologicalComplex (.up ℤ)).obj D ⟶
      (B.mapHomologicalComplex (.up ℤ)).obj
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C) :=
      (NatTrans.mapHomologicalComplex (finiteEvaluation l E f n).hom (.up ℤ)).app C
  let VD := coefficientSequenceDerivedEvaluation l E X n
  let BD := proEtaleConstantRingDerivedPullback
    (Padic.coefficientExtensionRing l E (n + 1)) f
  let β : F.mapDerivedCategory ⋙ VD ≅
      (coefficientSequenceEvaluation l E Y n).mapDerivedCategory ⋙ BD :=
    finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
      (integralSystemTransition l E) f n
  VD.map (F.mapDerivedCategoryFactors.inv.app C) ≫
    β.hom.app (DerivedCategory.Q.obj C) ≫
    BD.map ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C ≫
      DerivedCategory.Q.map k) ≫ B.mapDerivedCategoryFactors.hom.app N =
  V.mapDerivedCategoryFactors.hom.app D ≫
    DerivedCategory.Q.map (H ≫ (B.mapHomologicalComplex (.up ℤ)).map k) := by
  have := finiteEvaluation_zero l E f n
  let B : normalizedDVRModules l E Y n ⥤ normalizedDVRModules l E X n :=
      proEtaleConstantRingPullback (Padic.coefficientExtensionRing l E (n + 1)) f
  let V := coefficientSequenceEvaluation l E X n
  let F := integralComparisonSequencePullback l E f
  let D := (F.mapHomologicalComplex (.up ℤ)).obj C
  let H : (V.mapHomologicalComplex (.up ℤ)).obj D ⟶
      (B.mapHomologicalComplex (.up ℤ)).obj
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C) :=
      (NatTrans.mapHomologicalComplex (finiteEvaluation l E f n).hom (.up ℤ)).app C
  let VD := coefficientSequenceDerivedEvaluation l E X n
  let BD := proEtaleConstantRingDerivedPullback
    (Padic.coefficientExtensionRing l E (n + 1)) f
  let β : F.mapDerivedCategory ⋙ VD ≅
      (coefficientSequenceEvaluation l E Y n).mapDerivedCategory ⋙ BD :=
    finiteSystemDerivedPullbackEvaluation (integralSystemRings l E)
      (integralSystemTransition l E) f n
  dsimp only [BD, proEtaleConstantRingDerivedPullback]
  simp only [Functor.map_comp, Category.assoc]
  erw [B.mapDerivedCategoryFactors.hom.naturality k]
  erw [reassoc_of% (finiteEvaluation_fac l E f C n)]
  dsimp only [Functor.comp_map]
  erw [Category.assoc, Category.assoc]
  change VD.map (F.mapDerivedCategoryFactors.inv.app C) ≫
    VD.map (F.mapDerivedCategoryFactors.hom.app C) ≫
    V.mapDerivedCategoryFactors.hom.app D ≫ DerivedCategory.Q.map H ≫
    DerivedCategory.Q.map ((B.mapHomologicalComplex (.up ℤ)).map k) = _
  rw [← VD.map_comp_assoc, Iso.inv_hom_id_app, VD.map_id, Category.id_comp]

end Proof

end WeilConjectures
