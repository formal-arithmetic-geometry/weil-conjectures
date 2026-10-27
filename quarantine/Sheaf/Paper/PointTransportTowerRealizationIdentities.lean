/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G6
-/
module

public import Sheaf.Paper.PointTransportConeComparisonDescent
import all Sheaf.Paper.PointTransportConeComparisonDescent
import all Sheaf.Paper.PointPullbackConeLocalization
import all Sheaf.Paper.PointQuotientAugmentationDiagram

/-! # Explicit projection and derived comparison for the point quotient cone
Source: blueprint rational Frobenius integral model, clause (3)
(blueprint: lem-trf-integral-point-transport-tower-realization).
These proved private helpers keep the normalized cone comparison as a named map
while expanding its derived factors only once.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- This module intentionally exports only proved helpers through import all.
set_option linter.privateModule false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local irreducible] CategoryTheory.Limits.limit
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory.Q
  integralDerivedPullback integralDerivedPullbackComparison
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  unrestrictedTowerUnit unrestrictedIntegralTransition
  inverseImageReductionTheta integralOperationsRoosMap
  PointTransportCone.augmentation PointTransportCone.sectionsFactors
  PointTransportCone.representativeComparison PointTransportCone.coneSections
  CochainComplex.mappingCocone towerTransitionEndomorphism
attribute [local implicit_reducible] PointTransportCone.sections PointTransportCone.moduleQ
  PointTransportCone.reductionTower PointTransportCone.pullbackTower
  PointTransportCone.reductionTowers PointTransportCone.pullbackTowers
  integralTowerHasDerivedCategory integralOperationsCommHasDerivedCategory
  integralCompletedRingHasDerivedCategory integralOperationsPullbackTowerFunctor
  integralOperationsPullbackComplexFunctor integralOperationsRoosFunctor
  integralOperationsRoos integralOperationsTowerStep Functor.ofOpSequence Functor.ofSequence
  Functor.mapHomologicalComplex

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem pointReductionAugmentation_zeroShift
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (i : ℤ) :
    (PointTransportCone.augmentation D l E P).f i ≫
      (CochainComplex.mappingCocone.snd
        (PointTransportCone.reductionEnd D l E P)).v i (i - 1) (by omega) = 0 := by
  simpa only [PointTransportCone.augmentation,
    CochainComplex.HomComplex.Cochain.zero_v] using!
    CochainComplex.mappingCocone.lift_f_snd_v
      (PointTransportCone.reductionEnd D l E P)
      (PointTransportCone.reductionProduct D l E P) 0
      (PointTransportCone.augmentation_condition D l E P) i (i - 1) (by omega)

private instance realizationIdentitySectionsProducts :
    PreservesLimitsOfShape (Discrete ℕ) (pointIntegralSections l E D.k) :=
  PointQuotientAugmentation.sectionsProducts l E D.k

private theorem pointTransportTowerRealization_identity (hl : l ≠ D.p)
    (P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory)
    (v : (PointTransportCone.reductionTowers D l E).obj P.obj ⟶
      (PointTransportCone.pullbackTowers D l E).obj P.obj)
    (hv : ∀ n : ℕ, frobeniusPointIntegralSigma D l E P.obj ≫
      (PointTransportCone.sections D l E).map
        (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj) =
      PointTransportCone.reductionUnit D l E P.obj n ≫ v.app (op n)) :
    frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj P.obj) ≫
      (pointFibreIntegralAmbient D l E).map
        ((integralDerivedPullbackComparison l E (frobeniusPointIso D).hom).hom.app P) ≫
      (PointTransportCone.sectionsFactors D l E).hom.app
        ((integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom).obj P.obj) ≫
      (PointTransportCone.moduleQ l E).map
        ((PointQuotientAugmentation.roosComparison (pointIntegralSections l E D.k)).hom.app
          ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P.obj)) =
    (PointTransportCone.sectionsFactors D l E).hom.app P.obj ≫
      (PointTransportCone.moduleQ l E).map (PointTransportCone.augmentation D l E P.obj) ≫
      (PointTransportCone.moduleQ l E).map (integralOperationsRoosMap v) := by
  simpa only [PointTransportCone.targetComparison,
    PointPullbackCone.targetComparison, PointTransportCone.sourceComparison,
    PointTransportCone.sectionsFactors, PointPullbackCone.sectionsFactors,
    PointPullbackCone.roosComparison, PointTransportCone.coneArrow,
    PointTransportCone.moduleQ, Iso.trans_hom, Iso.app_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.map_comp,
    Category.assoc] using!
      PointTransportCone.normalized_identity D l E hl P v hv

end WeilConjectures
