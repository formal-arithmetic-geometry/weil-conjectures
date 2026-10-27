/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q14
-/
module

public import Sheaf.SixFunctors.FrobeniusPointTransport
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.AdicCoefficientDatum
public import Sheaf.Paper.PointTransportTowerRealizationSpec
import Sheaf.Paper.PointTransportStrictQuotientAllComplexes
import Sheaf.Paper.PointReductionAugmentationComplete
import all Sheaf.Paper.PointTransportConeComparisonDescent
import all Sheaf.Paper.PointTransportTowerRealizationIdentities
import all Sheaf.Paper.PointTransportTowerRealizationConstruction
import all Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
import all Sheaf.Paper.PointQuotientAugmentationDiagram

/-! # Assembly of the normalized point transport realization
Source: blueprint rational Frobenius integral model, clause (3)
(blueprint: lem-trf-integral-point-transport-tower-realization).
The proof is complete from the two stated coefficient sublemmas and the existing
normalized cone comparison. This module uses the named canonical tower interfaces.
-/

@[expose] public noncomputable section
set_option autoImplicit false
-- The assembly is a proved private helper for the original public statement.
set_option linter.privateModule false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures
variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local instance 5000] integralTowerHasDerivedCategory
attribute [local irreducible] CategoryTheory.Limits.limit
  completedIntegralCoefficientSheafUnrestricted completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions DerivedCategory.Q
  integralDerivedPullback integralDerivedPullbackComparison
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  unrestrictedTowerUnit unrestrictedIntegralTransition strictQuotientPointMap
  inverseImageReductionTheta integralOperationsRoosMap
  PointTransportCone.augmentation PointTransportCone.sectionsFactors
  CochainComplex.mappingCocone towerTransitionEndomorphism realizationTowerMap
attribute [local implicit_reducible] PointTransportCone.sections PointTransportCone.moduleQ
  PointTransportCone.reductionTower PointTransportCone.pullbackTower
  PointTransportCone.reductionTowers PointTransportCone.pullbackTowers
  integralTowerHasDerivedCategory integralOperationsCommHasDerivedCategory
  integralCompletedRingHasDerivedCategory integralOperationsPullbackTowerFunctor
  integralOperationsPullbackComplexFunctor integralOperationsRoosFunctor
  integralOperationsRoos integralOperationsTowerStep Functor.ofOpSequence Functor.ofSequence
  Functor.mapHomologicalComplex PointTransportCone.reductionEnd
  trfPointTargetEnd trfPointTargetTower trfPointSheafTargetEnd

private instance assemblySectionsProducts :
    PreservesLimitsOfShape (Discrete ℕ) (pointIntegralSections l E D.k) :=
  PointQuotientAugmentation.sectionsProducts l E D.k

private theorem canonicalPointTransportTowerRealization (hl : l ≠ D.p) :
    pointTransportTowerRealizationSpec D l E hl := by
  unfold pointTransportTowerRealizationSpec
  let U := realizationTowerMap D l E hl
  let α := realizationAlpha D l E
  let β := realizationBeta D l E
  refine ⟨U, α, β, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P n i x
    rw [show (U.app P).app (op n) = strictQuotientPointMap D l E n P from
      realizationTowerMap_app D l E hl P n]
    exact (pointTransport_strictQuotient_allComplexes D l E hl).2.2 P n i x
  · intro P i n x
    have h := PointTransportCone.augmentation_first D l E P n i
    have hr := unrestrictedTowerUnit_condition l E (Spec (.of D.k)) P n i
      (op (ProEt.mk (𝟙 (Spec (.of D.k))))) x
    change (((α.app P).f i ≫ CompletedStalk.roosFirst
      ((PointTransportCone.reductionTowers D l E).obj P) n i).hom x) = _
    rw [show (α.app P).f i ≫ CompletedStalk.roosFirst
      ((PointTransportCone.reductionTowers D l E).obj P) n i =
      (PointTransportCone.reductionUnit D l E P n).f i from h]
    exact hr
  · intro P i
    exact pointReductionAugmentation_zeroShift D l E P i
  · intro P i n
    simpa only [trfPointTargetEnd, trfPointTargetTower, trfPointSheafTargetEnd] using!
      (PointQuotientAugmentation.roosComparison_coordinates
        (pointIntegralSections l E D.k)).1
        ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P) n i
  · intro P i n
    simpa only [β, realizationBeta, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, trfPointTargetEnd, trfPointTargetTower, trfPointSheafTargetEnd,
      integralOperationsTowerStep, sub_eq_add_neg] using!
      (PointQuotientAugmentation.roosComparison_coordinates
        (pointIntegralSections l E D.k)).2
        ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P) n i
  · intro P hP
    refine ⟨pointReductionAugmentation_isIso D l E hl P hP, ?_⟩
    have hv (n : ℕ) : frobeniusPointIntegralSigma D l E P.obj ≫
        (PointTransportCone.sections D l E).map
          (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P.obj) =
        PointTransportCone.reductionUnit D l E P.obj n ≫ (U.app P.obj).app (op n) :=
      by
        rw [show (U.app P.obj).app (op n) = strictQuotientPointMap D l E n P.obj from
          realizationTowerMap_app D l E hl P.obj n]
        exact ((pointTransport_strictQuotient D l E hl).2.2.1 P n).symm
    simpa only [β, realizationBeta, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, α, realizationAlpha] using!
        pointTransportTowerRealization_identity D l E hl P (U.app P.obj) hv
  · intro N N' f
    simpa only [Functor.comp_map, PointTransportCone.transportNatural_app] using
      (PointTransportCone.transportNatural D l E hl).naturality f.hom


end WeilConjectures
