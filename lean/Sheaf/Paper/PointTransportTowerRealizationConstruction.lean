/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G6
-/
module

public import Sheaf.Paper.PointTransportConeComparisonDescent
public import Sheaf.Paper.PointTransportStrictQuotientAllComplexes
import all Sheaf.Paper.PointTransportConeComparisonDescent
import all Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted
import all Sheaf.Paper.PointQuotientAugmentationDiagram

/-! # Strict point towers and their normalized augmentation
Source: blueprint rational Frobenius integral model, clause (3), steps 1--3
(blueprint: lem-trf-integral-point-transport-tower-realization).
These private constructions use the existing named canonical tower presentations.
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
  unrestrictedTowerUnit unrestrictedIntegralTransition strictQuotientPointMap
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

private instance constructionSectionsProducts :
    PreservesLimitsOfShape (Discrete ℕ) (pointIntegralSections l E D.k) :=
  PointQuotientAugmentation.sectionsProducts l E D.k

private def realizationTowerMap (hl : l ≠ D.p) :
    PointTransportCone.reductionTowers D l E ⟶ PointTransportCone.pullbackTowers D l E where
  app P := NatTrans.ofOpSequence (fun n ↦ strictQuotientPointMap D l E n P) (by
    intro n
    simpa only [PointTransportCone.reductionTowers, PointTransportCone.reductionTower,
      PointTransportCone.pullbackTowers, PointTransportCone.pullbackTower,
      PointTransportCone.sections, Functor.comp_obj, Functor.comp_map,
      Functor.whiskeringRight_obj_obj,
      Functor.flip_obj_map, Functor.flip_obj_obj, Functor.ofOpSequence_obj,
      integralOperationsPullbackTowerFunctor,
      Functor.ofOpSequence_map_homOfLE_succ] using!
        (pointTransport_strictQuotient_allComplexes D l E hl).1 P n)
  naturality P Q f := by
    apply NatTrans.ext
    funext n
    exact (pointTransport_strictQuotient_allComplexes D l E hl).2.1 P Q f n.unop

private theorem realizationTowerMap_app (hl : l ≠ D.p)
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ) :
    ((realizationTowerMap D l E hl).app P).app (op n) =
      strictQuotientPointMap D l E n P := rfl

attribute [local irreducible] realizationTowerMap

private theorem realizationAugmentation_naturality
    {P Q : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ} (f : P ⟶ Q) :
    (PointTransportCone.sections D l E).map f ≫ PointTransportCone.augmentation D l E Q =
      PointTransportCone.augmentation D l E P ≫
        integralOperationsRoosMap ((PointTransportCone.reductionTowers D l E).map f) := by
  change ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map f ≫
      PointTransportCone.augmentation D l E Q =
    PointTransportCone.augmentation D l E P ≫
      integralOperationsRoosMap ((PointTransportCone.reductionTowers D l E).map f)
  apply PointTransportCone.roos_ext ((PointTransportCone.reductionTowers D l E).obj Q)
  · intro n i
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [PointTransportCone.augmentation_first, PointTransportCone.roosMap_first,
      ← Category.assoc, PointTransportCone.augmentation_first]
    have h := congrArg ((PointTransportCone.sections D l E).map)
      (towerUnit_naturality l E (Spec (.of D.k)) n f)
    simpa only [Functor.map_comp, PointTransportCone.reductionUnit,
      PointTransportCone.sections, HomologicalComplex.comp_f] using! congrArg (fun z ↦ z.f i) h
  · intro n i
    simp only [HomologicalComplex.comp_f, Category.assoc]
    rw [PointTransportCone.augmentation_second, PointTransportCone.roosMap_second,
      ← Category.assoc, PointTransportCone.augmentation_second, zero_comp, comp_zero]

private def realizationAlpha : PointTransportCone.sections D l E ⟶
    PointTransportCone.reductionTowers D l E ⋙ integralOperationsRoosFunctor where
  app P := PointTransportCone.augmentation D l E P
  naturality _ _ f := realizationAugmentation_naturality D l E f

private def realizationBeta :
    integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom ⋙
        PointTransportCone.sections D l E ≅
      PointTransportCone.pullbackTowers D l E ⋙ integralOperationsRoosFunctor :=
  Functor.isoWhiskerLeft
    (integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom)
    (PointQuotientAugmentation.roosComparison (pointIntegralSections l E D.k))

end WeilConjectures
