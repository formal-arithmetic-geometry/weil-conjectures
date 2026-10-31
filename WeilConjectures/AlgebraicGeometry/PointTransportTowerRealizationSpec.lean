/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralPointTransportTowerData

/-! # Canonical integral point transport realization property
Source: blueprint rational Frobenius integral model, clause (3)
(blueprint: lem-trf-integral-point-transport-tower-realization).
The explicit predicate names the seven properties of the canonical tower realization.
It introduces no mathematical assumption and contains no proof or chosen witness.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

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
  CochainComplex.mappingCocone towerTransitionEndomorphism
attribute [local implicit_reducible] PointTransportCone.sections PointTransportCone.moduleQ
  PointTransportCone.sectionsFactors PointTransportCone.reductionTowers
  PointTransportCone.pullbackTowers PointTransportCone.reductionEnd
  integralTowerHasDerivedCategory integralOperationsCommHasDerivedCategory
  integralCompletedRingHasDerivedCategory integralOperationsPullbackTowerFunctor
  integralOperationsPullbackComplexFunctor integralOperationsRoosFunctor
  integralOperationsRoos integralOperationsTowerStep Functor.ofOpSequence Functor.ofSequence
  Functor.mapHomologicalComplex trfPointTargetEnd trfPointTargetTower trfPointSheafTargetEnd

/-- The complete canonical realization specification, with the recorded finite formula,
whole augmentation and comparison coordinates, completeness, identity and naturality.
Source: blueprint rational Frobenius integral model, clause (3)
(blueprint: lem-trf-integral-point-transport-tower-realization). -/
def pointTransportTowerRealizationSpec (hl : l ≠ D.p) : Prop :=
    ∃ (U : PointTransportCone.reductionTowers D l E ⟶ PointTransportCone.pullbackTowers D l E)
      (α : PointTransportCone.sections D l E ⟶
        PointTransportCone.reductionTowers D l E ⋙ integralOperationsRoosFunctor)
      (β : integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom ⋙
          PointTransportCone.sections D l E ≅
        PointTransportCone.pullbackTowers D l E ⋙ integralOperationsRoosFunctor),
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (n : ℕ) (i : ℤ)
        (x : (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i).val.obj
          (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        (((U.app P).app (op n)).f i) x =
          ((((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).obj P).X i).val.map
            (proEtaleIsoCommaArrow (frobeniusPointIso D).hom
              (ProEt.mk (𝟙 (Spec (.of D.k))))).op
            (integralOperationsPullbackGenerator l E (frobeniusPointIso D).hom n
              (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i)
              ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
                (ProEt.mk (𝟙 (Spec (.of D.k)))))
              ((((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i).val.map
                (frobeniusPointRestriction D).op x)))) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ) (x : (P.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        ((α.app P).f i ≫ (CochainComplex.mappingCocone.fst
            (PointTransportCone.reductionEnd D l E P)).f i ≫
          (Pi.π (fun n ↦ ((PointTransportCone.reductionTowers D l E).obj P).obj (op n)) n).f i) x =
          unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (P.X i)
            (op (ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (i : ℤ),
        (α.app P).f i ≫ (CochainComplex.mappingCocone.snd
          (PointTransportCone.reductionEnd D l E P)).v i (i - 1) (by omega) = 0) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ),
        (β.hom.app P).f i ≫ (CochainComplex.mappingCocone.fst
            (trfPointTargetEnd D l E P)).f i ≫
          (Pi.π (fun n ↦ ((PointTransportCone.pullbackTowers D l E).obj P).obj (op n)) n).f i =
        ((PointTransportCone.sections D l E).map
          (CochainComplex.mappingCocone.fst (trfPointSheafTargetEnd D l E P) ≫
            Pi.π (fun n ↦
              ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P).obj
                (op n)) n)).f i) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ),
        (β.hom.app P).f i ≫ (CochainComplex.mappingCocone.snd
            (trfPointTargetEnd D l E P)).v i (i - 1) (by omega) ≫
          (Pi.π (fun n ↦
            ((PointTransportCone.pullbackTowers D l E).obj P).obj (op n)) n).f (i - 1) =
        (pointIntegralSections l E D.k).map
          ((CochainComplex.mappingCocone.snd (trfPointSheafTargetEnd D l E P)).v
              i (i - 1) (by omega) ≫
            (Pi.π (fun n ↦
              ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P).obj
                (op n)) n).f (i - 1))) ∧
      (∀ P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory,
        sfIntegralConstructible l E (Spec (.of D.k)) (DerivedCategory.Q.obj P.obj) →
        IsIso ((PointTransportCone.moduleQ l E).map (α.app P.obj)) ∧
          frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj P.obj) ≫
            (pointFibreIntegralAmbient D l E).map
              ((integralDerivedPullbackComparison l E (frobeniusPointIso D).hom).hom.app P) ≫
            (PointTransportCone.sectionsFactors D l E).hom.app
              ((integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom).obj
                P.obj) ≫
            (PointTransportCone.moduleQ l E).map (β.hom.app P.obj) =
          (PointTransportCone.sectionsFactors D l E).hom.app P.obj ≫
            (PointTransportCone.moduleQ l E).map (α.app P.obj) ≫
            (PointTransportCone.moduleQ l E).map (integralOperationsRoosMap (U.app P.obj))) ∧
      (∀ (N N' : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
        (f : N ⟶ N'),
        (pointFibreIntegralAmbient D l E).map f.hom ≫
            frobeniusPointTransportIntegral D l hl E N'.obj =
          frobeniusPointTransportIntegral D l hl E N.obj ≫
            (pointFibreIntegralAmbient D l E).map
              ((integralDerivedPullback l E (frobeniusPointIso D).hom).map f.hom))

section ExpandedStatement
attribute [local instance 4000] trfPointModuleHasDerivedCategory
attribute [local implicit_reducible] trfPointModuleHasDerivedCategory
  trfPointSectionsComplex trfPointSourceTower trfPointSourceEnd

/-- The canonical specification is exactly the original expanded supporting statement.
Source: blueprint rational Frobenius integral model, clause (3)
(blueprint: lem-trf-integral-point-transport-tower-realization).
Proof: unfold the specification, its four source presentation aliases, and the
recorded localization/section comparison. Each direction is the same proposition
with definitionally equal names for those fixed constructions. -/
private theorem pointTransportTowerRealizationSpec_iff_expanded (hl : l ≠ D.p) :
    (∃ (U : trfPointSourceTower D l E ⟶ trfPointTargetTower D l E)
      (α : trfPointSectionsComplex D l E ⟶
        trfPointSourceTower D l E ⋙ integralOperationsRoosFunctor)
      (β : integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom ⋙
          trfPointSectionsComplex D l E ≅
        trfPointTargetTower D l E ⋙ integralOperationsRoosFunctor),
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (n : ℕ) (i : ℤ)
        (x : (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i).val.obj
          (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        (((U.app P).app (op n)).f i) x =
          ((((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).obj P).X i).val.map
            (proEtaleIsoCommaArrow (frobeniusPointIso D).hom
              (ProEt.mk (𝟙 (Spec (.of D.k))))).op
            (integralOperationsPullbackGenerator l E (frobeniusPointIso D).hom n
              (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i)
              ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
                (ProEt.mk (𝟙 (Spec (.of D.k)))))
              ((((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i).val.map
                (frobeniusPointRestriction D).op x)))) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ) (x : (P.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))),
        ((α.app P).f i ≫ (CochainComplex.mappingCocone.fst
            (trfPointSourceEnd D l E P)).f i ≫
          (Pi.π (fun n ↦ ((trfPointSourceTower D l E).obj P).obj (op n)) n).f i) x =
          unrestrictedIntegralTensorSection l E (Spec (.of D.k)) n (P.X i)
            (op (ProEt.mk (𝟙 (Spec (.of D.k))))) 1 x) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (i : ℤ),
        (α.app P).f i ≫ (CochainComplex.mappingCocone.snd
          (trfPointSourceEnd D l E P)).v i (i - 1) (by omega) = 0) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ),
        (β.hom.app P).f i ≫ (CochainComplex.mappingCocone.fst
            (trfPointTargetEnd D l E P)).f i ≫
          (Pi.π (fun n ↦ ((trfPointTargetTower D l E).obj P).obj (op n)) n).f i =
        ((trfPointSectionsComplex D l E).map
          (CochainComplex.mappingCocone.fst (trfPointSheafTargetEnd D l E P) ≫
            Pi.π (fun n ↦
              ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P).obj
                (op n)) n)).f i) ∧
      (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
        (i : ℤ) (n : ℕ),
        (β.hom.app P).f i ≫ (CochainComplex.mappingCocone.snd
            (trfPointTargetEnd D l E P)).v i (i - 1) (by omega) ≫
          (Pi.π (fun n ↦ ((trfPointTargetTower D l E).obj P).obj (op n)) n).f (i - 1) =
        (pointIntegralSections l E D.k).map
          ((CochainComplex.mappingCocone.snd (trfPointSheafTargetEnd D l E P)).v
              i (i - 1) (by omega) ≫
            (Pi.π (fun n ↦
              ((integralOperationsPullbackTowerFunctor l E (frobeniusPointIso D).hom).obj P).obj
                (op n)) n).f (i - 1))) ∧
      (∀ P : (integralOperationsGoodComplex l E (Spec (.of D.k))).FullSubcategory,
        sfIntegralConstructible l E (Spec (.of D.k)) (DerivedCategory.Q.obj P.obj) →
        IsIso (DerivedCategory.Q.map (α.app P.obj)) ∧
          frobeniusPointTransportIntegral D l hl E (DerivedCategory.Q.obj P.obj) ≫
            (pointFibreIntegralAmbient D l E).map
              ((integralDerivedPullbackComparison l E (frobeniusPointIso D).hom).hom.app P) ≫
            (pointIntegralSections l E D.k).mapDerivedCategoryFactors.hom.app
              ((integralOperationsPullbackComplexFunctor l E (frobeniusPointIso D).hom).obj
                P.obj) ≫
            DerivedCategory.Q.map (β.hom.app P.obj) =
          (pointIntegralSections l E D.k).mapDerivedCategoryFactors.hom.app P.obj ≫
            DerivedCategory.Q.map (α.app P.obj) ≫
            DerivedCategory.Q.map (integralOperationsRoosMap (U.app P.obj))) ∧
      (∀ (N N' : sfIntegralConstructibleCategory l E (Spec (.of D.k)))
        (f : N ⟶ N'),
        (pointFibreIntegralAmbient D l E).map f.hom ≫
            frobeniusPointTransportIntegral D l hl E N'.obj =
          frobeniusPointTransportIntegral D l hl E N.obj ≫
            (pointFibreIntegralAmbient D l E).map
              ((integralDerivedPullback l E (frobeniusPointIso D).hom).map f.hom))) ↔
      pointTransportTowerRealizationSpec D l E hl := by
  constructor <;> intro h
  · simpa only [pointTransportTowerRealizationSpec, trfPointSectionsComplex,
      trfPointSourceTower, trfPointTargetTower, trfPointSourceEnd,
      PointTransportCone.moduleQ, PointTransportCone.sectionsFactors] using! h
  · simpa only [pointTransportTowerRealizationSpec, trfPointSectionsComplex,
      trfPointSourceTower, trfPointTargetTower, trfPointSourceEnd,
      PointTransportCone.moduleQ, PointTransportCone.sectionsFactors] using! h

end ExpandedStatement
end WeilConjectures
