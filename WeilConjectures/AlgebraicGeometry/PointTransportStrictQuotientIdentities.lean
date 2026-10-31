/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointTransportStrictQuotientModels
import WeilConjectures.AlgebraicGeometry.PointTransportStrictQuotientSections

/-! # Strict transition, augmentation and naturality identities

The actual pullback transitions and quotient units commute with point transport
before localization. These formulas do not require flatness of the complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  HasDerivedCategory.standard
  scalarReductionExistence unrestrictedIntegralReductionExistence
  pointIntegralSectionMap
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local implicit_reducible] strictQuotientPointRestrictionComplexIso
  pointUnitIntegralSectionsRestrictionIso pointIntegralSections pointFiniteSections
  unrestrictedIntegralComplexFunctor
  unrestrictedIntegralReductionFunctor scalarReductionExtension
  integralOperationsRestrict integralOperationsPullbackLevel
  integralOperationsLevelPullback inverseImageReductionTheta
  completedIntegralCommRingSheafUnrestricted integralCoefficientSheaf
  integralCoefficientCommRingSheaf ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj' SheafOfModules.restrictScalars
  PresheafOfModules.restrictScalars PresheafOfModules.restrictScalarsObj
  inverseImageFiniteComparisonComplex frobeniusPointFiniteSigma frobeniusPointIntegralSigma


private theorem pointMap_transition
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ) :
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
        ((unrestrictedIntegralTransition l E (Spec (.of D.k)) n).app P) ≫
        strictQuotientPointMap D l E n P =
      strictQuotientPointMap D l E (n + 1) P ≫
        ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          ((integralOperationsPullbackTransition l E (frobeniusPointIso D).hom n).app P) := by
  apply HomologicalComplex.hom_ext
  intro i
  ext x
  change (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) (n + 1)).obj P).X i
    ).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k))))) at x
  change (strictQuotientPointMap D l E n P).f i
      ((((unrestrictedIntegralTransition l E (Spec (.of D.k)) n).app P).f i).val.app _ x) =
    (((integralOperationsPullbackTransition l E (frobeniusPointIso D).hom n).app P
      ).f i).val.app _ ((strictQuotientPointMap D l E (n + 1) P).f i x)
  let U := ProEt.mk (𝟙 (Spec (.of D.k)))
  let V := (proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U
  let y := (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) (n + 1)).obj P
    ).X i).val.map (frobeniusPointRestriction D).op x
  have ht := (integralOperationsPullbackTransition_existsUnique l E
    (frobeniusPointIso D).hom n).exists.choose_spec P i V y
  have hr := congrArg (fun k ↦ k
      (integralOperationsPullbackGenerator l E (frobeniusPointIso D).hom (n + 1)
        (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) (n + 1)).obj P).X i) V y))
    ((((integralOperationsPullbackTransition l E (frobeniusPointIso D).hom n
      ).app P).f i).val.naturality
      (proEtaleIsoCommaArrow (frobeniusPointIso D).hom U).op)
  have hn := PresheafOfModules.naturality_apply
    (((unrestrictedIntegralTransition l E (Spec (.of D.k)) n).app P).f i).val
    (frobeniusPointRestriction D).op x
  have hraw := (hr.trans (congrArg
    ((((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).obj P).X i
      ).val.map (proEtaleIsoCommaArrow (frobeniusPointIso D).hom U).op)
    (ht.trans (congrArg
      (integralOperationsPullbackGenerator l E (frobeniusPointIso D).hom n
        (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i) V)
      hn)))).symm
  exact (strictQuotientPointMap_sections D l E n P i _).trans
    (hraw.trans (congrArg
      (fun z ↦ (((integralOperationsPullbackTransition l E (frobeniusPointIso D).hom n
        ).app P).f i).val.app (op U) z)
      (strictQuotientPointMap_sections D l E (n + 1) P i x).symm))

private theorem pointMap_augmentation
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ) :
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
        (unrestrictedTowerUnit l E (Spec (.of D.k)) P n) ≫
        strictQuotientPointMap D l E n P =
      frobeniusPointIntegralSigma D l E P ≫
        ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P) := by
  apply HomologicalComplex.hom_ext
  intro i
  ext x
  change (P.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k))))) at x
  change (strictQuotientPointMap D l E n P).f i
      (((unrestrictedTowerUnit l E (Spec (.of D.k)) P n).f i).val.app _ x) =
    ((inverseImageReductionTheta l E (frobeniusPointIso D).hom n P).f i).val.app _
      ((frobeniusPointIntegralSigma D l E P).f i x)
  have hσ := congrFun (eq_of_heq
    ((frobeniusPointIntegralSigma_existsUnique D l E P).choose_spec.1 i)) x
  change (frobeniusPointIntegralSigma D l E P).f i x = _ at hσ
  have hθ := (inverseImageReductionTheta_existsUnique l E (frobeniusPointIso D).hom
    n P).exists.choose_spec i (ProEt.mk (𝟙 (Spec (.of D.k))))
      ((P.X i).val.map (frobeniusPointRestriction D).op x)
  have hn := PresheafOfModules.naturality_apply
    ((unrestrictedTowerUnit l E (Spec (.of D.k)) P n).f i).val
    (frobeniusPointRestriction D).op x
  have hraw := congrArg
    (fun z ↦ (((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n
      ).obj P).X i).val.map
      (proEtaleIsoCommaArrow (frobeniusPointIso D).hom
        (ProEt.mk (𝟙 (Spec (.of D.k))))).op
      (integralOperationsPullbackGenerator l E (frobeniusPointIso D).hom n
        (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i)
        ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
          (ProEt.mk (𝟙 (Spec (.of D.k))))) z))
    (hn.symm.trans (unrestrictedTowerUnit_condition l E (Spec (.of D.k)) P n i _ _))
  exact (strictQuotientPointMap_sections D l E n P i _).trans
    (hraw.trans (hθ.symm.trans (congrArg
      (fun y ↦ ((inverseImageReductionTheta l E (frobeniusPointIso D).hom n P).f i
        ).val.app (op (ProEt.mk (𝟙 (Spec (.of D.k))))) y) hσ.symm)))

private theorem pointMap_naturality
    {P P' : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ}
    (f : P ⟶ P') (n : ℕ) :
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
        ((unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n).map f) ≫
        strictQuotientPointMap D l E n P' =
      strictQuotientPointMap D l E n P ≫
        ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          ((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).map f) := by
  apply HomologicalComplex.hom_ext
  intro i
  ext x
  change (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i
    ).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k))))) at x
  let a := ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).map f).f i
  change (strictQuotientPointMap D l E n P').f i (a.val.app _ x) =
    (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).map a).val.app _)
      ((strictQuotientPointMap D l E n P).f i x)
  let U := ProEt.mk (𝟙 (Spec (.of D.k)))
  let V := (proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj U
  let y := (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i
    ).val.map (frobeniusPointRestriction D).op x
  let adj := coefficientProEtaleModuleAdjunction.{u, u} (frobeniusPointIso D).hom
    (CommRingCat.of (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))
  have hn := PresheafOfModules.naturality_apply a.val (frobeniusPointRestriction D).op x
  have hu := congrArg (fun k ↦ k.val.app (op V) y) (adj.unit.naturality a)
  have hr := congrArg (fun k ↦ k
    (integralOperationsPullbackGenerator l E (frobeniusPointIso D).hom n
      (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i) V y))
    (((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).map a
      ).val.naturality (proEtaleIsoCommaArrow (frobeniusPointIso D).hom U).op)
  have hraw := (congrArg
    (fun z ↦ (((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n
      ).obj P').X i).val.map (proEtaleIsoCommaArrow (frobeniusPointIso D).hom U).op
      (integralOperationsPullbackGenerator l E (frobeniusPointIso D).hom n
        (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P').X i) V z))
    hn.symm).trans ((congrArg
      ((((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).obj P').X i
        ).val.map (proEtaleIsoCommaArrow (frobeniusPointIso D).hom U).op) hu).trans hr.symm)
  exact (strictQuotientPointMap_sections D l E n P' i _).trans
    (hraw.trans (congrArg
      (fun z ↦ ((integralOperationsLevelPullback l E (frobeniusPointIso D).hom n).map a
        ).val.app (op U) z) (strictQuotientPointMap_sections D l E n P i x).symm))

/-- Strict compatibility with transitions, augmentation and chain maps.
Source: retained blueprint clause (3), simultaneous quotient transport.
(blueprint: lem-trf-point-transport-strict-quotient-identities).

Proof: evaluate the section formula degreewise. Naturality of restriction and
the prescribed pullback transition formula give the transition identity. The
integral sigma, theta and quotient-unit formulas give augmentation. Naturality
of the pullback adjunction unit gives naturality for every chain map. -/
theorem strictQuotientPointMap_identities :
    (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ),
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
        ((unrestrictedIntegralTransition l E (Spec (.of D.k)) n).app P) ≫
        strictQuotientPointMap D l E n P =
      strictQuotientPointMap D l E (n + 1) P ≫
        ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          ((integralOperationsPullbackTransition l E (frobeniusPointIso D).hom n).app P)) ∧
    (∀ (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) (n : ℕ),
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
        (unrestrictedTowerUnit l E (Spec (.of D.k)) P n) ≫
        strictQuotientPointMap D l E n P =
      frobeniusPointIntegralSigma D l E P ≫
        ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          (inverseImageReductionTheta l E (frobeniusPointIso D).hom n P)) ∧
    (∀ (P P' : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (f : P ⟶ P') (n : ℕ),
    ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
        ((unrestrictedIntegralComplexFunctor l E (Spec (.of D.k)) n).map f) ≫
        strictQuotientPointMap D l E n P' =
      strictQuotientPointMap D l E n P ≫
        ((pointIntegralSections l E D.k).mapHomologicalComplex (.up ℤ)).map
          ((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).map f)) := by
  exact ⟨pointMap_transition D l E, pointMap_augmentation D l E,
    fun P P' f n ↦ pointMap_naturality D l E f n⟩

end WeilConjectures
