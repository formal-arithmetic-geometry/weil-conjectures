/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointTransportStrictQuotientModels
import all WeilConjectures.AlgebraicGeometry.PointTransportStrictQuotientModels
import all WeilConjectures.SixFunctors.FrobeniusPointTransportNatural
import WeilConjectures.AlgebraicGeometry.IsomorphismComparisonNatural

/-! # Derived evaluation of strict finite point transport

Exact-functor localization factors identify the strict map with the prescribed
finite Frobenius point transport on every finite quotient representative.
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


private theorem finiteTransport_complex (hl : l ≠ D.p) (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    frobeniusPointTransportFinite D l hl E n (DerivedCategory.Q.obj K) =
      frobeniusPointTransportFiniteComplex D l hl E n K := by
  let g := (frobeniusPointIso D).hom
  let S := pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))
  let H := inverseImageFiniteModules l E g n
  let Sd := S.mapDerivedCategory
  let Hd := H.mapDerivedCategory
  let T := finiteDerivedPullback l E n g
  have : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_le_succ (Nat.zero_le n))
  let e := inverseImageFiniteIntrinsicPullbackComparison g
    (Padic.coefficientExtensionRing l E (n + 1))
  obtain ⟨σ, _, hσ⟩ := naturalFiniteSigmaDerived D l E n
  obtain ⟨κ, hk, _⟩ := inverseImagePullbackComparisonFinite_natural.{u, u, 0, 0} l E g
    (frobeniusPointPrimeUnit D l hl) (frobeniusPointPrimeUnit D l hl) n
  let : (coefficientProEtaleModulePullback g
      (CommRingCat.of (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
    integralOperationsLevelPullback_additive l E g n
  let : PreservesFiniteLimits (coefficientProEtaleModulePullback g
      (CommRingCat.of (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_limits l E g n
  let : PreservesFiniteColimits (coefficientProEtaleModulePullback g
      (CommRingCat.of (ULift.{u + 1, u}
        (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_colimits l E g n
  let κ' : Hd ⟶ T := κ ≫ (Functor.mapDerivedCategoryNatIso e).hom
  let τ : Sd ⟶ T ⋙ Sd := σ ≫ Functor.whiskerRight κ' Sd
  have hτ (K : CochainComplex
      (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
      τ.app (DerivedCategory.Q.obj K) =
        frobeniusPointTransportFiniteComplex D l hl E n K := by
    dsimp only [τ, NatTrans.comp_app, Functor.whiskerRight_app, κ']
    rw [hσ, hk]
    simp only [frobeniusPointTransportFiniteComplex, inverseImagePullbackComparisonFiniteIntrinsic,
      Functor.map_comp, Category.assoc]
    rfl
  have hN (N) : τ.app N = frobeniusPointTransportFinite D l hl E n N := by
    rw [conjugate_component τ (DerivedCategory.Q.objObjPreimageIso N), hτ]
    rfl
  rw [← hN]
  exact hτ K

private theorem exactFactors_square
    {C M N Dc Dm Dn : Type*}
    [Category C] [Category M] [Category N]
    [Category Dc] [Category Dm] [Category Dn]
    (Q₀ : C ⥤ Dc) (Q₁ : M ⥤ Dm) (Q₂ : N ⥤ Dn)
    (S₀ : C ⥤ M) (S₁ : Dc ⥤ Dm) (R₀ : M ⥤ N) (R₁ : Dm ⥤ Dn)
    (eS : Q₀ ⋙ S₁ ≅ S₀ ⋙ Q₁) (eR : Q₁ ⋙ R₁ ≅ R₀ ⋙ Q₂)
    {X Y Z : C} (σ : S₀.obj X ⟶ S₀.obj Y) (κ : Y ⟶ Z) :
    Q₂.map (R₀.map σ) ≫ Q₂.map (R₀.map (S₀.map κ)) ≫
        eR.inv.app (S₀.obj Z) ≫ R₁.map (eS.inv.app Z) =
      eR.inv.app (S₀.obj X) ≫ R₁.map (eS.inv.app X) ≫ R₁.map (eS.hom.app X) ≫
        R₁.map (Q₁.map σ) ≫ R₁.map (eS.inv.app Y) ≫ R₁.map (S₁.map (Q₀.map κ)) := by
  simp only [← R₁.map_comp, Iso.inv_hom_id_app_assoc]
  have hS := eS.inv.naturality κ
  simp only [Functor.comp_map] at hS
  rw [← hS]
  simp only [Functor.map_comp]
  have hκ := eR.inv.naturality (S₀.map κ)
  have hσ := eR.inv.naturality σ
  simp only [Functor.comp_map] at hκ hσ
  rw [reassoc_of% hκ, reassoc_of% hσ]


private theorem finitePointMap_derived (hl : l ≠ D.p) (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ) :
    DerivedCategory.Q.map (finitePointMap D l E n K) ≫
        (strictQuotientPointTargetIso D l E n K).hom =
      (strictQuotientPointSectionsIso D l E n K).hom ≫
        (strictQuotientPointDerivedRestriction l E n).map
          (frobeniusPointTransportFinite D l hl E n (DerivedCategory.Q.obj K)) := by
  rw [finiteTransport_complex D l E hl n]
  let : Finite (Padic.coefficientExtensionRing l E (n + 1)) :=
    Padic.finite_coefficientExtensionRing l E (n + 1)
      (Nat.succ_le_succ (Nat.zero_le n))
  let : (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
      (CommRingCat.of (ULift.{u + 1}
        (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
    integralOperationsLevelPullback_additive l E (frobeniusPointIso D).hom n
  let : PreservesFiniteLimits
      (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
        (CommRingCat.of (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_limits l E (frobeniusPointIso D).hom n
  let : PreservesFiniteColimits
      (coefficientProEtaleModulePullback (frobeniusPointIso D).hom
        (CommRingCat.of (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E (n + 1))))) :=
    inverseImageFinitePullback_colimits l E (frobeniusPointIso D).hom n
  dsimp only [finitePointMap, strictQuotientPointTargetIso,
    strictQuotientPointSectionsIso, frobeniusPointTransportFiniteComplex,
    inverseImagePullbackComparisonFiniteIntrinsic, inverseImagePullbackComparisonFinite,
    strictQuotientPointDerivedRestriction]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_hom]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc,
    Iso.map_inv_hom_id_assoc]
  let S := pointFiniteSections D.k (Padic.coefficientExtensionRing l E (n + 1))
  let R := pointUnitIntegralRestriction l E n
  let κ := inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n K
  let σ := frobeniusPointFiniteSigma D l E n K
  let F := integralOperationsLevelPullback l E (frobeniusPointIso D).hom n
  let j := (Functor.mapDerivedCategoryNatIso
    (inverseImageFiniteIntrinsicPullbackComparison (frobeniusPointIso D).hom
      (Padic.coefficientExtensionRing l E (n + 1)))).hom.app (DerivedCategory.Q.obj K)
  have hsquare := exactFactors_square DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (S.mapHomologicalComplex (.up ℤ)) S.mapDerivedCategory
    (R.mapHomologicalComplex (.up ℤ)) R.mapDerivedCategory
    S.mapDerivedCategoryFactors R.mapDerivedCategoryFactors σ κ
  have h := congrArg
    (fun t ↦ DerivedCategory.Q.map
      (strictQuotientPointRestrictionComplexIso D l E n K).hom ≫ t ≫
      R.mapDerivedCategory.map (S.mapDerivedCategory.map
        (F.mapDerivedCategoryFactors.inv.app K)) ≫
      R.mapDerivedCategory.map (S.mapDerivedCategory.map j)) hsquare
  simpa only [Category.assoc] using h


/-- Finite evaluation through the canonical source and target comparisons.
Source: retained blueprint clause (3), finite point transport.
(blueprint: lem-trf-point-transport-strict-quotient-finite-evaluation).

Proof: finite sigma and the inverse-image comparison descend naturally. Their
component at a complex is the specified finite transport formula. Naturality
of exact scalar restriction and sections cancels the canonical localization
factors and gives the stated comparison. -/
theorem strictQuotientPointMap_derived (hl : l ≠ D.p) (n : ℕ)
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ) :
    DerivedCategory.Q.map (strictQuotientPointMap D l E n P) ≫
        (strictQuotientPointTargetIso D l E n
          ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P)).hom =
      (strictQuotientPointSectionsIso D l E n
        ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P)).hom ≫
        (strictQuotientPointDerivedRestriction l E n).map
          (frobeniusPointTransportFinite D l hl E n
            (DerivedCategory.Q.obj
              ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P))) := by
  exact finitePointMap_derived D l E hl n
    ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P)

end WeilConjectures
