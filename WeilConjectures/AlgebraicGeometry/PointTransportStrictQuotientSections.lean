/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PointTransportStrictQuotientModels
import all WeilConjectures.AlgebraicGeometry.PointTransportStrictQuotientModels

/-! # Formula for strict point transport on sections

The scalar-restriction comparisons are identity maps on sections, so the strict
map is exactly the specified finite sigma followed by tensor insertion.
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


private theorem restriction_hom_apply (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
    (i : ℤ)
    (x : (K.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))) :
    ((strictQuotientPointRestrictionComplexIso D l E n K).hom.f i) x = x := by
  exact (pointUnitIntegralSectionsRestriction D l E n).exists.choose_spec (K.X i) x

private theorem restriction_inv_apply (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
    (i : ℤ)
    (x : (K.X i).val.obj (op (ProEt.mk (𝟙 (Spec (.of D.k)))))) :
    ((strictQuotientPointRestrictionComplexIso D l E n K).inv.f i) x = x := by
  have h := congrArg (fun f ↦ f.f i x)
    (strictQuotientPointRestrictionComplexIso D l E n K).hom_inv_id
  change ((strictQuotientPointRestrictionComplexIso D l E n K).inv.f i)
    (((strictQuotientPointRestrictionComplexIso D l E n K).hom.f i) x) = x at h
  rwa [restriction_hom_apply] at h

private theorem finitePointMap_apply (n : ℕ)
    (K : CochainComplex (integralOperationsFiniteModules l E (Spec (.of D.k)) n) ℤ)
    (i : ℤ)
    (x : (K.X i).val.obj
      (op (ProEt.mk (𝟙 (Spec (.of D.k)))))) :
    (finitePointMap D l E n K).f i x =
      ((inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n
        K).f i).val.app
          (op (ProEt.mk (𝟙 (Spec (.of D.k)))))
          ((K.X i).val.map
            (frobeniusPointRestriction D).op x) := by
  let κ := inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n K
  let σ := frobeniusPointFiniteSigma D l E n K
  let U := op (ProEt.mk (𝟙 (Spec (.of D.k))))
  have hσ := congrFun (eq_of_heq
    ((frobeniusPointFiniteSigma_existsUnique D l E n K).choose_spec.1 i)) x
  exact (restriction_inv_apply D l E n _ i
    ((κ.f i).val.app U ((σ.f i)
      (((strictQuotientPointRestrictionComplexIso D l E n K).hom.f i) x)))).trans
    ((congrArg (fun y ↦ (κ.f i).val.app U ((σ.f i) y))
      (restriction_hom_apply D l E n K i x)).trans
      (congrArg (fun y ↦ (κ.f i).val.app U y) hσ))

private theorem pointMap_apply (n : ℕ)
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (i : ℤ)
    (x : (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i).val.obj
      (op (ProEt.mk (𝟙 (Spec (.of D.k)))))) :
    (strictQuotientPointMap D l E n P).f i x =
      ((inverseImageFiniteComparisonComplex l E (frobeniusPointIso D).hom n
        ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P)).f i).val.app
          (op (ProEt.mk (𝟙 (Spec (.of D.k)))))
          ((((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i).val.map
            (frobeniusPointRestriction D).op x) := by
  exact finitePointMap_apply D l E n
    ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P) i x

/-- Formula on sections of every degree. Source: the specified sigma and kappa
formulas in the retained strict-quotient transport argument.
(blueprint: lem-trf-point-transport-strict-quotient-sections).

Proof: the published scalar-restriction comparison and its inverse are identity
on sections. Apply the prescribed finite sigma formula and then the prescribed
finite kappa formula to the resulting restricted section. -/
theorem strictQuotientPointMap_sections (n : ℕ)
    (P : CochainComplex (integralTowerModules l E (Spec (.of D.k))) ℤ)
    (i : ℤ)
    (x : (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i).val.obj
      (op (ProEt.mk (𝟙 (Spec (.of D.k)))))) :
    (strictQuotientPointMap D l E n P).f i x =
      (((integralOperationsPullbackLevel l E (frobeniusPointIso D).hom n).obj P).X i).val.map
        (proEtaleIsoCommaArrow (frobeniusPointIso D).hom
          (ProEt.mk (𝟙 (Spec (.of D.k))))).op
        (integralOperationsPullbackGenerator l E (frobeniusPointIso D).hom n
          (((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i)
          ((proEtaleIsoPostcompose (frobeniusPointIso D).hom).obj
            (ProEt.mk (𝟙 (Spec (.of D.k)))))
          ((((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P).X i).val.map
            (frobeniusPointRestriction D).op x)) := by
  exact (pointMap_apply D l E n P i x).trans
    ((inverseImageFiniteComparison_existsUnique l E (frobeniusPointIso D).hom n
    ((unrestrictedIntegralFiniteComplex l E (Spec (.of D.k)) n).obj P)
    ).exists.choose_spec i (ProEt.mk (𝟙 (Spec (.of D.k)))) _)


end WeilConjectures
