/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q02
-/
module

public import Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafFoldScalar
public import Sheaf.Paper.EtaleProEtaleCoefficientCompatibility
public import Sheaf.Paper.ProperOpenCoefficientRefinement
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtension
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import Sheaf.SecSmoothPurity.SupportedEtaleTensorOrigin
public import Sheaf.Paper.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.QuasiIso
public import Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
public import Sheaf.AlgebraicGeometry.EtaleTorAmplitude
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact

import all Sheaf.EtaleCohomology.Purity.Smooth.EtaleSheafFoldScalar
import all Sheaf.Paper.ScalarPullbackIsoExistence
import all Sheaf.Paper.ScalarPullbackIsoUniqueness
import all Sheaf.Paper.EtaleProEtaleScalarMate
import all Sheaf.SixFunctors.EtaleOpenTensor
import Sheaf.Algebra.Homology.FlatTermKFlatFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all Sheaf.SixFunctors.EtaleOpenTensorDefs

/-! # Common K-flat models for the two étale coefficient-counit composites

Source: Stacks Project, sites-cohomology.tex, Tags 06YY, 06YS and 0G7E;
blueprint latest, det-sp-reduction-exceptional, Charts, integral summation
(blueprint: lem-sp-etale-counit-scalar-model).

The auxiliary constructions name the actual degreewise fold maps and the canonical
exact-localization factors. The computation isomorphisms in the theorem are fixed by
equations with the scalar-extension representative counit, rather than chosen freely.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CoefficientCompatibility

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The common A-complex J = S_A e_A^* P, degreewise, with no boundedness restriction.
Source: Stacks 0G7E and 06YY (blueprint: lem-sp-etale-counit-scalar-model). -/
def etaleCounitScalarSource (A : Type (u + 1)) [CommRing A]
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :=
  (upperStar (ModuleCat.{u + 1} A) e).mapHomologicalComplex (.up ℤ) ⋙
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapHomologicalComplex (.up ℤ)

/-- The common source J tensor B, using the existing ordinary scalar extension.
Source: Stacks 06YY (blueprint: lem-sp-etale-counit-scalar-model). -/
def etaleCounitScalarTensorSource
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :=
  etaleCounitScalarSource A e ⋙
    (ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)

/-- f_P is rho, then S_B(a_P^0), then the B-fold, degreewise.
Source: Stacks 03S3 and 06YY (blueprint: lem-sp-etale-counit-scalar-model). -/
def etaleCounitScalarFirstChain
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (P : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (etaleCounitScalarTensorSource φ e).obj P ⟶
      ((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).obj P :=
  (NatTrans.mapHomologicalComplex
    (etaleScalarReassociatedFold φ e
      (((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance).comp
        (ProEtale.etaleSheafExtendScalarsAdjunction φ V)).leftAdjointUniq
          (((ProEtale.etaleSheafExtendScalarsAdjunction φ U).comp
            (etaleLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} B) e inferInstance)).ofNatIsoRight
                (upperStarRestrictScalarsIsoSheaf φ e).symm)).hom) (.up ℤ)).app P

/-- g_P is the degreewise A-fold tensored with B.
Source: Stacks 03S3 and 06YY (blueprint: lem-sp-etale-counit-scalar-model). -/
def etaleCounitScalarSecondChain
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (P : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    (etaleCounitScalarTensorSource φ e).obj P ⟶
      ((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).obj P :=
  (NatTrans.mapHomologicalComplex (etaleScalarExtendedFold φ e) (.up ℤ)).app P

/-- Q_A J is canonically E_A e_A^*(Q_A P), using precisely the exact factors.
Source: Stacks 015F (blueprint: lem-sp-etale-counit-scalar-model). -/
def etaleCounitScalarSourceIso (A : Type (u + 1)) [CommRing A]
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (P : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    _root_.DerivedCategory.Q.obj ((etaleCounitScalarSource A e).obj P) ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj
          (_root_.DerivedCategory.Q.obj P)) :=
  ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryFactors.app
      (((upperStar (ModuleCat.{u + 1} A) e).mapHomologicalComplex (.up ℤ)).obj P)).symm ≪≫
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.mapIso
      ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategoryFactors.app P).symm

/-- The fixed inverse of lambda_P: transport eta backwards, remove the exact factors,
then use the scalar-extension counit r_J. No inverse of a noninvertible map is taken.
Source: Stacks 06YY and 015F (blueprint: lem-sp-etale-counit-scalar-model). -/
def etaleCounitScalarSourceComputation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (P : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    {K : DerivedCategoryModule A V} (η : _root_.DerivedCategory.Q.obj P ≅ K) :
    (scalarExtension φ V).obj
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)) ⟶
      _root_.DerivedCategory.Q.obj ((etaleCounitScalarTensorSource φ e).obj P) :=
  (scalarExtension φ V).map
      ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map η.inv) ≫
          (etaleCounitScalarSourceIso A e P).inv) ≫
    scalarExtensionRepresentative φ V ((etaleCounitScalarSource A e).obj P)

/-- The first specified derived composite, sigma_e followed by E_B(a_e) and v_B.
Here a_e is the inverse normalized scalar/pullback comparison, expressed with exact
inverse image by properOpenCoefficientPullbackIso.
Source: blueprint Charts and Stacks 06YY (blueprint: lem-sp-etale-counit-scalar-model). -/
def etaleCounitScalarFirstDerived
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (K : DerivedCategoryModule A V) :=
  (sumCoefficientIso φ e).hom.app
      ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
    (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory.map
      ((properOpenCoefficientPullbackIso φ e).inv.app K) ≫
    (derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) e inferInstance).counit.app ((scalarExtension φ V).obj K)

private theorem firstChain_eq_second
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (P : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    etaleCounitScalarFirstChain φ e P = etaleCounitScalarSecondChain φ e P := by
  exact congrArg (fun t ↦ (NatTrans.mapHomologicalComplex t (.up ℤ)).app P)
    (foldScalarGeometricComparison_counit φ e)

private theorem scalarRep_naturality
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (V : Scheme.{u})
    {P P' : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ}
    (h : P ⟶ P') :
    (scalarExtension φ V).map (_root_.DerivedCategory.Q.map h) ≫
        scalarExtensionRepresentative φ V P' =
      scalarExtensionRepresentative φ V P ≫ _root_.DerivedCategory.Q.map
        (((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).map h) := by
  exact (cochainAdjointComparison (ProEtale.etaleSheafExtendScalars φ V)
    (Sheaf.restrictScalars V.smallEtaleTopology φ)
    (ProEtale.etaleSheafExtendScalarsAdjunction φ V)
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ))).naturality h

set_option backward.isDefEq.respectTransparency.types false in
private theorem exactFactorh
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 (_root_.DerivedCategory.Q.obj P)) ≫
    F.mapDerivedCategoryFactors.hom.app P ≫
      𝟙 (_root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        _root_.DerivedCategory.Qh.map
          (𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj P))) = _
  have hi : _root_.DerivedCategory.Qh.map
      (𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P))) =
      𝟙 (_root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
    _root_.DerivedCategory.Qh.map_id _
  rw [hi, CategoryTheory.Functor.map_id]
  change (𝟙 _ ≫ F.mapDerivedCategoryFactors.hom.app P ≫ 𝟙 _ ≫ 𝟙 _) =
    F.mapDerivedCategoryFactors.hom.app P
  simp only [Category.id_comp, Category.comp_id]

private theorem exactAdjCounit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {G : D ⥤ C} (a : F ⊣ G) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (P : CochainComplex D ℤ) :
    a.mapDerivedCategoryAdjunction.counit.app (_root_.DerivedCategory.Q.obj P) =
      F.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app P) ≫
        F.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
          _root_.DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app P) := by
  have h := a.mapDerivedCategoryAdjunction_counit_app_Qh_obj
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  rw [Adjunction.mapHomotopyCategory_counit_app_quotient] at h
  change a.mapDerivedCategoryAdjunction.counit.app (_root_.DerivedCategory.Q.obj P) = _ at h
  rw [h]
  change F.mapDerivedCategory.map
      (G.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj
        ((G.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      _root_.DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app P) = _
  rw [exactFactorh, exactFactorh]

private theorem derivedAdj_eq (A : Type (u + 1)) [CommRing A]
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    (etaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryAdjunction =
      derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance := by
  apply Adjunction.ext_counit
  apply Localization.natTrans_ext _root_.DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
  intro P
  rw [exactAdjCounit]
  rw [derivedEtaleLowerShriekUpperStarAdjunction, Adjunction.localization_counit_app]
  rfl

private theorem pullback_inverse_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    ((mateEquiv
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ))
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ))).symm
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso
            (upperStarRestrictScalarsIsoSheaf φ e)).hom)).natTrans =
      (properOpenCoefficientPullbackIso φ e).inv := by
  set_option backward.isDefEq.respectTransparency false in
    let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
    let b := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
    let x := TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ e).hom
    let i := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e
    let j := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) e
    have heq : TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ e)).hom =
        TwoSquare.mk _ _ _ _
          (Functor.whiskerLeft (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
            i.inv ≫ x.natTrans ≫
            Functor.whiskerRight j.hom
              (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)) := by
      ext M
      dsimp only [x, i, j, scalarRestrictionPullbackIso, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.trans_hom,
        Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom]
      simp only [Category.assoc, Iso.inv_hom_id_app_assoc,
        ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
      erw [Category.comp_id]
    rw [heq, inverse_mate_transport a b x i j]
    have hm : ((mateEquiv a b).symm x).natTrans = (scalarPullbackIso φ e).inv :=
      congrArg Iso.inv (scalarPullback_eq φ e)
    rw [hm]
    ext M
    simp only [properOpenCoefficientPullbackIso, Iso.trans_inv,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Iso.symm_inv,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app, i, j,
      Category.assoc, ProEtale.pbcFixedScalarExtension]

private theorem firstDerived_eq_second
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (K : DerivedCategoryModule A V) :
    etaleCounitScalarFirstDerived φ e K = (scalarExtension φ V).map
      ((derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) e inferInstance).counit.app K) := by
  let a := (etaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategoryAdjunction
  let b := (etaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategoryAdjunction
  let x := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars V.smallEtaleTopology φ)
  let z := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let α := (mateEquiv x z).symm (TwoSquare.mk _ _ _ _
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ e)).hom)
  have hm : ((mateEquiv a b).symm α).natTrans = (sumCoefficientIso φ e).inv := by
    have hh := scalarOpenInverseMate a b x z
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ e)).symm
    rw [uniq_eq_conjugate] at hh
    exact hh
  have h := mateEquiv_counit_symm a b α K
  change _ = ((mateEquiv a b).symm α).natTrans.app _ ≫ _ at h
  rw [hm] at h
  have hr : α.natTrans = (properOpenCoefficientPullbackIso φ e).inv :=
    pullback_inverse_mate φ e
  change (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory.map
      (α.natTrans.app K) ≫ b.counit.app ((scalarExtension φ V).obj K) =
    (sumCoefficientIso φ e).inv.app _ ≫ (scalarExtension φ V).map (a.counit.app K) at h
  rw [hr] at h
  have hh := congrArg (fun t ↦ (sumCoefficientIso φ e).hom.app
    ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫ t) h
  simpa only [a, b, derivedAdj_eq, Category.assoc, Iso.hom_inv_id_app_assoc,
    etaleCounitScalarFirstDerived] using hh

private theorem sourceIso_naturality (A : Type (u + 1)) [CommRing A]
    {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    {P P' : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ}
    (h : P ⟶ P') :
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
        ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map
          (_root_.DerivedCategory.Q.map h)) ≫ (etaleCounitScalarSourceIso A e P').inv =
      (etaleCounitScalarSourceIso A e P).inv ≫
        _root_.DerivedCategory.Q.map ((etaleCounitScalarSource A e).map h) := by
  dsimp only [etaleCounitScalarSourceIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
  simp only [Iso.app_hom]
  rw [← Functor.map_comp_assoc, Functor.mapDerivedCategoryFactors_hom_naturality,
    Functor.map_comp, Category.assoc, Functor.mapDerivedCategoryFactors_hom_naturality]
  exact (Category.assoc _ _ _).symm

private theorem second_computation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (P : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    {K : DerivedCategoryModule A V} (η : _root_.DerivedCategory.Q.obj P ≅ K) :
    etaleCounitScalarSourceComputation φ e P η ≫
        _root_.DerivedCategory.Q.map (etaleCounitScalarSecondChain φ e P) =
      (scalarExtension φ V).map
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).counit.app K) ≫
        (scalarExtension φ V).map η.inv ≫ scalarExtensionRepresentative φ V P := by
  let a := etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance
  let c := (a.mapHomologicalComplex (.up ℤ)).counit.app P
  have hc : etaleCounitScalarSecondChain φ e P =
      ((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).map c := by
    apply HomologicalComplex.Hom.ext
    funext i
    simp only [etaleCounitScalarSecondChain, etaleScalarExtendedFold,
      NatTrans.mapHomologicalComplex_app_f, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.mapHomologicalComplex_map_f,
      c, a, Adjunction.mapHomologicalComplex_counit_app_f]
    exact Category.comp_id _
  have hloc : (etaleCounitScalarSourceIso A e P).inv ≫
      _root_.DerivedCategory.Q.map c =
      (derivedEtaleLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} A) e inferInstance).counit.app (_root_.DerivedCategory.Q.obj P) := by
    rw [derivedEtaleLowerShriekUpperStarAdjunction, Adjunction.localization_counit_app]
    simp only [etaleCounitScalarSourceIso, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
      CatCommSq.iso, Iso.app_hom, Category.assoc]
    rfl
  rw [hc]
  dsimp only [etaleCounitScalarSourceComputation]
  rw [Category.assoc, ← scalarRep_naturality, ← Functor.map_comp_assoc,
    Category.assoc, hloc]
  have hn := (derivedEtaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e inferInstance).counit.naturality η.inv
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn, Functor.map_comp, Category.assoc]
  rfl

private theorem comparison_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {T : D ⥤ E} {G : C ⥤ E} (r : F ⋙ T ⟶ G)
    {P P' : C} {K K' : D} (η : F.obj P ≅ K) (η' : F.obj P' ≅ K')
    (i : G.obj P ≅ T.obj K) (i' : G.obj P' ≅ T.obj K')
    (h : P ⟶ P') (ξ : K ⟶ K')
    (hi : i.inv = T.map η.inv ≫ r.app P)
    (hi' : i'.inv = T.map η'.inv ≫ r.app P')
    (hη : F.map h ≫ η'.hom = η.hom ≫ ξ) :
    G.map h ≫ i'.hom = i.hom ≫ T.map ξ := by
  have hη' : η.inv ≫ F.map h = ξ ≫ η'.inv := by
    apply (cancel_epi η.hom).1
    apply (cancel_mono η'.hom).1
    simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
      Category.comp_id] using hη
  apply (cancel_epi i.inv).1
  apply (cancel_mono i'.inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  rw [hi, hi']
  rw [Category.assoc, ← r.naturality h]
  dsimp only [Functor.comp_map]
  rw [← T.map_comp_assoc, hη', T.map_comp, Category.assoc]

private def sourceRepresentative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e] :
    (_root_.DerivedCategory.Q ⋙ (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory ⋙
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory) ⋙
        scalarExtension φ V ⟶ etaleCounitScalarTensorSource φ e ⋙ _root_.DerivedCategory.Q where
  app P := (scalarExtension φ V).map (etaleCounitScalarSourceIso A e P).inv ≫
    scalarExtensionRepresentative φ V ((etaleCounitScalarSource A e).obj P)
  naturality {P P'} h := by
    dsimp only [Functor.comp_map, Functor.comp_obj]
    rw [← Functor.map_comp_assoc, sourceIso_naturality, Functor.map_comp,
      Category.assoc, scalarRep_naturality]
    exact (Category.assoc _ _ _).symm

private def scalarRepresentative
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (V : Scheme.{u}) :
    _root_.DerivedCategory.Q ⋙ scalarExtension φ V ⟶
      (ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ) ⋙
        _root_.DerivedCategory.Q where
  app := scalarExtensionRepresentative φ V
  naturality {_ _} h := scalarRep_naturality φ V h

private theorem computed_equation
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (P : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    {K : DerivedCategoryModule A V} (η : _root_.DerivedCategory.Q.obj P ≅ K)
    (lam : _root_.DerivedCategory.Q.obj ((etaleCounitScalarTensorSource φ e).obj P) ≅
      (scalarExtension φ V).obj
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)))
    (τ : _root_.DerivedCategory.Q.obj
        (((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).obj P) ≅
      (scalarExtension φ V).obj K)
    (hlam : lam.inv = etaleCounitScalarSourceComputation φ e P η)
    (hτ : τ.inv = (scalarExtension φ V).map η.inv ≫ scalarExtensionRepresentative φ V P) :
    _root_.DerivedCategory.Q.map (etaleCounitScalarSecondChain φ e P) ≫ τ.hom =
      lam.hom ≫ (scalarExtension φ V).map
        ((derivedEtaleLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} A) e inferInstance).counit.app K) := by
  apply (cancel_epi lam.inv).1
  apply (cancel_mono τ.inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc]
  rw [hlam, hτ]
  exact second_computation φ e P η

/-- Separate identification of the two composites on every flat-term K-flat resolution,
with canonical computation maps, naturality, transport, and resolution independence.
Source: Stacks 06YS (lemma-K-flat-resolution), 0G7E (lemma-pullback-K-flat),
06YY (lemma-derived-base-change), and blueprint latest, Charts, integral summation
(blueprint: lem-sp-etale-counit-scalar-model).

Proof:
1. The source flat-preservation instances and the flat-term K-flat functor theorem
apply successively to inverse image and etale sum extension, without boundedness.
2. The exact localization factors give the source isomorphism. Naturality and
K-flat invertibility of the canonical scalar representative give lambda and tau,
with exactly the inverses prescribed in the statement.
3. The total-derived and localized exact adjunctions agree: compare their counits
on homotopy representatives and use localization extensionality. Transport the
normalized scalar/pullback mate to exact inverse image. Iterated mates identify
sigma followed by inverse scalar/pullback and the B-counit with the scalar-extended
A-counit. The already proved ordinary fold identity identifies the two chain maps.
4. Naturality of the scalar representative at the degreewise A-counit and the
localized counit formula prove the second computation equation. The fold identities
then give the first equation with its specified derived composite.
5. The extended fold is natural. Naturality of the source comparison and scalar
representative proves transport of the computation isomorphisms by conjugation.
Both transported chain composites equal the same fixed derived counit, which proves
resolution independence. No flatness or projective dimension of B/A is used. -/
theorem etaleCounitScalarModel
    (ell p : ℕ) [Fact ell.Prime] (_hp : 0 < p) (_hEll : p ≠ ell)
    (k : Type u) [Field k] [CharP k p]
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (_hA : ∃ n : ℕ, (ell ^ n : A) = 0)
    (_hB : ∃ n : ℕ, (ell ^ n : B) = 0) (φ : A →+* B)
    {U V : Scheme.{u}} [U.Over (Spec (.of k))] [V.Over (Spec (.of k))]
    [LocallyOfFiniteType (U ↘ Spec (.of k))] [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))]
    [LocallyOfFiniteType (V ↘ Spec (.of k))] [QuasiCompact (V ↘ Spec (.of k))]
    [IsSeparated (V ↘ Spec (.of k))]
    (e : U ⟶ V) [e.IsOver (Spec (.of k))]
    [Etale e] [IsSeparated e] [LocallyOfFiniteType e] [QuasiCompact e]
    (K : DerivedCategoryModule A V)
    (_hK : DerivedCategory.isBoundedConstructible A V K)
    (_hKtor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A V a b K)
    (_heK : DerivedCategory.isBoundedConstructible A U
      ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K))
    (_heKtor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn A U a b
      ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K))
    (K₀ P : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    (q : P ⟶ K₀) [QuasiIso q]
    (κ : _root_.DerivedCategory.Q.obj K₀ ≅ K)
    (_hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (_hflat : ∀ i : ℤ, ObjectProperty.flat (P.X i)) :
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat
      (((upperStar (ModuleCat.{u + 1} A) e).mapHomologicalComplex (.up ℤ)).obj P) ∧
    (∀ i : ℤ, ObjectProperty.flat
      ((((upperStar (ModuleCat.{u + 1} A) e).mapHomologicalComplex (.up ℤ)).obj P).X i)) ∧
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat ((etaleCounitScalarSource A e).obj P) ∧
    (∀ i : ℤ, ObjectProperty.flat (((etaleCounitScalarSource A e).obj P).X i)) ∧
    ∃ (lam : _root_.DerivedCategory.Q.obj ((etaleCounitScalarTensorSource φ e).obj P) ≅
        (scalarExtension φ V).obj
          ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj
            ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)))
      (τ : _root_.DerivedCategory.Q.obj
          (((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).obj P) ≅
        (scalarExtension φ V).obj K),
      lam.inv = etaleCounitScalarSourceComputation φ e P
        (asIso (_root_.DerivedCategory.Q.map q) ≪≫ κ) ∧
      τ.inv = (scalarExtension φ V).map
          (asIso (_root_.DerivedCategory.Q.map q) ≪≫ κ).inv ≫
        scalarExtensionRepresentative φ V P ∧
      _root_.DerivedCategory.Q.map (etaleCounitScalarFirstChain φ e P) ≫ τ.hom =
        lam.hom ≫ etaleCounitScalarFirstDerived φ e K ∧
      _root_.DerivedCategory.Q.map (etaleCounitScalarSecondChain φ e P) ≫ τ.hom =
        lam.hom ≫ (scalarExtension φ V).map
          ((derivedEtaleLowerShriekUpperStarAdjunction
            (ModuleCat.{u + 1} A) e inferInstance).counit.app K) ∧
      (∀ (P' : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (h : P ⟶ P'),
        (etaleCounitScalarTensorSource φ e).map h ≫ etaleCounitScalarFirstChain φ e P' =
          etaleCounitScalarFirstChain φ e P ≫
            ((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).map h ∧
        (etaleCounitScalarTensorSource φ e).map h ≫ etaleCounitScalarSecondChain φ e P' =
          etaleCounitScalarSecondChain φ e P ≫
            ((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).map h) ∧
      (∀ (P' : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (K' : DerivedCategoryModule A V) (η' : _root_.DerivedCategory.Q.obj P' ≅ K')
        (lam' : _root_.DerivedCategory.Q.obj ((etaleCounitScalarTensorSource φ e).obj P') ≅
          (scalarExtension φ V).obj
            ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj
              ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K')))
        (τ' : _root_.DerivedCategory.Q.obj
            (((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).obj P') ≅
          (scalarExtension φ V).obj K') (h : P ⟶ P') (ξ : K ⟶ K'),
        lam'.inv = etaleCounitScalarSourceComputation φ e P' η' →
        τ'.inv = (scalarExtension φ V).map η'.inv ≫ scalarExtensionRepresentative φ V P' →
        _root_.DerivedCategory.Q.map h ≫ η'.hom =
          (asIso (_root_.DerivedCategory.Q.map q) ≪≫ κ).hom ≫ ξ →
        (_root_.DerivedCategory.Q.map ((etaleCounitScalarTensorSource φ e).map h) ≫
            lam'.hom = lam.hom ≫
          (scalarExtension φ V).map
            ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
              ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map ξ))) ∧
        (_root_.DerivedCategory.Q.map
            (((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).map h) ≫
            τ'.hom = τ.hom ≫ (scalarExtension φ V).map ξ)) ∧
      (∀ (P' : CochainComplex (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
        (η' : _root_.DerivedCategory.Q.obj P' ≅ K)
        (_hP' : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P')
        (_hflat' : ∀ i : ℤ, ObjectProperty.flat (P'.X i))
        (lam' : _root_.DerivedCategory.Q.obj ((etaleCounitScalarTensorSource φ e).obj P') ≅
          (scalarExtension φ V).obj
            ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.obj
              ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K)))
        (τ' : _root_.DerivedCategory.Q.obj
            (((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).obj P') ≅
          (scalarExtension φ V).obj K),
        lam'.inv = etaleCounitScalarSourceComputation φ e P' η' →
        τ'.inv = (scalarExtension φ V).map η'.inv ≫ scalarExtensionRepresentative φ V P' →
        (lam'.inv ≫ _root_.DerivedCategory.Q.map (etaleCounitScalarFirstChain φ e P') ≫
            τ'.hom =
          lam.inv ≫ _root_.DerivedCategory.Q.map (etaleCounitScalarFirstChain φ e P) ≫ τ.hom) ∧
        (lam'.inv ≫ _root_.DerivedCategory.Q.map (etaleCounitScalarSecondChain φ e P') ≫
            τ'.hom =
          lam.inv ≫ _root_.DerivedCategory.Q.map
            (etaleCounitScalarSecondChain φ e P) ≫ τ.hom)) := by
  have hf : ∀ i : ℤ, ObjectProperty.flat
      ((((upperStar (ModuleCat.{u + 1} A) e).mapHomologicalComplex (.up ℤ)).obj P).X i) :=
    fun i ↦ Functor.PreservesFlat.flat_obj (F := upperStar (ModuleCat.{u + 1} A) e)
      (_hflat i)
  have hk := Functor.kFlat_map_of_flat_terms
    (upperStar (ModuleCat.{u + 1} A) e) P _hP _hflat
  have hjf : ∀ i : ℤ, ObjectProperty.flat (((etaleCounitScalarSource A e).obj P).X i) :=
    fun i ↦ Functor.PreservesFlat.flat_obj
      (F := etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance) (hf i)
  let := (etaleLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} A) e inferInstance).isLeftAdjoint
  have hj := Functor.kFlat_map_of_flat_terms
    (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance) _ hk hf
  refine ⟨hk, hf, hj, hjf, ?_⟩
  let η := asIso (_root_.DerivedCategory.Q.map q) ≪≫ κ
  have : IsIso (scalarExtensionRepresentative φ V P) :=
    scalarRepresentative_isIso φ V P _hP
  have : IsIso (scalarExtensionRepresentative φ V ((etaleCounitScalarSource A e).obj P)) :=
    scalarRepresentative_isIso φ V _ hj
  have : IsIso (etaleCounitScalarSourceComputation φ e P η) := by
    dsimp only [etaleCounitScalarSourceComputation]
    infer_instance
  let lam := (asIso (etaleCounitScalarSourceComputation φ e P η)).symm
  let τ := (asIso ((scalarExtension φ V).map η.inv ≫
    scalarExtensionRepresentative φ V P)).symm
  have hlam : lam.inv = etaleCounitScalarSourceComputation φ e P η := rfl
  have hτ : τ.inv = (scalarExtension φ V).map η.inv ≫
      scalarExtensionRepresentative φ V P := rfl
  have hg := computed_equation φ e P η lam τ hlam hτ
  refine ⟨lam, τ, hlam, hτ, ?_, hg, ?_, ?_, ?_⟩
  · simpa only [firstChain_eq_second, firstDerived_eq_second] using hg
  · intro P' h
    have hh := (NatTrans.mapHomologicalComplex (etaleScalarExtendedFold φ e)
      (.up ℤ)).naturality h
    have hh' : (etaleCounitScalarTensorSource φ e).map h ≫
        etaleCounitScalarSecondChain φ e P' = etaleCounitScalarSecondChain φ e P ≫
          ((ProEtale.etaleSheafExtendScalars φ V).mapHomologicalComplex (.up ℤ)).map h := by
      apply HomologicalComplex.Hom.ext
      funext i
      exact congrArg (fun t ↦ t.f i) hh
    exact ⟨by simpa only [firstChain_eq_second] using hh', hh'⟩
  · intro P' K' η' lam' τ' h ξ hlam' hτ' hη
    constructor
    · apply comparison_transport (sourceRepresentative φ e)
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.mapIso
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.mapIso η))
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.mapIso
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.mapIso η'))
        lam lam' h
        ((etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
          ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map ξ))
      · simpa only [sourceRepresentative, etaleCounitScalarSourceComputation,
          Functor.map_comp, Functor.mapIso_inv, Category.assoc] using hlam
      · simpa only [sourceRepresentative, etaleCounitScalarSourceComputation,
          Functor.map_comp, Functor.mapIso_inv, Category.assoc] using hlam'
      · simpa only [Functor.comp_map, Functor.mapIso_hom, ← Functor.map_comp] using
          congrArg (fun t ↦
            (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory.map
              ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.map t)) hη
    · apply comparison_transport (scalarRepresentative φ V) η η' τ τ' h ξ
      · simpa only [scalarRepresentative] using hτ
      · simpa only [scalarRepresentative] using hτ'
      · exact hη
  · intro P' η' _ _ lam' τ' hlam' hτ'
    have hg' := computed_equation φ e P' η' lam' τ' hlam' hτ'
    have heq : lam'.inv ≫
          _root_.DerivedCategory.Q.map (etaleCounitScalarSecondChain φ e P') ≫ τ'.hom =
        lam.inv ≫ _root_.DerivedCategory.Q.map
          (etaleCounitScalarSecondChain φ e P) ≫ τ.hom := by
      rw [hg, hg']
      simp only [Iso.inv_hom_id_assoc]
    exact ⟨by simpa only [firstChain_eq_second] using heq, heq⟩

end AlgebraicGeometry.Etale
