/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleAmbientAdjointLocality
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleProEtaleAdjunctionTransfer
public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
public import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensor
import WeilConjectures.CategoryTheory.DerivedCategory.AdjunctionUnit
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible

/-!
# Scalar compatibility of the etale sum-extension counit

Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/
sk-lem-sp-reduction/sk-lem-sp-reduction-exceptional.proof.md, Charts, integral summation;
Stacks Project, etale-cohomology.tex, Tag 03S3
(blueprint: lem-sp-etale-sum-counit-scalar).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CoefficientCompatibility

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private noncomputable def etaleCounitScalarFirstDerived
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U V : Scheme.{u}} (e : U ⟶ V) [Etale e]
    (K : DerivedCategoryModule A V) :=
  (sumCoefficientIso φ e).hom.app
      ((upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj K) ≫
    (etaleLowerShriek (ModuleCat.{u + 1} B) e inferInstance).mapDerivedCategory.map
      ((properOpenCoefficientPullbackIso φ e).inv.app K) ≫
    (derivedEtaleLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} B) e inferInstance).counit.app ((scalarExtension φ V).obj K)

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

private theorem boundedConstructible_iff_source
    (R : Type (u + 1)) [CommRing R] [Finite R] (X : Scheme.{u})
    (M : DerivedCategoryModule R X) :
    DerivedCategory.isBoundedConstructible R X M ↔
      DerivedCategory.boundedConstructible (ModuleCat.{u + 1} R) X M := by
  constructor
  · rintro ⟨hc, a, b, -, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mp (hc i)⟩
    · exact (_root_.DerivedCategory.isGE_iff M a).mpr fun i hi ↦ hz i (.inl hi)
    · exact (_root_.DerivedCategory.isLE_iff M b).mpr fun i hi ↦ hz i (.inr hi)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦
      (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).mpr (hc i),
      min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (_root_.DerivedCategory.isGE_iff M a).mp ha i
        (hi.trans_le (min_le_left _ _))
    · exact (_root_.DerivedCategory.isLE_iff M b).mp hb i hi

end AlgebraicGeometry.Etale
