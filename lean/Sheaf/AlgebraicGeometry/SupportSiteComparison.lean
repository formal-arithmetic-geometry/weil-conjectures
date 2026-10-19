/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups NY and Q86
-/
module

public import Sheaf.AlgebraicGeometry.NormalizedSupportTriangle
public import Sheaf.AlgebraicGeometry.SupportLongExact
public import Sheaf.AlgebraicGeometry.ProEtaleSupportedExteriorProduct
public import Sheaf.AlgebraicGeometry.ComparisonGlobalCohomologyFiniteNormalized
public import Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
import Sheaf.AlgebraicGeometry.SupportCohomology
import Sheaf.AlgebraicGeometry.SupportedExteriorProduct
import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
import Sheaf.CategoryTheory.DerivedCategory.AdjointFunctors
import Sheaf.AlgebraicGeometry.DerivedSupportDirectImageComparison
import Sheaf.AlgebraicGeometry.SupportQuotientFlat
import Sheaf.AlgebraicGeometry.SupportQuotientProduct
import Sheaf.AlgebraicGeometry.SupportedProductQuotientModel
import Sheaf.Paper.ComparisonPullbackExact
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses

/-!
# Comparison of ordinary supported sections between the two sites

Source: Stacks Project, Tags 099W, 099V, 09B1 and 09XP, with the supported
refinement of blueprint `lem-pur-support-site-comparison`
(blueprint: lem-pur-support-site-comparison).

## Main definitions and statements

* `ProEtale.supportComparison`: the natural bounded-below comparison map.
* `ProEtale.supportComparison_isIso`: invertibility under the node's hypotheses.
* `ProEtale.supportComparison_forget`, `ProEtale.fullSupportForget_isIso`, and
  `ProEtale.supportComparison_open`: forgetting, full-support normalization, and restriction.
* `ProEtale.supportExteriorCoefficientIso`: the specified tensor/pullback comparison theta.
* `ProEtale.supportComparison_exterior`: equality of the supported exterior-product maps.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v₁ v₂ v₃ w₁ w₂ w₃

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace CategoryTheory.Functor
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  [HasKInjectiveResolutions C]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
private lemma compatibility_fac (F : C ⥤ D) [F.Additive] (K : HomotopyCategory.Plus C) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
      F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K) =
    F.rightDerivedFunctorUnit.app K.obj := by
  have h : F.rightDerivedFunctorPlusιUnit.app K ≫
      F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K) =
      F.ιRightDerivedFunctorUnit.app K := by
    simp [Functor.rightDerivedFunctorPlusCompatibility]
  exact h

private lemma compatibility_naturality (τ : F ⟶ G) :
    Functor.whiskerRight (rightDerivedFunctorPlusNatTrans τ) DerivedCategory.Plus.ι ≫
      G.rightDerivedFunctorPlusCompatibility.hom =
    F.rightDerivedFunctorPlusCompatibility.hom ≫
      Functor.whiskerLeft DerivedCategory.Plus.ι (rightDerivedFunctorNatTrans τ) := by
  apply Functor.rightDerived_ext _ F.rightDerivedFunctorPlusιUnit
    (HomotopyCategory.Plus.quasiIso C)
  ext K : 2
  change DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
      (DerivedCategory.Plus.ι.map ((rightDerivedFunctorPlusNatTrans τ).app
        (DerivedCategory.Plus.Qh.obj K)) ≫ _) =
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
      (F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K) ≫ _)
  rw [← Category.assoc, ← Functor.map_comp, rightDerivedFunctorPlusNatTrans_app,
    Functor.map_comp, Category.assoc, compatibility_fac, ← Category.assoc,
    compatibility_fac]
  change DerivedCategory.Qh.map
      ((HomotopyCategory.Plus.ι D).map ((NatTrans.mapHomotopyCategoryPlus τ).app K)) ≫ _ = _
  rw [NatTrans.ι_map_mapHomotopyCategoryPlus_app]
  exact (rightDerivedNatTrans_app F.rightDerivedFunctor G.rightDerivedFunctor
    F.rightDerivedFunctorUnit G.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (.up ℤ)) DerivedCategory.Qh)
    K.obj).symm
end CategoryTheory.Functor

namespace CategoryTheory.Functor
section BaseChange
variable {C C' D : Type*} [Category C] [Category C'] [Category D]
  [Abelian C] [Abelian C'] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
  [EnoughInjectives C] [EnoughInjectives C']
  (B : C ⥤ C') [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
  {G J : C ⥤ D} {H I : C' ⥤ D} [G.Additive] [J.Additive] [H.Additive] [I.Additive]
private noncomputable def testBC (e : G ⟶ B ⋙ H) :
    G.rightDerivedFunctorPlus ⟶ B.mapDerivedCategoryPlus ⋙ H.rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso D)).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange ((Functor.rightUnitor _).hom ≫ e)
private lemma testBC_fac (e : G ⟶ B ⋙ H) (K : HomotopyCategory.Plus C) :
    G.rightDerivedFunctorPlusUnit.app K ≫ (testBC B e).app (DerivedCategory.Plus.Qh.obj K) =
    DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e).app K) ≫
      DerivedCategory.Plus.Qh.map
        ((Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (B ⋙ H))).inv.app K) ≫
      H.rightDerivedFunctorPlusUnit.app (B.mapHomotopyCategoryPlus.obj K) ≫
      H.rightDerivedFunctorPlus.map (B.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  simp only [testBC, NatTrans.comp_app, Functor.rightUnitor_inv_app,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app]
  erw [Category.id_comp]
  have hn := (Functor.mapDerivedCategoryPlusIdIso D).inv.naturality
    (G.rightDerivedFunctorPlusUnit.app K)
  simp only [Functor.id_map] at hn
  rw [reassoc_of% hn]
  have hf := NatTrans.congr_app
    (Functor.rightDerivedFunctorPlusBaseChange_fac ((Functor.rightUnitor _).hom ≫ e)) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Category.comp_id] at hf
  rw [hf]
  simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id]
  rw [← Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp_assoc]
  congr 2
  rw [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app, Category.id_comp]
  congr 1
  apply NatTrans.ext
  funext X
  simp
private lemma testBC_naturality
    (e : G ⟶ B ⋙ H) (e' : J ⟶ B ⋙ I) (a : G ⟶ J) (b : H ⟶ I)
    (h : e ≫ Functor.whiskerLeft B b = a ≫ e') :
    testBC B e ≫ Functor.whiskerLeft B.mapDerivedCategoryPlus
        (rightDerivedFunctorPlusNatTrans b) =
      rightDerivedFunctorPlusNatTrans a ≫ testBC B e' := by
  apply rightDerived_ext _ G.rightDerivedFunctorPlusUnit
    (HomotopyCategory.Plus.quasiIso C)
  ext K : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← Category.assoc, testBC_fac, Category.assoc, Category.assoc, Category.assoc]
  have hn := (rightDerivedFunctorPlusNatTrans b).naturality
    (B.mapDerivedCategoryPlusFactorsh.inv.app K)
  dsimp only [Functor.comp_obj] at hn
  erw [hn]
  rw [reassoc_of% (rightDerivedFunctorPlusNatTrans_app b
    (B.mapHomotopyCategoryPlus.obj K)),
    reassoc_of% (rightDerivedFunctorPlusNatTrans_app a K), testBC_fac]
  simp only [Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, Functor.map_id,
    Category.id_comp]
  rw [← Functor.map_comp_assoc]
  have hh := NatTrans.congr_app (congrArg NatTrans.mapHomotopyCategoryPlus h) K
  simp only [NatTrans.mapHomotopyCategoryPlus_comp, NatTrans.comp_app] at hh
  have ht : (NatTrans.mapHomotopyCategoryPlus e).app K ≫
      (NatTrans.mapHomotopyCategoryPlus b).app (B.mapHomotopyCategoryPlus.obj K) =
      (NatTrans.mapHomotopyCategoryPlus a).app K ≫
        (NatTrans.mapHomotopyCategoryPlus e').app K := hh
  rw [ht, Functor.map_comp]
  simp only [Category.assoc]
end BaseChange
end CategoryTheory.Functor

namespace CategoryTheory.Functor
section Transport
variable {C C' D : Type*} [Category C] [Category C'] [Category D]
  [Abelian C] [Abelian C'] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
  [EnoughInjectives C] [EnoughInjectives C']
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions C']
  (B : C ⥤ C') [B.Additive] [PreservesFiniteLimits B] [PreservesFiniteColimits B]
  {G J : C ⥤ D} {H I : C' ⥤ D} [G.Additive] [J.Additive] [H.Additive] [I.Additive]
private noncomputable def transportedBC (e : G ⟶ B ⋙ H) (M : DerivedCategory.Plus C) :=
  G.rightDerivedFunctorPlusCompatibility.inv.app M ≫
    DerivedCategory.Plus.ι.map ((testBC B e).app M) ≫
      H.rightDerivedFunctorPlusCompatibility.hom.app (B.mapDerivedCategoryPlus.obj M)
private lemma transportedBC_naturality
    (e : G ⟶ B ⋙ H) (e' : J ⟶ B ⋙ I) (a : G ⟶ J) (b : H ⟶ I)
    (h : e ≫ Functor.whiskerLeft B b = a ≫ e') (M : DerivedCategory.Plus C) :
    transportedBC B e M ≫ (rightDerivedFunctorNatTrans b).app
        (B.mapDerivedCategory.obj M.obj) =
      (rightDerivedFunctorNatTrans a).app M.obj ≫ transportedBC B e' M := by
  have ha := NatTrans.congr_app (compatibility_naturality a) M
  have hb := NatTrans.congr_app (compatibility_naturality b)
    (B.mapDerivedCategoryPlus.obj M)
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at ha hb
  dsimp only [Functor.mapDerivedCategoryPlus, ObjectProperty.lift,
    Functor.comp_obj, ObjectProperty.ι_obj] at hb
  dsimp only [transportedBC]
  simp only [Category.assoc]
  erw [← hb]
  rw [← Functor.map_comp_assoc]
  have hc := NatTrans.congr_app (testBC_naturality B e e' a b h) M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hc
  erw [hc, Functor.map_comp]
  have ha' : G.rightDerivedFunctorPlusCompatibility.inv.app M ≫
      DerivedCategory.Plus.ι.map ((rightDerivedFunctorPlusNatTrans a).app M) =
    (rightDerivedFunctorNatTrans a).app M.obj ≫
      J.rightDerivedFunctorPlusCompatibility.inv.app M := by
    apply (cancel_mono (J.rightDerivedFunctorPlusCompatibility.hom.app M)).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc, ObjectProperty.ι_obj] using
      congrArg (fun t ↦ G.rightDerivedFunctorPlusCompatibility.inv.app M ≫ t) ha
  rw [← Category.assoc, ← Category.assoc, ha']
  simp only [Category.assoc]
  rfl
end Transport
end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (A : Type (u + 1)) [CommRing A]
  {Z T : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]

/-- The etale support kernel used by the canonical comparison unit.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable abbrev etaleSupportKernel :=
  Sheaf.supportedSectionsFunctor T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (Etale.supportRestrictionArrow i)

/-- The support comparison unit is uniquely normalized by the adjunction-unit
map on sections and the kernel inclusion.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: sections identify with evaluation at the final object.  The comparison
adjunction unit commutes with restriction, so it maps the etale support kernel
into the pro-etale kernel.  The kernel universal property gives the map and its
inclusion equation gives uniqueness. -/
theorem supportComparisonUnit_existsUnique :
    ∃! c : etaleSupportKernel A i ⟶
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙ supportSections i A,
      ∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
        c.app F ≫ kernel.ι
          (((comparisonUpperStar (ModuleCat.{u + 1} A) T).obj F).obj.map
            (supportRestrictionArrow i).op) =
        (Sheaf.supportedSectionsInclusion T.smallEtaleTopology
          (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i)).app F ≫
          (((comparisonAdjunction (ModuleCat.{u + 1} A) T).unit.app F).hom.app
            (op (Scheme.Etale.mk (𝟙 T)))) := by
  let c : etaleSupportKernel A i ⟶
      comparisonUpperStar (ModuleCat.{u + 1} A) T ⋙ supportSections i A :=
    (Functor.leftUnitor _).inv ≫
      Functor.whiskerRight (comparisonAdjunction (ModuleCat.{u + 1} A) T).unit
        (etaleSupportKernel A i) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} A) T)
        (supportKernelIdentity A i).hom
  refine ⟨c, ?_, ?_⟩
  · intro F
    dsimp [c, supportKernelIdentity, supportEt, supportPro, supportNu,
      etaleSupportKernel, Sheaf.supportedSectionsFunctor]
    simp only [Category.id_comp, Category.comp_id, kernel.map]
    erw [kernel.lift_ι]
    rfl
  · intro d hd
    apply NatTrans.ext
    funext F
    apply equalizer.hom_ext
    apply (hd F).trans
    dsimp [c, supportKernelIdentity, supportEt, supportPro, supportNu,
      etaleSupportKernel, Sheaf.supportedSectionsFunctor]
    simp only [Category.id_comp, Category.comp_id, kernel.map]
    erw [kernel.lift_ι]
    rfl

/-- The canonical ordinary support comparison unit.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportComparisonUnit :=
  Classical.choose (supportComparisonUnit_existsUnique A i)

/-- The canonical bounded-below derived support comparison induced by the unit.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: apply the right-derived-functor-plus base-change construction to the
unit-normalized ordinary support map, inserting the canonical identity
unitors and the derived-category-plus identity comparison. -/
noncomputable def supportComparison :
    (etaleSupportKernel A i).rightDerivedFunctorPlus ⟶
      (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus ⋙
        (supportSections i A).rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
      (ModuleCat.{u + 1} A))).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange
      (G := etaleSupportKernel A i) (G' := supportSections i A)
      (β := comparisonUpperStar (ModuleCat.{u + 1} A) T)
      (γ := 𝟭 (ModuleCat.{u + 1} A))
      ((Functor.rightUnitor _).hom ≫ supportComparisonUnit A i)

private lemma supportComparisonUnit_formula :
    supportComparisonUnit A i =
      (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (comparisonAdjunction (ModuleCat.{u + 1} A) T).unit
          (etaleSupportKernel A i) ≫
        (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} A) T)
          (supportKernelIdentity A i).hom := by
  apply ((supportComparisonUnit_existsUnique A i).choose_spec.2 _ ?_).symm
  intro F
  dsimp [supportKernelIdentity, supportEt, supportPro, supportNu,
    etaleSupportKernel, Sheaf.supportedSectionsFunctor]
  simp only [Category.id_comp, Category.comp_id, kernel.map]
  erw [kernel.lift_ι]
  rfl

private noncomputable def derivedUnitBaseChange
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    [Abelian C] [Abelian C'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [EnoughInjectives C] [EnoughInjectives C']
    (L : C ⥤ C') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    {G : C ⥤ D} {H : C' ⥤ D} [G.Additive] [H.Additive] (c : G ⟶ L ⋙ H) :
    G.rightDerivedFunctorPlus ⟶ L.mapDerivedCategoryPlus ⋙ H.rightDerivedFunctorPlus :=
  (Functor.rightUnitor _).inv ≫
    (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso D)).inv ≫
    Functor.rightDerivedFunctorPlusBaseChange ((Functor.rightUnitor _).hom ≫ c)

private lemma derivedUnitBaseChange_eq
    {C C' D : Type*} [Category C] [Category C'] [Category D]
    [Abelian C] [Abelian C'] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory C'] [HasDerivedCategory D]
    [EnoughInjectives C] [EnoughInjectives C']
    (L : C ⥤ C') (R : C' ⥤ C) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (G : C ⥤ D) (H : C' ⥤ D) [G.Additive] [H.Additive]
    (adj : L ⊣ R) (e : R ⋙ G ≅ H) (M : DerivedCategory.Plus C) :
    (derivedUnitBaseChange L ((Functor.leftUnitor G).inv ≫
      Functor.whiskerRight adj.unit G ≫ (Functor.associator L R G).hom ≫
        Functor.whiskerLeft L e.hom)).app M =
      G.rightDerivedFunctorPlus.map (adj.derivedPlus.unit.app M) ≫
        (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
          R G _ _ _ _
          (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj)
          e).hom.app (L.mapDerivedCategoryPlus.obj M) := by
  have : R.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms adj
  let c : G ⟶ L ⋙ H :=
    (Functor.leftUnitor G).inv ≫ Functor.whiskerRight adj.unit G ≫
      (Functor.associator L R G).hom ≫ Functor.whiskerLeft L e.hom
  let β := Functor.whiskerRight (NatTrans.mapHomotopyCategoryPlus c)
      DerivedCategory.Plus.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (L ⋙ H))).inv
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft L.mapHomotopyCategoryPlus H.rightDerivedFunctorPlusUnit ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight L.mapDerivedCategoryPlusFactorsh.inv H.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom
  let γ : G.rightDerivedFunctorPlus ⟶ L.mapDerivedCategoryPlus ⋙ H.rightDerivedFunctorPlus :=
    Functor.whiskerRight adj.derivedPlus.unit G.rightDerivedFunctorPlus ≫
      Functor.whiskerLeft L.mapDerivedCategoryPlus
        (Functor.rightDerivedFunctorPlusCompIso' R G e).hom
  have hα : derivedUnitBaseChange L c = Functor.rightDerivedDesc _
      G.rightDerivedFunctorPlusUnit (HomotopyCategory.Plus.quasiIso _) _ β := by
    apply Functor.rightDerived_ext _ G.rightDerivedFunctorPlusUnit
      (HomotopyCategory.Plus.quasiIso _)
    rw [Functor.rightDerived_fac]
    ext K : 2
    simp only [derivedUnitBaseChange, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.rightUnitor_inv_app, Functor.isoWhiskerLeft_inv,
      Functor.whiskerLeft_app]
    erw [Category.id_comp]
    have hn := (Functor.mapDerivedCategoryPlusIdIso D).inv.naturality
      (G.rightDerivedFunctorPlusUnit.app K)
    simp only [Functor.id_map] at hn
    rw [reassoc_of% hn]
    have hf := NatTrans.congr_app
      (Functor.rightDerivedFunctorPlusBaseChange_fac
        ((Functor.rightUnitor _).hom ≫ c)) K
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Category.comp_id] at hf
    rw [hf]
    simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id]
    rw [← Functor.mapDerivedCategoryPlusIdIso_hom_app_factorsh]
    erw [Iso.inv_hom_id_app_assoc]
    dsimp only [β]
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
      Category.comp_id]
    rw [← Functor.map_comp_assoc]
    congr 2
    rw [Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app, Category.id_comp]
    congr 1
    apply NatTrans.ext
    funext X
    simp
  have hγ : Functor.rightDerivedDesc _ G.rightDerivedFunctorPlusUnit
      (HomotopyCategory.Plus.quasiIso _) _ β = γ := by
    apply Functor.rightDerived_ext _ G.rightDerivedFunctorPlusUnit
      (HomotopyCategory.Plus.quasiIso _)
    rw [Functor.rightDerived_fac]
    ext K : 2
    simp only [β, γ, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id]
    have hu : adj.derivedPlus.unit.app (DerivedCategory.Plus.Qh.obj K) =
        DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K) ≫
          R.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj K) ≫
          R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.inv.app K) := by
      rw [← Category.assoc, ← adj.derivedPlus_unit_app_fac, Category.assoc,
        ← Functor.map_comp]
      simp
    rw [hu, Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc]
    have hn := (Functor.rightDerivedFunctorPlusCompIso' R G e).hom.naturality
      (L.mapDerivedCategoryPlusFactorsh.inv.app K)
    simp only [Functor.comp_map] at hn
    dsimp only [Functor.comp_obj] at hn
    rw [hn]
    have hG := G.rightDerivedFunctorPlusUnit.naturality
      (adj.mapHomotopyCategoryPlus.unit.app K)
    simp only [Functor.comp_map] at hG
    rw [← reassoc_of% hG]
    rw [← Functor.rightDerivedFunctorPlusCompUnit_app_assoc]
    have hf := NatTrans.congr_app (Functor.rightDerivedFunctorPlusCompIso'_fac R G e)
      (L.mapHomotopyCategoryPlus.obj K)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hf
    rw [reassoc_of% hf]
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    congr 2
    apply (HomotopyCategory.Plus.ι _).map_injective
    obtain ⟨K, hK⟩ := K
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    simp only [Functor.map_comp, NatTrans.ι_map_mapHomotopyCategoryPlus_app,
      Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app]
    rw [(HomotopyCategory.Plus.ι _).map_id, Category.comp_id]
    change _ = (G.mapHomotopyCategory _).map
        ((HomotopyCategory.Plus.ι _).map
          (adj.mapHomotopyCategoryPlus.unit.app ⟨_, hK⟩)) ≫ _
    rw [Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app]
    dsimp only [Functor.mapHomotopyCategoryPlus, ObjectProperty.lift,
      Functor.comp_obj, ObjectProperty.ι_obj]
    change (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex c _).app P) =
      (G.mapHomotopyCategory _).map
        ((adj.mapHomotopyCategory _).unit.app ((HomotopyCategory.quotient _ _).obj P)) ≫
      (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex e.hom _).app ((L.mapHomologicalComplex _).obj P))
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient,
      Functor.mapHomotopyCategory_map, ← Functor.map_comp]
    congr 1
    ext n
    simp only [c, NatTrans.mapHomologicalComplex_app_f,
      Functor.mapHomologicalComplex_map_f, HomologicalComplex.comp_f,
      Adjunction.mapHomologicalComplex_unit_app_f, NatTrans.comp_app,
      Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp,
      Functor.comp_obj]
    rfl
  have h := NatTrans.congr_app (hα.trans hγ) M
  dsimp only [γ, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app] at h
  exact h


private lemma supportComparison_eq_derivedUnit
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (supportComparison A i).app M =
      (etaleSupportKernel A i).rightDerivedFunctorPlus.map
        ((comparisonAdjunction (ModuleCat.{u + 1} A) T).derivedPlus.unit.app M) ≫
      (@Functor.rightDerivedFunctorPlusCompIso' _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (comparisonLowerStar (ModuleCat.{u + 1} A) T) (etaleSupportKernel A i) _ _ _ _
        (Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
          (comparisonAdjunction (ModuleCat.{u + 1} A) T))
        (supportKernelIdentity A i)).hom.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.obj M) := by
  change (derivedUnitBaseChange
    (comparisonUpperStar (ModuleCat.{u + 1} A) T) (supportComparisonUnit A i)).app M = _
  rw [supportComparisonUnit_formula]
  exact derivedUnitBaseChange_eq _ _ _ _ _ _ M

/-- Under finite algebraically closed field hypotheses this canonical support map
is an isomorphism.
Source: Stacks Tags 099V(2), 099W(2), 09B1(2), 09XP and blueprint
proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: direct image restricts to the etale subsite, so the support kernels are
termwise the same on injective resolutions.  Exact comparison inverse image makes
its right adjoint preserve injectives, and the bounded-below comparison unit is
invertible.  The derived support map is therefore invertible. -/
theorem supportComparison_isIso (k : Type u) [Field k] [IsAlgClosed k]
    [T.Over (Spec (.of k))] [LocallyOfFiniteType (T ↘ Spec (.of k))]
    [QuasiCompact (T ↘ Spec (.of k))] [IsSeparated (T ↘ Spec (.of k))]
    [Finite A] : IsIso (supportComparison A i) := by
  have hu := isIso_compactSupportComparisonUnit T A
  have : IsIso (comparisonAdjunction (ModuleCat.{u + 1} A) T).derivedPlus.unit := by
    rwa [← Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  rw [supportComparison_eq_derivedUnit]
  infer_instance

private lemma supportTerminalEvaluation_eq_res {C : Type*} [Category C]
    (J : GrothendieckTopology C) (D : Type*) [Category D]
    [HasWeakSheafify J D] [HasTerminal C] {V : C} (hV : IsTerminal V)
    (F : Sheaf J D) :
    (Sheaf.ΓNatIsoSheafSections J D hV).hom.app F = F.ΓRes (op V) := by
  simp only [Sheaf.ΓNatIsoSheafSections, Sheaf.ΓRes, Sheaf.coneΓ, Sheaf.ΓHomEquiv,
    Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app]
  dsimp
  erw [Adjunction.homEquiv_counit]
  erw [Adjunction.homEquiv_unit]
  simp [constantSheafAdj, Adjunction.comp_unit_app]

/-- The canonical identification of the global-section kernel with the restriction
kernel used by the support long exact sequence.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: the terminal-evaluation isomorphism identifies global restriction with
restriction from the terminal object. It induces an isomorphism of kernels.
The kernel inclusion determines its forward map and hence the isomorphism uniquely. -/
theorem supportKernelEvaluationIso_existsUnique :
    ∃! e : Etale.supportedEtaleSections A T i.openComplement ≅ etaleSupportKernel A i,
      e.hom ≫ Sheaf.supportedSectionsInclusion T.smallEtaleTopology
        (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i) =
      Etale.supportedEtaleSectionsι A T i.openComplement ≫
        (Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
          (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).hom := by
  let ev := Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
  let a := Etale.supportedEtaleSectionsι A T i.openComplement
  let b := Sheaf.supportedSectionsInclusion T.smallEtaleTopology
    (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i)
  let h : ∀ F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A),
      ev.hom.app F ≫ F.obj.map (Etale.supportRestrictionArrow i).op =
        F.ΓRes (op (Scheme.Etale.mk i.openComplement.ι)) := by
    intro F
    rw [supportTerminalEvaluation_eq_res]
    exact Sheaf.ΓRes_map F _
  let eF (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      (Etale.supportedEtaleSections A T i.openComplement).obj F ≅
        (etaleSupportKernel A i).obj F :=
    PreservesKernel.iso ((evaluation _ _).obj F)
      (Sheaf.natTransΓRes T.smallEtaleTopology (ModuleCat.{u + 1} A)
        (op (Scheme.Etale.mk i.openComplement.ι))) ≪≫
    kernel.mapIso _ (F.obj.map (Etale.supportRestrictionArrow i).op)
      (ev.app F) (Iso.refl _) (by simpa using (h F).symm)
  have eF_ι (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
      (eF F).hom ≫ b.app F = a.app F ≫ ev.hom.app F := by
    change (eF F).hom ≫ kernel.ι _ = (a.app F) ≫ ev.hom.app F
    dsimp [eF, a, Etale.supportedEtaleSectionsι]
    simp only [Category.assoc, kernel.mapIso_hom, kernel.map,
      kernel.lift_ι, PreservesKernel.iso_hom]
    erw [kernelComparison_comp_ι_assoc]
    rfl
  let e : Etale.supportedEtaleSections A T i.openComplement ≅ etaleSupportKernel A i :=
    NatIso.ofComponents eF (by
      intro F G g
      apply equalizer.hom_ext
      change ((Etale.supportedEtaleSections A T i.openComplement).map g ≫
        (eF G).hom) ≫ b.app G = ((eF F).hom ≫ (etaleSupportKernel A i).map g) ≫ b.app G
      rw [Category.assoc, eF_ι, ← Category.assoc, a.naturality,
        Category.assoc, ev.hom.naturality, ← Category.assoc, ← eF_ι,
        Category.assoc]
      exact congrArg (fun t ↦ (eF F).hom ≫ t) (b.naturality g).symm)
  have he : e.hom ≫ b = a ≫ ev.hom := by
    apply NatTrans.ext
    funext F
    exact eF_ι F
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  apply NatTrans.ext
  funext F
  apply equalizer.hom_ext
  exact (NatTrans.congr_app hd F).trans (NatTrans.congr_app he F).symm

/-- The uniquely kernel-normalized terminal-evaluation transport.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportKernelEvaluationIso :=
  Classical.choose (supportKernelEvaluationIso_existsUnique A i)

/-- The existing global-section presentation of the etale support functor.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable abbrev globalEtaleSupportKernel :=
  Etale.supportedEtaleSections A T i.openComplement

/-- The bounded-below comparison viewed in unbounded `D(A)`, using the canonical
compatibility of the two right-derived-functor constructions.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportComparisonUnbounded
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (globalEtaleSupportKernel A i).rightDerivedFunctor.obj M.obj ⟶
      (supportSections i A).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) :=
  (Functor.rightDerivedFunctorNatTrans (supportKernelEvaluationIso A i).hom).app M.obj ≫
    (etaleSupportKernel A i).rightDerivedFunctorPlusCompatibility.inv.app M ≫
    DerivedCategory.Plus.ι.map ((supportComparison A i).app M) ≫
    (supportSections i A).rightDerivedFunctorPlusCompatibility.hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.obj M)

/-- The published inclusion of the ordinary etale support kernel into global sections.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable abbrev etaleSupportForget := Etale.supportedEtaleSectionsι A T i.openComplement

/-- Reuse the published inclusion of pro-etale supported sections.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable abbrev proEtaleSupportForget := supportedModuleSectionsι A i

/-- Terminal evaluation for etale modules, with its explicit additive functor type.
Source: blueprint full-support normalization (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportEtaleGlobalEvaluationIso (T : Scheme.{u}) :
    Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A) ≅
      sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T))) :=
  Sheaf.ΓNatIsoSheafSections T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)

/-- Terminal evaluation for pro-etale modules in the same additive presentation.
Source: blueprint full-support normalization (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportProEtaleGlobalEvaluationIso (T : Scheme.{u}) :
    Sheaf.Γ (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ≅
      sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 T))) :=
  Sheaf.ΓNatIsoSheafSections (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)
    (Scheme.ProEt.isTerminalMkId T)

/-- The specified finite global comparison, in the global-sections presentation.
The only inserted maps are terminal evaluation and D+/unbounded derived compatibility.
Source: blueprint full-support normalization (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportGlobalComparison [Finite A]
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (Sheaf.Γ T.smallEtaleTopology (ModuleCat.{u + 1} A)).rightDerivedFunctor.obj M.obj ⟶
      (Sheaf.Γ (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) :=
  (Functor.rightDerivedFunctorNatTrans
    (supportEtaleGlobalEvaluationIso A T).hom).app M.obj ≫
  (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T)))).rightDerivedFunctorPlusCompatibility.inv.app
      M ≫
  DerivedCategory.Plus.ι.map
    (((Functor.rightUnitor _).inv ≫
      (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
        (ModuleCat.{u + 1} A))).inv ≫ finiteComparisonGlobalSections T A).app M) ≫
  (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
    (evaluation _ _).obj
      (op (Scheme.ProEt.mk (𝟙 T)))).rightDerivedFunctorPlusCompatibility.hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategoryPlus.obj M) ≫
  (Functor.rightDerivedFunctorNatTrans
    (supportProEtaleGlobalEvaluationIso A T).inv).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj)

private lemma rd_comp {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions C]
    {F G H : C ⥤ D} [F.Additive] [G.Additive] [H.Additive]
    (a : F ⟶ G) (b : G ⟶ H) :
    Functor.rightDerivedFunctorNatTrans (a ≫ b) =
      Functor.rightDerivedFunctorNatTrans a ≫ Functor.rightDerivedFunctorNatTrans b := by
  simp [Functor.rightDerivedFunctorNatTrans, NatTrans.mapHomotopyCategory_comp,
    Functor.whiskerRight_comp]

/-- The square for forgetting support commutes with the existing adjunction-unit
comparison of global sections.
Source: Stacks Tags 099W and 09XP; blueprint proof paragraph 1
(blueprint: lem-pur-support-site-comparison).
Proof: compose the ordinary comparison kernel map with its kernel inclusion.
Kernel functoriality gives evaluation of the ordinary comparison unit at `T`.
Apply the right-derived universal property to this commuting square; on
K-injective direct images it is literally the same square in each degree.
The terminal-evaluation transport in `supportGlobalComparison` has this normalization. -/
theorem supportComparison_forget [Finite A]
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    supportComparisonUnbounded A i M ≫
      (Functor.rightDerivedFunctorNatTrans (proEtaleSupportForget A i)).app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) =
    (Functor.rightDerivedFunctorNatTrans (etaleSupportForget A i)).app M.obj ≫
      supportGlobalComparison A (T := T) M := by
  let B := comparisonUpperStar (ModuleCat.{u + 1} A) T
  let a := Sheaf.supportedSectionsInclusion T.smallEtaleTopology
    (ModuleCat.{u + 1} A) (Etale.supportRestrictionArrow i)
  let b : supportSections i A ⟶
      sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 T))) :=
    supportedModuleSectionsToSections A i
  let e : (sheafToPresheaf T.smallEtaleTopology (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op (Scheme.Etale.mk (𝟙 T)))) ⟶
      B ⋙ (sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
        (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 T)))) :=
    (Functor.rightUnitor _).inv ≫ finiteComparisonGlobalSectionsUnit T A
  have hc : supportComparisonUnit A i ≫ Functor.whiskerLeft B b = a ≫ e := by
    apply NatTrans.ext
    funext F
    exact (Classical.choose_spec (supportComparisonUnit_existsUnique A i)).1 F
  have ht := Functor.transportedBC_naturality B (supportComparisonUnit A i) e a b hc M
  have he : Functor.testBC B e = (Functor.rightUnitor _).inv ≫
      (Functor.isoWhiskerLeft _ (Functor.mapDerivedCategoryPlusIdIso
        (ModuleCat.{u + 1} A))).inv ≫ finiteComparisonGlobalSections T A := by
    dsimp only [Functor.testBC, e]
    rw [Iso.hom_inv_id_assoc]
    rfl
  dsimp only [Functor.transportedBC] at ht
  change (_ ≫ DerivedCategory.Plus.ι.map ((supportComparison A i).app M) ≫ _) ≫ _ =
    _ ≫ _ ≫ DerivedCategory.Plus.ι.map ((Functor.testBC B e).app M) ≫ _ at ht
  rw [he] at ht
  have : ((sheafSections (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A)).obj
      (op (Scheme.ProEt.mk (𝟙 T)))).Additive :=
    inferInstanceAs ((sheafToPresheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A) ⋙
      (evaluation _ _).obj (op (Scheme.ProEt.mk (𝟙 T))))).Additive
  have hn := (Classical.choose_spec (supportKernelEvaluationIso_existsUnique A i)).1
  have hp : proEtaleSupportForget A i = b ≫ (supportProEtaleGlobalEvaluationIso A T).inv := rfl
  dsimp only [supportComparisonUnbounded, supportGlobalComparison]
  rw [hp, rd_comp]
  simp only [NatTrans.comp_app, Category.assoc]
  have hn' : (supportKernelEvaluationIso A i).hom ≫ a =
      etaleSupportForget A i ≫ (supportEtaleGlobalEvaluationIso A T).hom := hn
  have hr := NatTrans.congr_app (congrArg Functor.rightDerivedFunctorNatTrans hn') M.obj
  rw [rd_comp, rd_comp] at hr
  simp only [NatTrans.comp_app] at hr
  have ht' := congrArg (fun t ↦
    (Functor.rightDerivedFunctorNatTrans (supportKernelEvaluationIso A i).hom).app M.obj ≫
      t ≫ (Functor.rightDerivedFunctorNatTrans (supportProEtaleGlobalEvaluationIso A T).inv).app
        (B.mapDerivedCategory.obj M.obj)) ht
  simp only [Category.assoc] at ht'
  rw [reassoc_of% hr] at ht'
  simpa only [NatTrans.comp_app, Category.assoc] using ht'

private lemma supportKernelι_isIso_of_eq_zero {D : Type*} [Category D]
    [HasZeroMorphisms D] {V W : D} (f : V ⟶ W) [HasKernel f] (h : f = 0) :
    IsIso (kernel.ι f) := by
  subst f
  infer_instance

/-- With full support, the forgetful maps are isomorphisms. Together with the
preceding square this states that the full-support comparison is exactly the
existing global-sections comparison induced by the adjunction unit.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: the complement of the identity immersion is empty. A module sheaf has zero
sections over the empty scheme, so each restriction kernel is its source and its
kernel inclusion is invertible. Derive these natural isomorphisms. The preceding
square identifies the full-support comparison with the specified global one. -/
theorem fullSupportForget_isIso (T : Scheme.{u}) :
    IsIso (Functor.rightDerivedFunctorNatTrans (etaleSupportForget A (𝟙 T))) ∧
      IsIso (Functor.rightDerivedFunctorNatTrans (proEtaleSupportForget A (𝟙 T))) := by
  have hempty : IsEmpty (𝟙 T : T ⟶ T).openComplement :=
    ⟨fun x ↦ x.2 ⟨x.1, rfl⟩⟩
  have hemptyEt : IsEmpty (Scheme.Etale.mk (𝟙 T : T ⟶ T).openComplement.ι).left :=
    hempty
  have hzero : Sheaf.natTransΓRes T.smallEtaleTopology (ModuleCat.{u + 1} A)
      (op (Scheme.Etale.mk (𝟙 T : T ⟶ T).openComplement.ι)) = 0 := by
    apply NatTrans.ext
    funext F
    exact (Scheme.Etale.isTerminalSectionsOfIsEmpty F
      (Scheme.Etale.mk (𝟙 T : T ⟶ T).openComplement.ι)).isZero.eq_of_tgt _ _
  have he : IsIso (etaleSupportForget A (𝟙 T)) :=
    supportKernelι_isIso_of_eq_zero _ hzero
  have hemptyPro : IsEmpty (Scheme.ProEt.mk (𝟙 T : T ⟶ T).openComplement.ι).left :=
    hempty
  have hp : IsIso (supportedModuleSectionsToSections A (𝟙 T)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro F
    change IsIso (kernel.ι (F.obj.map (supportRestrictionArrow (𝟙 T)).op))
    have hz : F.obj.map (supportRestrictionArrow (𝟙 T)).op = 0 :=
      (Scheme.ProEt.isTerminalSectionsOfIsEmpty F _).isZero.eq_of_tgt _ _
    rw [hz]
    infer_instance
  have hp' : IsIso (proEtaleSupportForget A (𝟙 T)) := by
    dsimp [proEtaleSupportForget, supportedModuleSectionsι]
    infer_instance
  exact ⟨inferInstance, inferInstance⟩

/-- Derive the recorded coefficient pullback comparison before specializing coefficients.
Source: blueprint comparison-pullback clause (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportDerivedCoefficientPullbackIso
    (D : Type v₁) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.upperStar D f).mapDerivedCategory ⋙
        (comparisonUpperStar D X).mapDerivedCategory ≅
      (comparisonUpperStar D Y).mapDerivedCategory ⋙ (upperStar D f).mapDerivedCategory :=
  let e : Etale.upperStar D f ⋙ comparisonUpperStar D X ≅
      comparisonUpperStar D Y ⋙ upperStar D f :=
    supportSiteComparisonCoefficientPullbackIso D f
  (Functor.mapDerivedCategoryCompIso (Etale.upperStar D f)
    (comparisonUpperStar D X)).symm ≪≫
  Functor.mapDerivedCategoryNatIso e ≪≫
  Functor.mapDerivedCategoryCompIso (comparisonUpperStar D Y) (upperStar D f)

/-- Exact coefficient pullback comparison on unbounded derived categories, formed
from the recorded, unit-normalized comparison-pullback isomorphism.
Source: blueprint comparison-pullback clause (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportDerivedPullbackIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory :=
  supportDerivedCoefficientPullbackIso (ModuleCat.{u + 1} A) f

open MonoidalCategory

/-- Apply the existing bifunctor to two isomorphisms without unfolding a
scheme-indexed monoidal instance.
Source: blueprint tensor comparison (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportBifunctorIso
    {C : Type v₁} {D : Type v₂} {E : Type v₃}
    [Category.{w₁} C] [Category.{w₂} D] [Category.{w₃} E]
    (B : C ⥤ D ⥤ E) {M M' : C} {N N' : D} (a : M ≅ M') (b : N ≅ N') :
    (B.obj M).obj N ≅ (B.obj M').obj N' :=
  (B.mapIso a).app N ≪≫ (B.obj M').mapIso b

/-- The canonical derived monoidal comparison, assembled from the general
left-derived tensor comparison and exact/left-derived identifications. Generic
coefficients keep their categorical structures abstract during elaboration.
Source: blueprint specified theta (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportDerivedComparisonTensorIso
    (D : Type v₁) [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [SymmetricCategory D] [MonoidalClosed D]
    [Abelian.HasFunctorialFlatResolution D]
    (T : Scheme.{u}) [(comparisonUpperStar D T).PreservesFlat]
    (K L : DerivedCategory (Sheaf T.smallEtaleTopology D)) :
    (comparisonUpperStar D T).mapDerivedCategory.obj (((Etale.derivedTensor D T).obj K).obj L) ≅
      ((derivedTensor D T).obj ((comparisonUpperStar D T).mapDerivedCategory.obj K)).obj
        ((comparisonUpperStar D T).mapDerivedCategory.obj L) :=
  (comparisonUpperStar D T).leftDerivedFunctorIsoMapDerivedCategory.symm.app
      (((Etale.derivedTensor D T).obj K).obj L) ≪≫
    ((asIso (comparisonUpperStar D T).leftDerivedTensorComparison).app K).app L ≪≫
    supportBifunctorIso (derivedTensor D T)
      ((comparisonUpperStar D T).leftDerivedFunctorIsoMapDerivedCategory.app K)
      ((comparisonUpperStar D T).leftDerivedFunctorIsoMapDerivedCategory.app L)

/-- The specified exterior-product coefficient comparison: tensor comparison followed
by the two canonical comparison-pullback identifications.
Source: blueprint displayed `theta` (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportExteriorCoefficientIso [Finite A]
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g)).mapDerivedCategory.obj
      (Etale.externalProduct (ModuleCat.{u + 1} A) f g K L) ≅
    externalProduct (ModuleCat.{u + 1} A) f g
      ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) (pullback f g)).mapDerivedCategory.mapIso
    (supportBifunctorIso (Etale.derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.fst f g)).app K)
      ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.snd f g)).app L)) ≪≫
  supportDerivedComparisonTensorIso (ModuleCat.{u + 1} A) (pullback f g)
    ((Etale.upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).mapDerivedCategory.obj K)
    ((Etale.upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).mapDerivedCategory.obj L) ≪≫
  supportBifunctorIso (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
    ((supportDerivedPullbackIso A (pullback.fst f g)).app K)
    ((supportDerivedPullbackIso A (pullback.snd f g)).app L) ≪≫
  supportBifunctorIso (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
      (pullback.fst f g)).symm.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K))
    ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
      (pullback.snd f g)).symm.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L)) ≪≫
  eqToIso (supportedExternalProduct_eq A f g
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K)
    ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L))

/-- Compatibility with both supported exterior products in the unbounded derived
category of ordinary modules; the boundedness hypothesis is imposed on the actual
exterior product, rather than implicitly assuming it follows from its inputs.
Source: Stacks Tags 0H9A and 07A4; blueprint proof paragraphs 2--8
(blueprint: lem-pur-support-site-comparison).
Proof: form the quotient of the free constant sheaf by the free sheaf of the
open complement. It represents supported sections by the kernel/cokernel Yoneda
bijection. Its geometric etale stalks are zero or A, hence it is flat; comparison
pullback gives the pro-etale quotient and its flatness without using pro-etale
stalk conservativity. Quotient multiplication identifies the tensor of the two
pulled-back quotients with the product-support quotient. All maps preserve quotient
generators. The exact constant-with-support functors are left adjoint to the actual
unbounded derived support functors. Comparison of supports is the transpose of
the pulled-back counit, since both transposes send a section to its adjunction-unit
image. The exterior product is the transpose of the tensor of the two pulled-back
counits through the generator-normalized product identification. Pullback and tensor
coherence identify that identification in both topologies. Transpose both sides of
the displayed equation under the product-support adjunction. The two comparison
counit identities and monoidal coherence make the transposes equal. Injectivity of
the Hom bijection proves the equation. K-flat localization identifies these maps
with the pairing derived using K-flat tensor and injective support resolutions. -/
theorem supportComparison_exterior [Finite A] (k : Type u) [Field k] [IsAlgClosed k]
    {X Y Z W : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
    [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
    [IsSeparated (X ↘ Spec (.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
    [IsSeparated (Y ↘ Spec (.of k))]
    (i : Z ⟶ X) (j : W ⟶ Y) [IsClosedImmersion i] [IsClosedImmersion j]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (L : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (F : DerivedCategory.Plus
      (Sheaf (pullback (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))).smallEtaleTopology
        (ModuleCat.{u + 1} A)))
    (eF : F.obj ≅ Etale.externalProduct (ModuleCat.{u + 1} A)
      (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) K.obj L.obj) :
    Etale.supportedExteriorProduct A (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j K.obj L.obj ≫
      (globalEtaleSupportKernel A
        (Etale.supportedProductImmersion
          (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j)).rightDerivedFunctor.map
          eF.inv ≫
      supportComparisonUnbounded A
        (Etale.supportedProductImmersion (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j) F ≫
      (supportSections
        (Etale.supportedProductImmersion
          (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j) A).rightDerivedFunctor.map
        ((comparisonUpperStar (ModuleCat.{u + 1} A)
          (pullback (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)))).mapDerivedCategory.map eF.hom ≫
          (supportExteriorCoefficientIso A (X ↘ Spec (.of k)) (Y ↘ Spec (.of k))
            K.obj L.obj).hom) =
    tensorHom (supportComparisonUnbounded A i K) (supportComparisonUnbounded A j L) ≫
      supportedExteriorProductOverField A k (X ↘ Spec (.of k)) (Y ↘ Spec (.of k)) i j
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K.obj)
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj L.obj) := by
  sorry

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry


namespace ProEtale

variable (A : Type (u + 1)) [CommRing A] [Finite A] {C T U : Scheme.{u}}
  [IsLocallyNoetherian T] [IsLocallyNoetherian U]
  (i : C ⟶ T) [IsClosedImmersion i] (v : U ⟶ T) [IsOpenImmersion v]

/-- Pullback of the support quotient, determined by its constant quotient map.
Source: blueprint proof paragraphs 1 and 3 (blueprint: lem-pur-support-site-comparison).
Proof: inverse image takes the free sheaf on an open to the free sheaf on its
inverse image. It preserves the cokernel defining supported constants, and the
inverse image of the complement is the complement of the pulled-back support.
This produces the normalized isomorphism. Its quotient map is epimorphic, so the
normalization determines it at every coefficient module, hence uniquely as a
natural isomorphism. In the pro-etale topology this is also the pullback of the
etale quotient construction through comparison. -/
theorem supportOpenConstantIso_existsUnique :
    ∃! e : supportedCoefficients A i ⋙ upperStar (ModuleCat.{u + 1} A) v ≅
      supportedCoefficients A (pullback.snd i v),
      ∀ M : ModuleCat.{u + 1} A,
        (upperStar (ModuleCat.{u + 1} A) v).map (supportedCoefficientQuotient A i M) ≫
          e.hom.app M =
        (constantSheafCompUpperStarIso (ModuleCat.{u + 1} A) v).hom.app M ≫
          supportedCoefficientQuotient A (pullback.snd i v) M := by
  sorry

/-- The normalized open pullback of the supported constant functor.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportOpenConstantIso :
    supportedCoefficients A i ⋙ upperStar (ModuleCat.{u + 1} A) v ≅
      supportedCoefficients A (pullback.snd i v) :=
  Classical.choose (supportOpenConstantIso_existsUnique A i v)

/-- The exact derived open pullback of the quotient functor.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportOpenDerivedConstantIso :
    (supportedCoefficients A i).mapDerivedCategory ⋙
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory ≅
        (supportedCoefficients A (pullback.snd i v)).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (supportedCoefficients A i)
    (upperStar (ModuleCat.{u + 1} A) v)).symm ≪≫
      Functor.mapDerivedCategoryNatIso (supportOpenConstantIso A i v)

/-- Restriction of derived supported sections to an open: transpose the pulled-back
support counit using the uniquely quotient-normalized base-change identification.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportOpenRestriction
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :=
  (supportedCoefficientDerivedAdjunction A (pullback.snd i v)).homEquiv _ _
    ((supportOpenDerivedConstantIso A i v).inv.app
      ((supportSections i A).rightDerivedFunctor.obj K) ≫
      (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.map
        ((supportedCoefficientDerivedAdjunction A i).counit.app K))

end ProEtale

namespace ProEtale

/-- Open restriction with local Noetherianity supplied by finite type over the field.
Source: blueprint open-restriction clause (blueprint: lem-pur-support-site-comparison). -/
noncomputable def supportOpenRestrictionOverField
    (A : Type (u + 1)) [CommRing A] [Finite A] (k : Type u) [Field k]
    {C T U : Scheme.{u}} [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))]
    (i : C ⟶ T) [IsClosedImmersion i] (v : U ⟶ T) [IsOpenImmersion v]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} A))) :=
  letI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian (T ↘ Spec (.of k))
  letI : IsLocallyNoetherian U := LocallyOfFiniteType.isLocallyNoetherian v
  supportOpenRestriction A i v K

/-- The comparison commutes with canonical restriction to every open, with the
specified comparison-pullback coefficient transport on the restricted object.
Source: blueprint proof paragraph 1 (blueprint: lem-pur-support-site-comparison).
Proof: restriction commutes with the support kernel because both maps restrict
the same sections. Open restriction preserves K-injectives: its extension-by-zero
left adjoint is exact in each topology. Thus on restricted K-injective direct
images the same kernel square computes the derived restriction square. The
comparison unit commutes with this square by adjunction, since both restricted
units are transposes of the identity. The pro-etale quotient-normalized transpose
is this same restriction map by the support adjunction. The etale arrow reuses
`Etale.derivedSupportOpenRestriction`,
normalized by ordinary kernel restriction and the derived-composition unit.
Therefore the two paths are equal, with exactly the canonical pullback coefficient
identification displayed on the last map. -/
theorem supportComparison_open (A : Type (u + 1)) [CommRing A] [Finite A]
    (k : Type u) [Field k] [IsAlgClosed k]
    {C T : Scheme.{u}} [T.Over (Spec (.of k))]
    [LocallyOfFiniteType (T ↘ Spec (.of k))] [QuasiCompact (T ↘ Spec (.of k))]
    [IsSeparated (T ↘ Spec (.of k))]
    (i : C ⟶ T) [IsClosedImmersion i] (U : T.Opens)
    (M : DerivedCategory.Plus (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    supportComparisonUnbounded A i M ≫
      supportOpenRestrictionOverField A k i U.ι
        ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.obj M.obj) =
    (Etale.derivedSupportOpenRestriction A i U).app M.obj ≫
      supportComparisonUnbounded A (pullback.snd i U.ι)
        ((Etale.upperStar (ModuleCat.{u + 1} A) U.ι).mapDerivedCategoryPlus.obj M) ≫
      (supportSections (pullback.snd i U.ι) A).rightDerivedFunctor.map
        ((supportDerivedPullbackIso A U.ι).hom.app M.obj) := by
  sorry

end ProEtale
end AlgebraicGeometry
