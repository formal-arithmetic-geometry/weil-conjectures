/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.FiniteComparisonClassAdjunction
import all WeilConjectures.AlgebraicGeometry.SpDirectImageEtaleMate
import WeilConjectures.AlgebraicGeometry.EtaleProEtaleScalarMateData
import all WeilConjectures.AlgebraicGeometry.EtaleProEtaleScalarPullbackCube
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CommIsoComp
import all WeilConjectures.AlgebraicGeometry.ProEtaleFixedScalarRestrictionDirectImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleRingSheafChangeAdjunctionSupplement

/-! # Restriction and the bounded direct-image site boundary

Source: Stacks 09AF, 099R and 0D6E.
(blueprint: lem-sf-proper-restriction-site-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace CategoryTheory.Functor

private theorem compatibility_unit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (I : HomotopyCategory.Plus C) :
    (F.rightDerivedFunctorPlusUnit.app I).hom ≫
        F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj I) =
      F.rightDerivedFunctorUnit.app I.obj := by
  simpa only [Functor.rightDerivedFunctorPlusCompatibility,
    Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
    Functor.rightDerivedFunctorPlusιUnit, Functor.ιRightDerivedFunctorUnit,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    DerivedCategory.Plus.ι, HomotopyCategory.Plus.ι,
    ObjectProperty.ι_map, ObjectProperty.ι_obj] using
    Functor.rightDerivedNatTrans_app
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
      (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor)
      F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
      (HomotopyCategory.Plus.quasiIso C) (𝟙 _) I

private theorem normalized_plus_compatibility
    {C D E V : Type*} [Category C] [Category D] [Category E] [Category V]
    [Abelian C] [Abelian D] [Abelian E] [Abelian V]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory V]
    [EnoughInjectives C] [EnoughInjectives E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions E]
    (F : C ⥤ D) (G : E ⥤ V) (x : C ⥤ E) (y : D ⥤ V)
    [F.Additive] [G.Additive] [x.Additive] [y.Additive]
    [Limits.PreservesFiniteLimits x] [Limits.PreservesFiniteColimits x]
    [Limits.PreservesFiniteLimits y] [Limits.PreservesFiniteColimits y]
    (c : F ⋙ y ⟶ x ⋙ G)
    (b : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ⟶
      x.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (hb : ∀ I : HomotopyCategory C (.up ℤ),
      y.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app I) ≫
          b.app (DerivedCategory.Qh.obj I) ≫
          G.rightDerivedFunctor.map (x.mapDerivedCategoryFactorsh.hom.app I) =
        y.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory c (.up ℤ)).app I) ≫
          G.rightDerivedFunctorUnit.app ((x.mapHomotopyCategory (.up ℤ)).obj I))
    (L : DerivedCategory.Plus C) :
    y.mapDerivedCategory.map (F.rightDerivedFunctorPlusCompatibility.hom.app L) ≫
        b.app L.obj =
      ((Functor.rightDerivedFunctorPlusBaseChange c).app L).hom ≫
        G.rightDerivedFunctorPlusCompatibility.hom.app (x.mapDerivedCategoryPlus.obj L) := by
  let left := Functor.whiskerRight F.rightDerivedFunctorPlusCompatibility.hom
      y.mapDerivedCategory ≫ Functor.whiskerLeft DerivedCategory.Plus.ι b
  let right := Functor.whiskerRight (Functor.rightDerivedFunctorPlusBaseChange c)
      DerivedCategory.Plus.ι ≫
    Functor.whiskerLeft x.mapDerivedCategoryPlus G.rightDerivedFunctorPlusCompatibility.hom
  have he : left = right := by
    apply Functor.rightDerived_ext
      (F.rightDerivedFunctorPlus ⋙ y.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι)
      (Functor.whiskerRight F.rightDerivedFunctorPlusUnit
        (y.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι) ≫
        (Functor.associator _ _ _).hom)
      (HomotopyCategory.Plus.quasiIso C)
    apply NatTrans.ext
    funext I
    simp only [left, right, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
      Functor.associator_hom_app, Category.id_comp, Category.assoc]
    erw [← y.mapDerivedCategory.map_comp_assoc, compatibility_unit]
    have h := hb I.obj
    have hf := congrArg (fun t ↦ t.hom)
      (congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac c) I)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Category.comp_id,
      ObjectProperty.FullSubcategory.comp_hom] at hf
    apply (cancel_mono (G.rightDerivedFunctor.map
      (x.mapDerivedCategoryFactorsh.hom.app I.obj))).mp
    simp only [Category.assoc]
    erw [h]
    erw [reassoc_of% hf]
    simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
    simp only [ObjectProperty.FullSubcategory.id_hom,
      Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
      Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app,
      CategoryTheory.Functor.map_id, Category.id_comp]
    have hn := G.rightDerivedFunctorPlusCompatibility.hom.naturality
      (x.mapDerivedCategoryPlusFactorsh.inv.app I)
    dsimp only [Functor.comp_map, DerivedCategory.Plus.ι, ObjectProperty.ι_map] at hn
    erw [reassoc_of% hn]
    erw [← G.rightDerivedFunctor.map_comp]
    have hi : (x.mapDerivedCategoryPlusFactorsh.inv.app I).hom ≫
        x.mapDerivedCategoryFactorsh.hom.app I.obj = 𝟙 _ := by
      erw [← x.ι_map_mapDerivedCategoryPlusFactorsh_hom_app I]
      exact congrArg (fun t ↦ t.hom) (x.mapDerivedCategoryPlusFactorsh.inv_hom_id_app I)
    rw [hi]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
    repeat' erw [Category.id_comp]
    erw [compatibility_unit]
    erw [← y.ι_map_mapDerivedCategoryPlusFactorsh_hom_app
      (F.mapHomotopyCategoryPlus.obj I)]
    rfl
  exact congr_app he L

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

private theorem mate_whisker_top
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G G' : C ⥤ E} {H : D ⥤ F}
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (w : TwoSquare G' L₁ L₂ H) (t : G ⟶ G') :
    mateEquiv a₁ a₂ (w.whiskerTop t) = (mateEquiv a₁ a₂ w).whiskerRight t := by
  simpa [TwoSquare.whiskerBottom, TwoSquare.whiskerLeft] using
    mateEquiv_whiskerTop_whiskerBottom a₁ a₂ w t (𝟙 H)

private theorem right_mate_cube
    {CA DA CB DB EA FA EB FB : Type*}
    [Category CA] [Category DA] [Category CB] [Category DB]
    [Category EA] [Category FA] [Category EB] [Category FB]
    {LA : CA ⥤ DA} {RA : DA ⥤ CA} {LB : CB ⥤ DB} {RB : DB ⥤ CB}
    {LA' : EA ⥤ FA} {RA' : FA ⥤ EA} {LB' : EB ⥤ FB} {RB' : FB ⥤ EB}
    (aA : LA ⊣ RA) (aB : LB ⊣ RB) (bA : LA' ⊣ RA') (bB : LB' ⊣ RB')
    {U : CB ⥤ CA} {V : DB ⥤ DA} {U' : EB ⥤ EA} {V' : FB ⥤ FA}
    {GA : CA ⥤ EA} {HA : DA ⥤ FA} {GB : CB ⥤ EB} {HB : DB ⥤ FB}
    (aa : TwoSquare GA LA LA' HA) (ab : TwoSquare GB LB LB' HB)
    (k : TwoSquare U LB LA V) (i : TwoSquare U' LB' LA' V')
    (t : U ⋙ GA ⟶ GB ⋙ U') (s : V ⋙ HA ⟶ HB ⋙ V')
    (h : ∀ N : CB,
    LA'.map (t.app N) ≫ i.app (GB.obj N) ≫ V'.map (ab.app N) =
      aa.app (U.obj N) ≫ HA.map (k.app N) ≫ s.app (LB.obj N))
    (M : DB) :
      t.app (RB.obj M) ≫ U'.map ((mateEquiv aB bB ab).app M) ≫
          (mateEquiv bB bA i).app (HB.obj M) =
        GA.map ((mateEquiv aB aA k).app M) ≫
          (mateEquiv aA bA aa).app (V.obj M) ≫ RA'.map (s.app M) := by
  have hc : (ab.hComp i).whiskerTop t = (k.hComp aa).whiskerBottom s := by
    ext N
    simpa only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using h N
  have hm := congrArg (mateEquiv aB bA) hc
  rw [mate_whisker_top, mateEquiv_whiskerBottom,
    mateEquiv_vcomp aB bB bA, mateEquiv_vcomp aB aA bA] at hm
  simpa only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using
    congrArg (fun w ↦ w.natTrans.app M) hm

private theorem ambient_restriction_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (p : X ⟶ Y)
    (M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (pbcDerivedComparisonRestrict Y φ).inv.app
        ((Etale.lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctor.obj M) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
        ((directImageComparisonAmbient B p).app M) ≫
      (fixedScalarRestrictionDirectImageMap φ p).app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj M) =
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        ((Etale.scalarRestrictionDirectImageMap φ p).app M) ≫
      (directImageComparisonAmbient A p).app
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj M) ≫
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
        ((pbcDerivedComparisonRestrict X φ).inv.app M) := by
  have h := right_mate_cube
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p)
    (TwoSquare.mk _ _ _ _ (directImageComparisonAmbientPullbackIso A p).hom)
    (TwoSquare.mk _ _ _ _ (directImageComparisonAmbientPullbackIso B p).hom)
    (TwoSquare.mk _ _ _ _ (Etale.scalarRestrictionPullbackIso φ p).hom)
    (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarRestrictScalarsIso φ p).hom)
    (pbcDerivedComparisonRestrict Y φ).inv (pbcDerivedComparisonRestrict X φ).inv
    (derived_restriction_cube φ p) M
  simpa only [directImageComparisonAmbient, fixedScalarRestrictionDirectImageMap,
    fixedScalarRestrictionPullback, Etale.scalarRestrictionDirectImageMap] using h



private theorem direct_boundary_normalization
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (fixedDirectImageComparisonIso A p).hom.app L =
      (directImageComparisonAmbient A p).app L.obj := by
  have h := sp_comparison_hom A p L.obj L.property
  have hh : (spDirectImageComparisonIso A p L.obj L.property).hom =
      (directImageComparisonAmbient A p).app L.obj := by
    simpa only [BoundaryComparison.directImageMate, BoundaryComparison.pullbackSquare,
      directImageComparisonAmbient, directImageComparisonAmbientPullbackIso,
      leftDerivedUpperStarIsoMapDerivedCategory, Etale.leftDerivedUpperStarIsoMapDerivedCategory,
      BoundaryComparison.comparison, TwoSquare.mk, TwoSquare.natTrans] using h
  rw [← hh]
  simp only [fixedDirectImageComparisonIso, spDirectImageComparisonIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.mapIso_hom,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app]
  rfl

private theorem etale_restriction_iso_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Etale.upperStarRestrictScalarsIso φ p = Etale.upperStarRestrictScalarsIsoSheaf φ p := by
  let a := (Sheaf.restrictCoextendScalarsAdj Y.smallEtaleTopology φ).comp
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
  let b := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p).comp
    (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ)
  apply Iso.ext
  apply (conjugateEquiv b a).injective
  rw [Etale.conjugateEquiv_upperStarRestrictScalarsIso_hom]
  exact (congrArg Iso.inv ((conjugateIsoEquiv a b).apply_symm_apply (Iso.refl _))).symm

private theorem etale_restriction_derived_adj_eq
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p =
      (Adjunction.mapDerivedCategoryRightDerivedAdjunction
        (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)).ofNatIsoLeft
          (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p).symm := by
  exact Adjunction.derived_eq_ofNatIsoLeft
    ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p).mapHomotopyCategory (.up ℤ))
    (HomotopyCategory.quasiIso _ _) (HomotopyCategory.quasiIso _ _)
    (Etale.upperStar (ModuleCat.{u + 1} A) p).leftDerivedFunctorCounit
    (Etale.upperStar (ModuleCat.{u + 1} A) p).mapDerivedCategoryFactorsh.hom
    (Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorUnit
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) p)
    (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac
      (Etale.upperStar (ModuleCat.{u + 1} A) p)).symm

private theorem etale_restriction_mate_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    Etale.scalarRestrictionDirectImageMap φ p =
      (mateEquiv
        (Adjunction.mapDerivedCategoryRightDerivedAdjunction
          (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p))
        (Adjunction.mapDerivedCategoryRightDerivedAdjunction
          (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p))
        (TwoSquare.mk _ _ _ _
          (Functor.mapDerivedCategorySquareIso
            (Etale.upperStarRestrictScalarsIsoSheaf φ p)).hom)).natTrans := by
  unfold Etale.scalarRestrictionDirectImageMap
  rw [etale_restriction_derived_adj_eq, etale_restriction_derived_adj_eq]
  refine (mate_left_iso _ _ _ _ (Etale.scalarRestrictionPullbackIso φ p).hom).trans ?_
  congr 2
  ext K
  simp only [Etale.scalarRestrictionPullbackIso,
    Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem etale_restriction_ordinary_mate
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (p : X ⟶ Y) :
    (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p)
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (TwoSquare.mk _ _ _ _ (Etale.upperStarRestrictScalarsIsoSheaf φ p).hom)).natTrans =
        (Etale.lowerStarCompRestrictScalarsIso φ p).hom := by
  rw [← etale_restriction_iso_eq]
  change (mateEquiv _ _ ((mateEquiv _ _).symm _)).natTrans = _
  rw [Equiv.apply_symm_apply]

private theorem etale_restriction_plus_normalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Y : Scheme.{u}} (p : X ⟶ Y)
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (Sheaf.restrictScalars Y.smallEtaleTopology φ).mapDerivedCategory.map
        ((Etale.lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctorPlusCompatibility.hom.app L)
      ≫ (Etale.scalarRestrictionDirectImageMap φ p).app L.obj =
    ((Etale.rightDerivedLowerStarRestrictScalars φ p).app L).hom ≫
      (Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) := by
  apply Functor.normalized_plus_compatibility
    (Etale.lowerStar (ModuleCat.{u + 1} B) p)
    (Etale.lowerStar (ModuleCat.{u + 1} A) p)
    (Sheaf.restrictScalars X.smallEtaleTopology φ)
    (Sheaf.restrictScalars Y.smallEtaleTopology φ)
    (Etale.lowerStarCompRestrictScalarsIso φ p).hom
  intro I
  rw [etale_restriction_mate_eq]
  have h := derived_mate_factorsh
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) p)
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
    (Etale.upperStarRestrictScalarsIsoSheaf φ p) I
  rw [etale_restriction_ordinary_mate] at h
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryCompIso_refl_inv_app] at h
  erw [Category.id_comp] at h
  exact h

/-- The direct-image site boundary with its output in the bounded etale category.
Source: Stacks 09AF and 099R
(blueprint: lem-sf-proper-restriction-site-square). -/
def properRestrictionSiteBoundary (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (p : X ⟶ Y) [QuasiCompact p] [QuasiSeparated p] :
    (DerivedCategory.Plus.ι ⋙
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory) ⋙
        (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor ≅
    (Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlus ⋙
      (DerivedCategory.Plus.ι ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory) :=
  (fixedDirectImageComparisonIso A p).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctorPlusCompatibility.symm _

private theorem reverse_hexagon
    {C : Type*} [Category C] {V₀ V₁ V₂ V₃ V₄ V₅ : C}
    (a : V₀ ≅ V₁) (b : V₁ ≅ V₂) (c : V₂ ≅ V₃)
    (d : V₀ ≅ V₄) (e : V₄ ≅ V₅) (f : V₅ ≅ V₃)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ f.hom) :
    f.hom ≫ c.inv ≫ b.inv = e.inv ≫ d.inv ≫ a.hom := by
  apply (cancel_epi (d.hom ≫ e.hom)).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← reassoc_of% h]
  simp only [Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

private theorem proper_forward_cube
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (p : X ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (pbcDerivedComparisonRestrict Y φ).inv.app
        ((Etale.lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctorPlus.obj L).obj ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
        ((properRestrictionSiteBoundary B p).inv.app L) ≫
      (fixedScalarRestrictionDirectImageMap φ p).app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj L.obj) =
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        (((Etale.rightDerivedLowerStarRestrictScalars φ p).app L).hom) ≫
      (properRestrictionSiteBoundary A p).inv.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) ≫
      (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
        ((pbcDerivedComparisonRestrict X φ).inv.app L.obj) := by
  simp only [properRestrictionSiteBoundary, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, NatTrans.comp_app,
    direct_boundary_normalization, Functor.map_comp, Category.assoc]
  have hd := (pbcDerivedComparisonRestrict Y φ).inv.naturality
    ((Etale.lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctorPlusCompatibility.hom.app L)
  dsimp only [Functor.comp_map] at hd
  erw [← reassoc_of% hd, ambient_restriction_cube]
  erw [← Functor.map_comp_assoc, etale_restriction_plus_normalization]
  simp only [Functor.map_comp, Category.assoc]
  rfl

/-- Scalar restriction respects the specified direct-image site boundary.
Source: Stacks 09AF, 099R and 0D6E
(blueprint: lem-sf-proper-restriction-site-square).

Proof: on ordinary sheaves, the comparison restriction functor commutes sectionwise
with geometric direct image and coefficient coextension. Conjugating that literal
identity gives the cube for comparison inverse image, geometric inverse image and
scalar restriction. Descend the exact cube to derived categories and take the
geometric adjunction mates. Mate pasting identifies its four faces with the
specified geometric restriction mates and the comparison direct-image mates.
On bounded-below complexes, the latter are the fixed counit-normalized site
comparisons. Insert the right-derived D-plus inclusion comparisons. The
K-injective resolution normalization of the etale restriction comparison agrees
with its mate, so these insertions give exactly the displayed equation. No
preservation of K-injective complexes by scalar restriction is assumed. -/
theorem properRestriction_site_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (p : X ⟶ Y)
    [QuasiCompact p] [QuasiSeparated p]
    (L : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))) :
    (lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.map
        ((pbcDerivedComparisonRestrict X φ).inv.app L.obj) ≫
      (fixedScalarRestrictionDirectImage φ p).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj L.obj) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).map
        ((properRestrictionSiteBoundary B p).hom.app L) =
    (properRestrictionSiteBoundary A p).hom.app
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.map
        (((asIso (Etale.rightDerivedLowerStarRestrictScalars φ p)).inv.app L).hom) ≫
      (pbcDerivedComparisonRestrict Y φ).inv.app
        ((Etale.lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctorPlus.obj L).obj := by
  have h := reverse_hexagon
    ((pbcDerivedComparisonRestrict Y φ).symm.app
      ((Etale.lowerStar (ModuleCat.{u + 1} B) p).rightDerivedFunctorPlus.obj L).obj)
    ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).mapIso
      ((properRestrictionSiteBoundary B p).symm.app L))
    ((fixedScalarRestrictionDirectImage φ p).symm.app
      ((comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory.obj L.obj))
    ((comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.mapIso
      (DerivedCategory.Plus.ι.mapIso
        ((asIso (Etale.rightDerivedLowerStarRestrictScalars φ p)).app L)))
    ((properRestrictionSiteBoundary A p).symm.app
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj L))
    ((lowerStar (ModuleCat.{u + 1} A) p).rightDerivedFunctor.mapIso
      ((pbcDerivedComparisonRestrict X φ).symm.app L.obj))
    (proper_forward_cube φ p L)
  simpa only [Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, ObjectProperty.ι_map] using h


end AlgebraicGeometry.ProEtale
