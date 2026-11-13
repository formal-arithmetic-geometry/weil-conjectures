/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SfP1IntegralTransportData

/-! # Geometric isomorphism cancellation normalizes the derived unit.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 015F](https://stacks.math.columbia.edu/tag/015F)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale.SfP1Transport

private theorem map_homotopy_obj_as
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive] (E : CochainComplex C ℤ) :
    ((F.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient C (.up ℤ)).obj E)).as =
        (F.mapHomologicalComplex (.up ℤ)).obj E := rfl

private theorem homotopy_unit_comp
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [(HomotopyCategory.quotient C (.up ℤ)).IsLocalization
      (HomologicalComplex.homotopyEquivalences C (.up ℤ))]
    [(HomotopyCategory.quotient D (.up ℤ)).IsLocalization
      (HomologicalComplex.homotopyEquivalences D (.up ℤ))]
    {L : C ⥤ D} {R V : D ⥤ C} [L.Additive] [R.Additive] [V.Additive]
    (a : L ⊣ R) (g : V ≅ R) (c : L ⋙ V ≅ 𝟭 C)
    (h : ∀ M, a.unit.app M ≫ g.inv.app (L.obj M) ≫ c.hom.app M = 𝟙 M)
    (M : HomotopyCategory C (.up ℤ)) :
    (a.mapHomotopyCategory (.up ℤ)).unit.app M ≫
      (NatTrans.mapHomotopyCategory g.inv (.up ℤ)).app
        ((L.mapHomotopyCategory (.up ℤ)).obj M) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ V)) (.up ℤ)).hom.app M ≫
      (NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app M ≫
      (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app M = 𝟙 M := by
  obtain ⟨E, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryIdIso_hom_app_eq_id]
  erw [Category.id_comp, Category.comp_id]
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  simp only [NatTrans.mapHomotopyCategory_app, map_homotopy_obj_as,
    HomotopyCategory.quotient_obj_as]
  change (HomotopyCategory.quotient _ (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient _ (.up ℤ)).map _ ≫
    (HomotopyCategory.quotient _ (.up ℤ)).map _ = _
  rw [← Functor.map_comp, ← Functor.map_comp,
    ← (HomotopyCategory.quotient _ (.up ℤ)).map_id]
  congr 1
  ext n : 1
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f,
    Adjunction.mapHomologicalComplex_unit_app_f, NatTrans.mapHomologicalComplex_app_f]
  change a.unit.app (E.X n) ≫ g.inv.app (L.obj (E.X n)) ≫ c.hom.app (E.X n) = 𝟙 _
  exact h (E.X n)

private theorem ordinary_unit_comp
    (A : Type (u + 1)) [CommRing A]
    {S X : Scheme.{u}} (i : X ≅ S)
    (M : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i.hom).unit.app M ≫
      (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} A) i).inv.app
        ((upperStar (ModuleCat.{u + 1} A) i.hom).obj M) ≫
      (upperStarComp (ModuleCat.{u + 1} A) i.inv i.hom (𝟙 S) (by simp)).inv.app M ≫
      (upperStarId (ModuleCat.{u + 1} A) S).hom.app M = 𝟙 M := by
  let B := ModuleCat.{u + 1} A
  let L := upperStar B i.hom
  let R := lowerStar B i.hom
  let V := upperStar B i.inv
  let U := lowerStar B i.inv
  let a := upperStarLowerStarAdjunction B i.hom
  let b := upperStarLowerStarAdjunction B i.inv
  let e := (lowerStarEquivalenceOfIso B i).toAdjunction
  let c := (upperStarComp B i.inv i.hom (𝟙 S) (by simp)).symm ≪≫ upperStarId B S
  let p := lowerStarComp B i.inv i.hom (𝟙 S) (by simp)
  have hg : (upperStarInvIsoLowerStarHom B i).inv.app (L.obj M) =
      R.map (b.unit.app (L.obj M)) ≫ e.counit.app (V.obj (L.obj M)) := by
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app e b (L.obj M)
    change e.homEquiv _ _ ((upperStarInvIsoLowerStarHom B i).inv.app (L.obj M)) = _ at h
    exact (e.homEquiv _ _).eq_symm_apply.mpr h
  change a.unit.app M ≫ (upperStarInvIsoLowerStarHom B i).inv.app (L.obj M) ≫
    c.hom.app M = 𝟙 M
  rw [hg]
  have hn := e.counit.naturality (c.hom.app M)
  change (U ⋙ R).map (c.hom.app M) ≫ e.counit.app M =
    e.counit.app (V.obj (L.obj M)) ≫ c.hom.app M at hn
  rw [Category.assoc, ← hn]
  change a.unit.app M ≫ (R.map (b.unit.app (L.obj M)) ≫
    (U ⋙ R).map (c.hom.app M) ≫ p.hom.app M ≫ (lowerStarId B S).hom.app M) = _
  have hp := p.hom.naturality (c.hom.app M)
  change (U ⋙ R).map (c.hom.app M) ≫ p.hom.app M =
    p.hom.app (V.obj (L.obj M)) ≫ (lowerStar B (𝟙 S)).map (c.hom.app M) at hp
  simp only [Functor.comp_map]
  rw [reassoc_of% hp]
  have hc := upperStarComp_hom_app_unit_app B i.inv i.hom M (𝟙 S) (by simp)
  change (upperStarLowerStarAdjunction B (𝟙 S)).unit.app M ≫
    (lowerStar B (𝟙 S)).map _ =
      (a.unit.app M ≫ R.map (b.unit.app (L.obj M))) ≫ p.hom.app _ at hc
  rw [← Category.assoc, ← Category.assoc, ← hc]
  simp only [c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc, upperStarId_hom_app_unit_app, Iso.inv_hom_id_app]
  rfl

private theorem derived_unit_comp
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R V : D ⥤ C} [L.Additive] [R.Additive] [V.Additive]
    [Limits.PreservesFiniteLimits L] [Limits.PreservesFiniteColimits L]
    [Limits.PreservesFiniteLimits R] [Limits.PreservesFiniteColimits R]
    [Limits.PreservesFiniteLimits V] [Limits.PreservesFiniteColimits V]
    (ηh : 𝟭 (HomotopyCategory C (.up ℤ)) ⟶
      L.mapHomotopyCategory (.up ℤ) ⋙ R.mapHomotopyCategory (.up ℤ))
    (η : 𝟭 (DerivedCategory C) ⟶ L.mapDerivedCategory ⋙ R.mapDerivedCategory)
    (g : V ≅ R) (c : L ⋙ V ≅ 𝟭 C)
    (hη : ∀ M, η.app (DerivedCategory.Qh.obj M) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app M) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj M) =
        DerivedCategory.Qh.map (ηh.app M))
    (hh : ∀ M, ηh.app M ≫
      (NatTrans.mapHomotopyCategory g.inv (.up ℤ)).app
        ((L.mapHomotopyCategory (.up ℤ)).obj M) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ V)) (.up ℤ)).hom.app M ≫
      (NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app M ≫
      (Functor.mapHomotopyCategoryIdIso _ (.up ℤ)).hom.app M = 𝟙 M)
    (K : DerivedCategory C) :
    η.app K ≫ (Functor.mapDerivedCategoryNatIso g.symm).hom.app
        (L.mapDerivedCategory.obj K) ≫
      (Functor.mapDerivedCategoryCompIso L V).hom.app K ≫
      (Functor.mapDerivedCategoryNatIso c).hom.app K ≫
      (Functor.mapDerivedCategoryIdIso C).hom.app K = 𝟙 K := by
  have h : η ≫
      Functor.whiskerLeft L.mapDerivedCategory (Functor.mapDerivedCategoryNatIso g.symm).hom ≫
      (Functor.mapDerivedCategoryCompIso L V).hom ≫
      (Functor.mapDerivedCategoryNatIso c).hom ≫
      (Functor.mapDerivedCategoryIdIso _).hom = 𝟙 _ := by
    apply Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso _ (.up ℤ))
    intro M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, NatTrans.id_app]
    have hid := NatTrans.congr_app
      (congrArg Iso.hom (Functor.mapDerivedCategoryIdIso_factorsh
        C)) M
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app] at hid
    erw [Category.comp_id, Category.comp_id] at hid
    rw [hid, Functor.mapDerivedCategoryNatIso_fach_assoc]
    have hc := Functor.mapDerivedCategoryCompIso_fach L V M
    have hc' : (Functor.mapDerivedCategoryCompIso L V).hom.app
        (DerivedCategory.Qh.obj M) ≫ (L ⋙ V).mapDerivedCategoryFactorsh.hom.app M =
      V.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app M) ≫
        V.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (L ⋙ V)) (.up ℤ)).hom.app M) := by
      rw [← hc, Iso.hom_inv_id_app_assoc]
    rw [reassoc_of% hc', ← (Functor.mapDerivedCategoryNatIso g.symm).hom.naturality_assoc,
      Functor.mapDerivedCategoryNatIso_fach_assoc,
      reassoc_of% (hη M)]
    simp only [← Functor.map_comp]
    calc
      _ = DerivedCategory.Qh.map (𝟙 M) := by
        simpa only [Iso.symm_hom] using congrArg DerivedCategory.Qh.map (hh M)
      _ = 𝟙 _ := DerivedCategory.Qh.map_id M
  exact NatTrans.congr_app h K

private theorem exact_unit_comp
    (A : Type (u + 1)) [CommRing A]
    {S X : Scheme.{u}} (i : X ≅ S)
    [CategoryTheory.Limits.PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) i.hom)]
    (K : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i.hom).mapDerivedCategoryAdjunction.unit.app
        K ≫
      (Functor.mapDerivedCategoryNatIso
        (upperStarInvIsoLowerStarHom (ModuleCat.{u + 1} A) i).symm).hom.app
          ((upperStar (ModuleCat.{u + 1} A) i.hom).mapDerivedCategory.obj K) ≫
      (Functor.mapDerivedCategoryCompIso (upperStar (ModuleCat.{u + 1} A) i.hom)
        (upperStar (ModuleCat.{u + 1} A) i.inv)).hom.app K ≫
      (Functor.mapDerivedCategoryNatIso
        ((upperStarComp (ModuleCat.{u + 1} A) i.inv i.hom (𝟙 S) (by simp)).symm ≪≫
          upperStarId (ModuleCat.{u + 1} A) S)).hom.app K ≫
      (Functor.mapDerivedCategoryIdIso _).hom.app K = 𝟙 K := by
  let B := ModuleCat.{u + 1} A
  let a := upperStarLowerStarAdjunction B i.hom
  let g := upperStarInvIsoLowerStarHom B i
  let c := (upperStarComp B i.inv i.hom (𝟙 S) (by simp)).symm ≪≫ upperStarId B S
  refine derived_unit_comp (a.mapHomotopyCategory (.up ℤ)).unit
    a.mapDerivedCategoryAdjunction.unit g c ?_ ?_ K
  · exact fun M ↦ a.mapDerivedCategoryAdjunction_unit_app_fac M
  · intro M
    apply homotopy_unit_comp a g c
    intro N
    simpa only [c, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc] using
      ordinary_unit_comp A i N

/-- The concrete geometric cancellation `pushPull` is inverse to the canonical derived unit. -/
theorem unit_comp_pushPull
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {S X : Scheme.{u}} (i : X ≅ ProjectiveLine S)
    (K : DerivedCategoryModule A (ProjectiveLine S)) :
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) i.hom).unit.app K ≫
        (pushPull A i).hom.app K = 𝟙 K := by
  let B := ModuleCat.{u + 1} A
  let : CategoryTheory.Limits.PreservesFiniteColimits (lowerStar B i.hom) :=
    CategoryTheory.Limits.preservesFiniteColimits_of_natIso (upperStarInvIsoLowerStarHom B i)
  have h := exact_unit_comp A i K
  simp only [Adjunction.mapDerivedCategoryAdjunction, Adjunction.ofNatIsoRight_unit,
    Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc] at h
  rw [(lowerStar B i.hom).rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc,
    (Functor.mapDerivedCategoryNatIso (upperStarInvIsoLowerStarHom B i).symm).hom.naturality_assoc]
    at h
  simp only [Functor.mapDerivedCategoryNatIso_trans, Functor.mapDerivedCategoryNatIso_symm,
    NatTrans.comp_app, Category.assoc] at h
  unfold pushPull
  simp only [ordinaryFinitePullback, leftDerivedUpperStarComp,
    leftDerivedUpperStarIsoMapDerivedCategory,
    Functor.leftDerivedFunctorNatIso, Functor.leftDerivedFunctorCompIso,
    Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  exact h

end AlgebraicGeometry.Etale.SfP1Transport
