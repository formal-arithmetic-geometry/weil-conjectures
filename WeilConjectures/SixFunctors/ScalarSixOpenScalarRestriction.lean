/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ScalarSixDefinitions
import all WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import all WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionCoherence
import all WeilConjectures.AlgebraicGeometry.CondensedSupportDerivedLocalization

/-! # Restriction of the specified open scalar comparison -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096
set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem scalarOpenMate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {R : B ⥤ A} {J' : C ⥤ D} {R' : D ⥤ C}
    {S : A ⥤ C} {U : C ⥤ A} {T : B ⥤ D} {V : D ⥤ B}
    (a : J ⊣ R) (b : J' ⊣ R') (s : S ⊣ U) (t : T ⊣ V)
    (e : R' ⋙ U ≅ V ⋙ R) :
    (mateEquiv a b (.mk _ _ _ _
      (((conjugateIsoEquiv (s.comp b) (a.comp t)).symm e).inv))).natTrans =
      Adjunction.pushHomOfComapIso t s e := by
  let d := ((conjugateIsoEquiv (s.comp b) (a.comp t)).symm e)
  have hd : conjugateEquiv (a.comp t) (s.comp b) d.inv = e.inv := by
    exact congrArg Iso.inv ((conjugateIsoEquiv (s.comp b) (a.comp t)).apply_symm_apply e)
  have hh := iterated_mateEquiv_conjugateEquiv a b s t (.mk _ _ _ _ d.inv)
  have he : mateEquiv t s (mateEquiv a b (.mk _ _ _ _ d.inv)) =
      TwoSquare.mk _ _ _ _ e.inv := by
    ext M
    exact congr_app (hh.trans hd) M
  exact congrArg TwoSquare.natTrans ((mateEquiv t s).eq_symm_apply.mpr he)

private theorem normalizedOpenSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {J : A ⥤ B} {R : B ⥤ A} {J' : C ⥤ D} {R' : D ⥤ C}
    {S : A ⥤ C} {T : B ⥤ D}
    (a : J ⊣ R) (b : J' ⊣ R')
    (rho : J ⋙ R ≅ 𝟭 A) (rho' : J' ⋙ R' ≅ 𝟭 C)
    (ha : ∀ M, a.unit.app M ≫ rho.hom.app M = 𝟙 M)
    (hb : ∀ M, b.unit.app M ≫ rho'.hom.app M = 𝟙 M)
    (q : R ⋙ S ≅ T ⋙ R') (d : J ⋙ T ≅ S ⋙ J')
    (hd : (mateEquiv a b (.mk _ _ _ _ d.inv)).natTrans = q.hom) (M : A) :
    R'.map (d.hom.app M) ≫ rho'.hom.app (S.obj M) =
      q.inv.app (J.obj M) ≫ S.map (rho.hom.app M) := by
  have hu := unit_mateEquiv a b (.mk _ _ _ _ d.inv) M
  change S.map (a.unit.app M) ≫
      (mateEquiv a b (.mk _ _ _ _ d.inv)).natTrans.app (J.obj M) =
    b.unit.app (S.obj M) ≫ R'.map (d.inv.app M) at hu
  rw [hd] at hu
  have hh := congrArg (fun z ↦
    q.inv.app (J.obj M) ≫ S.map (rho.hom.app M) ≫ z ≫
      R'.map (d.hom.app M) ≫ rho'.hom.app (S.obj M)) hu
  have hai : rho.hom.app M ≫ a.unit.app M = 𝟙 _ := by
    rw [← cancel_mono (rho.hom.app M), Category.assoc, ha]
    erw [Category.comp_id, Category.id_comp]
  simp only [Category.assoc, ← S.map_comp_assoc, hai, ← R'.map_comp_assoc,
    Iso.inv_hom_id_app] at hh
  erw [S.map_id, R'.map_id] at hh
  simpa only [Category.id_comp, Iso.inv_hom_id_app_assoc,
    hb, Functor.id_obj, Functor.comp_obj, Category.comp_id] using hh

private theorem transportRestriction_open
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (e : A ≌ C) (e' : B ≌ D) (J : A ⥤ B) (R : B ⥤ A)
    (F : C ⥤ D) (Q : D ⥤ C)
    (d : J ⋙ e'.functor ≅ e.functor ⋙ F)
    (p : R ⋙ e.functor ≅ e'.functor ⋙ Q)
    (r : J ⋙ R ≅ 𝟭 A) (rho : F ⋙ Q ≅ 𝟭 C)
    (h : ∀ M, Q.map (d.hom.app M) ≫ rho.hom.app (e.functor.obj M) =
      p.inv.app (J.obj M) ≫ e.functor.map (r.hom.app M)) (M : A) :
    (scalarSixTransportRestriction e e' F R Q p rho).hom.app M =
      R.map ((scalarSixTransportOpen e e' J F d).hom.app M) ≫ r.hom.app M := by
  let o := scalarSixTransportOpen e e' J F d
  have ho : e'.functor.map (o.hom.app M) =
      e'.counitIso.hom.app (F.obj (e.functor.obj M)) ≫ d.inv.app M := by
    dsimp only [o, scalarSixTransportOpen, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
    simp only [Category.comp_id, Functor.map_comp]
    erw [e'.functor.map_id, Category.comp_id]
    have ht : e'.functor.map (e'.unitIso.inv.app (J.obj M)) =
        e'.counitIso.hom.app (e'.functor.obj (J.obj M)) := by
      apply (cancel_epi (e'.counitIso.inv.app (e'.functor.obj (J.obj M)))).mp
      simpa only [Functor.id_obj, Iso.inv_hom_id_app] using e'.counitIso_functor_comp (J.obj M)
    rw [ht]
    exact e'.counitIso.hom.naturality (d.inv.app M)
  have hi : Q.map (d.inv.app M) ≫ p.inv.app (J.obj M) ≫
      e.functor.map (r.hom.app M) = rho.hom.app (e.functor.obj M) := by
    rw [← h, ← Q.map_comp_assoc, Iso.inv_hom_id_app, Q.map_id, Category.id_comp]
  have hp := p.hom.naturality (o.hom.app M)
  simp only [Functor.comp_map] at hp
  have ht : e.functor.map (R.map (o.hom.app M) ≫ r.hom.app M) =
      p.hom.app ((e.functor ⋙ F ⋙ e'.inverse).obj M) ≫
        Q.map (e'.counitIso.hom.app (F.obj (e.functor.obj M))) ≫
          rho.hom.app (e.functor.obj M) := by
    rw [Functor.map_comp]
    rw [← Iso.hom_inv_id_app_assoc p (J.obj M) (e.functor.map (r.hom.app M)),
      ← Category.assoc, hp, ho, Q.map_comp]
    simp only [Category.assoc, hi]
  simp only [scalarSixTransportRestriction, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
    Functor.rightUnitor_hom_app, Category.id_comp, Category.comp_id,
    Functor.map_comp, Category.assoc]
  erw [e.inverse.map_id, Category.id_comp]
  rw [← e.inverse.map_comp_assoc, ← e.inverse.map_comp_assoc]
  simp only [Category.assoc]
  erw [← ht]
  have hn := e.unitIso.hom.naturality (R.map (o.hom.app M) ≫ r.hom.app M)
  simp only [Functor.id_map, Functor.comp_map] at hn
  erw [← reassoc_of% hn, Iso.hom_inv_id_app, Category.comp_id]

private abbrev localizedRho
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (F : A ⥤ B) (R : B ⥤ A) [F.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (rho : F ⋙ R ≅ 𝟭 A) :=
  Functor.mapDerivedCategoryCompNatIso rho ≪≫ Functor.mapDerivedCategoryIdIso A

private theorem localizedRestrictionSquare
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (J : A ⥤ B) (R : B ⥤ A) (F : C ⥤ D) (Q : D ⥤ C)
    (e : A ⥤ C) (e' : B ⥤ D)
    [J.Additive] [R.Additive] [F.Additive] [Q.Additive] [e.Additive] [e'.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [PreservesFiniteLimits e] [PreservesFiniteColimits e]
    [PreservesFiniteLimits e'] [PreservesFiniteColimits e']
    (r : J ⋙ R ≅ 𝟭 A) (rho : F ⋙ Q ≅ 𝟭 C)
    (d : J ⋙ e' ≅ e ⋙ F) (p : R ⋙ e ≅ e' ⋙ Q)
    (hq : ∀ M, e.map (r.inv.app M) ≫ p.hom.app (J.obj M) ≫ Q.map (d.hom.app M) =
      rho.inv.app (e.obj M)) (M : DerivedCategory A) :
    Q.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso d).hom.app M) ≫
        (localizedRho F Q rho).hom.app (e.mapDerivedCategory.obj M) =
      (Functor.mapDerivedCategorySquareIso p).inv.app (J.mapDerivedCategory.obj M) ≫
        e.mapDerivedCategory.map ((localizedRho J R r).hom.app M) := by
  let z : (𝟭 A) ⋙ e ≅ e ⋙ (𝟭 C) := Iso.refl e
  have h := Functor.exactSquare_comp_forward J R (𝟭 A) F Q (𝟭 C) e e' e
    d p z r.symm rho.symm (by
      intro N
      change e.map (r.inv.app N) ≫ p.hom.app (J.obj N) ≫ Q.map (d.hom.app N) =
        𝟙 (e.obj N) ≫ rho.inv.app (e.obj N)
      erw [Category.id_comp]
      exact hq N) M
  have hz : (Functor.mapDerivedCategorySquareIso z).hom.app M ≫
      (Functor.mapDerivedCategoryIdIso C).hom.app (e.mapDerivedCategory.obj M) =
      e.mapDerivedCategory.map ((Functor.mapDerivedCategoryIdIso A).hom.app M) := by
    have hc := congr_app (Functor.mapDerivedCategoryCompIso_comp_id e) M
    have ha := congr_app (Functor.mapDerivedCategoryCompIso_id_comp e) M
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      NatTrans.id_app] at hc ha
    dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app]
    have hz0 : (Functor.mapDerivedCategoryNatIso z).hom = 𝟙 _ :=
      Functor.mapDerivedCategoryNatIso_refl
    rw [hz0]
    simp only [NatTrans.id_app, Category.id_comp, Category.assoc, hc]
    apply (cancel_epi ((Functor.mapDerivedCategoryCompIso (𝟭 A) e).hom.app M)).mp
    simpa only [Category.assoc, Iso.hom_inv_id_app_assoc, Category.comp_id] using ha.symm
  have hi (L : DerivedCategory A) :
      (Functor.mapDerivedCategoryNatIso r.symm ≪≫
          Functor.mapDerivedCategoryCompIso J R).hom.app L =
        (Functor.mapDerivedCategoryIdIso A).hom.app L ≫
          (localizedRho J R r).inv.app L := by
    simp only [localizedRho, Functor.mapDerivedCategoryCompNatIso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
      Functor.mapDerivedCategoryNatIso_symm, Iso.hom_inv_id_app_assoc]
  have hj (L : DerivedCategory C) :
      (Functor.mapDerivedCategoryNatIso rho.symm ≪≫
          Functor.mapDerivedCategoryCompIso F Q).hom.app L =
        (Functor.mapDerivedCategoryIdIso C).hom.app L ≫
          (localizedRho F Q rho).inv.app L := by
    simp only [localizedRho, Functor.mapDerivedCategoryCompNatIso,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
      Functor.mapDerivedCategoryNatIso_symm, Iso.hom_inv_id_app_assoc]
  rw [hi, hj, e.mapDerivedCategory.map_comp, Category.assoc,
    ← Category.assoc ((Functor.mapDerivedCategorySquareIso z).hom.app M), hz] at h
  have hh := (cancel_epi
    (e.mapDerivedCategory.map ((Functor.mapDerivedCategoryIdIso A).hom.app M))).mp h
  have he := congrArg (fun t ↦
    (Functor.mapDerivedCategorySquareIso p).inv.app (J.mapDerivedCategory.obj M) ≫
      e.mapDerivedCategory.map ((localizedRho J R r).hom.app M) ≫ t ≫
      (localizedRho F Q rho).hom.app (e.mapDerivedCategory.obj M)) hh
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app] at he
  erw [e.mapDerivedCategory.map_id] at he
  simpa only [Functor.id_obj, Functor.comp_obj, Category.id_comp,
    Iso.inv_hom_id_app_assoc, Category.comp_id] using he

private def openRho (Λ : ScalarSixRing.{u}) {S X : Scheme.{u}} (j : S ⟶ X)
    [IsOpenImmersion j] :
    openImmersionLowerShriek Λ.X j ⋙ upperStar Λ.X j ≅ 𝟭 _ := by
  letI : IsCommMonObj Λ.X := Λ.comm
  let adj := openImmersionLowerShriekUpperStarAdjunction Λ.X j
  have : IsIso adj.unit := openUnit Λ.X j
  exact (asIso adj.unit).symm

set_option maxHeartbeats 2000000 in
-- Keep the concrete derived models folded during transport.
private theorem openRho_unit (Λ : ScalarSixRing.{u}) {S X : Scheme.{u}} (j : S ⟶ X)
    [IsOpenImmersion j]
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S)) :
    (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).unit.app M ≫
      (localizedRho (openImmersionLowerShriek Λ.X j) (upperStar Λ.X j)
        (openRho Λ j)).hom.app M = 𝟙 M := by
  letI : IsCommMonObj Λ.X := Λ.comm
  let J := openImmersionLowerShriek Λ.X j
  let R := upperStar Λ.X j
  let adj := openImmersionLowerShriekUpperStarAdjunction Λ.X j
  let r := openRho Λ j
  have : IsIso adj.unit := openUnit Λ.X j
  suffices ht : (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).unit ≫
      (localizedRho J R r).hom = 𝟙 _ from NatTrans.congr_app ht M
  apply Localization.natTrans_ext DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleRingedComparison.internalModules Λ.X S) (.up ℤ))
  intro K
  simp only [NatTrans.comp_app, NatTrans.id_app]
  have hf : (localizedRho J R r).hom.app (DerivedCategory.Qh.obj K) =
      R.mapDerivedCategory.map (J.mapDerivedCategoryFactorsh.hom.app K) ≫
        R.mapDerivedCategoryFactorsh.hom.app ((J.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (J ⋙ R)) (.up ℤ)).hom.app K ≫
            (NatTrans.mapHomotopyCategory r.hom (.up ℤ)).app K) := by
    have hc := Functor.mapDerivedCategoryCompIso_fach J R K
    dsimp only [localizedRho, Functor.mapDerivedCategoryCompNatIso, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app]
    rw [Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj, Category.assoc,
      Functor.mapDerivedCategoryNatIso_fach, ← hc]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  change adj.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Qh.obj K) ≫ _ = _
  rw [hf]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% (adj.mapDerivedCategoryAdjunction_unit_app_Qh_obj K)]
  simp only [← DerivedCategory.Qh.map_comp]
  have hh : (adj.mapHomotopyCategory (.up ℤ)).unit.app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (J ⋙ R)) (.up ℤ)).hom.app K ≫
      (NatTrans.mapHomotopyCategory r.hom (.up ℤ)).app K = 𝟙 K := by
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
    change (HomotopyCategory.quotient _ (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient _ (.up ℤ)).map _ =
        (HomotopyCategory.quotient _ (.up ℤ)).map (𝟙 L)
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    ext n : 1
    simp only [HomologicalComplex.comp_f, Adjunction.mapHomologicalComplex_unit_app_f,
      Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.refl_hom, NatTrans.id_app,
      NatTrans.mapHomologicalComplex_app_f, HomologicalComplex.id_f, Category.id_comp]
    change adj.unit.app (L.X n) ≫ (asIso adj.unit).inv.app (L.X n) = 𝟙 _
    exact (asIso adj.unit).hom_inv_id_app (L.X n)
  rw [hh]
  erw [DerivedCategory.Qh.map_id]
  rfl


private theorem restriction_localized (E : LocallyClosedExtensionData.{u})
    (D : E.DerivedCoherence) {S X : LocallyClosedCoefficients.{u}}
    (b : LocallyClosedCoefficientImmersion S X) :
    D.restriction b = localizedRho (E.extension b) b.pull (E.restriction b) := by
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (proEtaleRingModules S.scheme S.ring) (.up ℤ))
  intro K
  exact (D.restrictionTermwise b K).trans (E.restrictionTermwise b K).symm

set_option maxHeartbeats 2000000 in
-- Keep the concrete derived models folded during transport.
private theorem openRestriction
    (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) {k : Type u} [Field k]
    (O : ScalarSixOpenComparison E G k) (Λ : ScalarSixRing.{u})
    {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ X) [IsOpenImmersion j.left]
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)) :
    (scalarSixRestriction E D G Λ j).hom.app M =
      (scalarSixPull Λ j.left).map ((scalarSixOpenIso E G O Λ j).hom.app M) ≫
        (localizedRho (openImmersionLowerShriek Λ.X j.left) (upperStar Λ.X j.left)
          (openRho Λ j.left)).hom.app M := by
  letI : IsCommMonObj Λ.X := Λ.comm
  let b := scalarSixImmersion G Λ j
  letI := E.additive b
  letI := E.finiteLimits b
  letI := E.finiteColimits b
  let e := ModuleRingedComparison.equivalence Λ.X S.left
  let e' := ModuleRingedComparison.equivalence Λ.X X.left
  letI : e.functor.Additive := scalarSixEquivalenceAdditive Λ S.left
  letI : e.inverse.Additive := scalarSixEquivalenceInverseAdditive Λ S.left
  letI : e'.functor.Additive := scalarSixEquivalenceAdditive Λ X.left
  letI : e'.inverse.Additive := scalarSixEquivalenceInverseAdditive Λ X.left
  let J := openImmersionLowerShriek Λ.X j.left
  let R := upperStar Λ.X j.left
  let adj := openImmersionLowerShriekUpperStarAdjunction Λ.X j.left
  have hrho (N) : (E.restriction b).inv.app N =
      (E.openAdjunction b (inferInstanceAs (IsOpenImmersion j.left))).unit.app N := by
    apply (cancel_mono ((E.restriction b).hom.app N)).mp
    rw [Iso.inv_hom_id_app]
    exact (E.openNormalization b (inferInstanceAs (IsOpenImmersion j.left)) N).symm
  have hq (N) : e.functor.map ((openRho Λ j.left).inv.app N) ≫
      (G.pull Λ j.left).hom.app (J.obj N) ≫ b.pull.map ((O.comparison Λ j).hom.app N) =
        (E.restriction b).inv.app (e.functor.obj N) := by
    have hh := unit_mateEquiv adj
      (E.openAdjunction b (inferInstanceAs (IsOpenImmersion j.left)))
      (.mk _ _ _ _ (O.comparison Λ j).inv) N
    change e.functor.map (adj.unit.app N) ≫
        (mateEquiv adj (E.openAdjunction b
          (inferInstanceAs (IsOpenImmersion j.left)))
          (.mk _ _ _ _ (O.comparison Λ j).inv)).natTrans.app (J.obj N) =
      (E.openAdjunction b (inferInstanceAs (IsOpenImmersion j.left))).unit.app
        (e.functor.obj N) ≫ b.pull.map ((O.comparison Λ j).inv.app N) at hh
    rw [O.normalization] at hh
    change e.functor.map (adj.unit.app N) ≫ _ ≫ _ = _
    rw [← Category.assoc, hh, Category.assoc, ← b.pull.map_comp,
      Iso.inv_hom_id_app]
    erw [b.pull.map_id, Category.comp_id, hrho]
  have hs := localizedRestrictionSquare J R (E.extension b) b.pull e.functor e'.functor
    (openRho Λ j.left) (E.restriction b) (O.comparison Λ j) (G.pull Λ j.left) hq
  have ht := transportRestriction_open e.mapDerivedCategory e'.mapDerivedCategory
    J.mapDerivedCategory R.mapDerivedCategory (E.extension b).mapDerivedCategory
    b.pull.mapDerivedCategory (Functor.mapDerivedCategorySquareIso (O.comparison Λ j))
    (Functor.mapDerivedCategorySquareIso (G.pull Λ j.left))
    (localizedRho J R (openRho Λ j.left))
    (localizedRho (E.extension b) b.pull (E.restriction b)) hs M
  change (scalarSixTransportRestriction _ _ _ _ _ _ (D.restriction b)).hom.app M = _
  rw [restriction_localized]
  exact ht

set_option maxHeartbeats 2000000 in
-- Bound the elaboration of the concrete scalar and open adjunctions.
/-- The specified open scalar comparison has the fixed restriction normalization.

Source: blueprint latest, det-prop-scalar-six-pullback.proof.md (2), open case;
Stacks Tags 03DI and 03DJ.
(blueprint: lem-sfb-scalar-six-open-scalar-restriction).

Proof: the inverse of E.restriction is the unit of E.openAdjunction by
E.openNormalization. Localize this equation on cochain complexes;
D.restrictionTermwise identifies its image with D.restriction, and localization
extensionality extends it to every derived object. Transport the equation through
the fixed module equivalences. The mate equation O.normalization identifies the
transported unit with the published internal open unit, using the equivalence
triangle identities and G.pull. The published derivedOpenImmersionShriekIso is
the conjugate of derivedComapUpperStarIso under the open and scalar adjunctions.
The unit identity for conjugation, together with the mate unit identity defining
scalarSixPullHom, gives the displayed restriction equation. Finally
C.thetaNormalization identifies the pullback comparison with C.theta. Cancel its
invertible hom and the two open units. This calculation does not use closed support
or an immersion comparison. -/
theorem scalarSixOpenScalar_restriction
    (E : LocallyClosedExtensionData.{u}) (D : E.DerivedCoherence)
    (G : ScalarSixGeometry.{u}) (C : ScalarSixPullbackData.{u})
    {k : Type u} [Field k] (O : ScalarSixOpenComparison E G k)
    {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ') {S X : Over (Spec (.of k))}
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    (j : S ⟶ X) [IsOpenImmersion j.left]
    (M : DerivedCategory (ModuleRingedComparison.internalModules Λ.X S.left)) :
    (scalarSixPull Λ' j.left).map
        ((scalarSixChange a X.left).map ((scalarSixOpenIso E G O Λ j).hom.app M) ≫
          (scalarSixOpenScalarIso a j.left).hom.app M ≫
          (scalarSixOpenIso E G O Λ' j).inv.app ((scalarSixChange a S.left).obj M)) ≫
        (scalarSixRestriction E D G Λ' j).hom.app ((scalarSixChange a S.left).obj M) =
      (C.theta a j.left).inv.app ((scalarSixExtension E G Λ j).obj M) ≫
        (scalarSixChange a S.left).map ((scalarSixRestriction E D G Λ j).hom.app M) := by
  letI : IsCommMonObj Λ.X := Λ.comm
  letI : IsCommMonObj Λ'.X := Λ'.comm
  letI : IsMonHom a.hom.hom := a.hom.isMonHom_hom
  let adj := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j.left
  let adj' := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X j.left
  let r := localizedRho (openImmersionLowerShriek Λ.X j.left)
    (upperStar Λ.X j.left) (openRho Λ j.left)
  let r' := localizedRho (openImmersionLowerShriek Λ'.X j.left)
    (upperStar Λ'.X j.left) (openRho Λ' j.left)
  have hd : (mateEquiv adj adj' (.mk _ _ _ _
      (scalarSixOpenScalarIso a j.left).inv)).natTrans = (C.theta a j.left).hom := by
    rw [C.thetaNormalization]
    exact scalarOpenMate adj adj'
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom S.left))
      (Mod.derivedExtendMapDerivedCategoryAdjunction
        (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom X.left))
      (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j.left)
  have hs := normalizedOpenSquare adj adj' r r' (openRho_unit Λ j.left)
    (openRho_unit Λ' j.left) (C.theta a j.left) (scalarSixOpenScalarIso a j.left) hd M
  rw [openRestriction E D G O Λ']
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [Functor.map_comp, Category.assoc]
  erw [hs]
  have hn := (C.theta a j.left).inv.naturality
    ((scalarSixOpenIso E G O Λ j).hom.app M)
  simp only [Functor.comp_map] at hn
  rw [← Category.assoc]
  erw [hn]
  rw [openRestriction E D G O Λ]
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing
