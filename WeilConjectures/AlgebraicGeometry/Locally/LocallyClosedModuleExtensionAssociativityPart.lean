/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Locally.LocallyClosedModuleExtensionBinary
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
/-! Associativity portion of locally closed model coherence. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme

private noncomputable abbrev ringAdj {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  proEtaleSheafAdjunction f CommRingCat.{u + 1}

private theorem ring_pull_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    conjugateIsoEquiv (ringAdj g) (ringAdj f)
      (eqToIso (congrArg (fun k ↦ proEtaleSheafInverseImage k CommRingCat.{u + 1}) h)) =
      (eqToIso (congrArg
        (fun k ↦ proEtaleSheafDirectImage k CommRingCat.{u + 1}) h)).symm := by
  cases h
  ext : 1
  simp

private theorem ring_pull_assoc {W T S X : Scheme.{u}}
    (d : W ⟶ T) (b : T ⟶ S) (a : S ⟶ X) :
    proEtaleRingInverseImageComp d (b ≫ a) ≪≫
        Functor.isoWhiskerRight (proEtaleRingInverseImageComp b a)
          (proEtaleSheafInverseImage d CommRingCat.{u + 1}) ≪≫
        Functor.associator _ _ _ =
      eqToIso (congrArg (fun k ↦ proEtaleSheafInverseImage k CommRingCat.{u + 1})
        (Category.assoc d b a).symm) ≪≫ proEtaleRingInverseImageComp (d ≫ b) a ≪≫
        Functor.isoWhiskerLeft (proEtaleSheafInverseImage a CommRingCat.{u + 1})
          (proEtaleRingInverseImageComp d b) := by
  apply (conjugateIsoEquiv ((ringAdj a).comp ((ringAdj b).comp (ringAdj d)))
    (ringAdj (d ≫ b ≫ a))).injective
  simp only [← Iso.trans_assoc]
  rw [conjugateIsoEquiv_trans _ (((ringAdj a).comp (ringAdj b)).comp (ringAdj d)) _,
    conjugateIsoEquiv_trans _ ((ringAdj (b ≫ a)).comp (ringAdj d)) _,
    conjugateIsoEquiv_trans _ ((ringAdj a).comp (ringAdj (d ≫ b))) _,
    conjugateIsoEquiv_trans _ (ringAdj ((d ≫ b) ≫ a)) _]
  simp only [conjugateIsoEquiv_associator, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_isoWhiskerLeft,
    proEtaleRingInverseImageComp, conjugateIsoEquiv_iso_symm,
    Equiv.apply_symm_apply, Iso.symm_symm_eq]
  erw [ring_pull_congr (Category.assoc d b a).symm]
  exact AlgebraicGeometry.ProEtale.legacy_lowerStarComp_assoc CommRingCat.{u + 1} d b a

private theorem immersion_eq {S X : LocallyClosedCoefficients.{u}}
    {a b : LocallyClosedCoefficientImmersion S X} (h : a.hom = b.hom)
    (hc : (eqToIso (congrArg
      (fun f ↦ proEtaleSheafInverseImage f CommRingCat.{u + 1}) h)).app X.ring ≪≫
        b.coefficient = a.coefficient) : a = b := by
  rcases a with ⟨f, hf, c⟩
  rcases b with ⟨g, hg, d⟩
  dsimp only at h
  cases h
  have hc' : d = c := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Iso.app_hom, eqToIso.hom, eqToHom_refl,
      NatTrans.id_app, Category.id_comp] using congrArg Iso.hom hc
  cases hc'
  rfl

private theorem immersion_assoc {S X T W : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (d : LocallyClosedCoefficientImmersion W T) :
    (a.comp b).comp d = a.comp (b.comp d) := by
  apply immersion_eq (Category.assoc d.hom b.hom a.hom).symm
  apply Iso.ext
  have h := congrArg (fun e ↦ e.hom.app X.ring) (ring_pull_assoc d.hom b.hom a.hom)
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app] at h
  simp only [Category.comp_id] at h
  dsimp only [LocallyClosedCoefficientImmersion.comp, proEtaleRingCompositeCoefficients,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [(proEtaleRingInverseImageComp d.hom b.hom).hom.naturality_assoc a.coefficient.hom]
  dsimp only [Functor.comp_map]
  rw [← reassoc_of% h]

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleRingDirectImageMap proEtaleRingCompositeCoefficients proEtaleRingInverseImageComp

private noncomputable abbrev moduleAdj {S X : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) :=
  proEtaleRingModuleAdjunction a.hom X.ring S.ring a.coefficient

@[irreducible] private noncomputable def pushComp {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S) :
    b.push ⋙ a.push ≅ (a.comp b).push :=
  conjugateIsoEquiv ((moduleAdj a).comp (moduleAdj b)) (moduleAdj (a.comp b)) (a.pullComp b)

-- The module compositor is fixed by its sectionwise right-adjoint normalization.
private theorem pushComp_forget {S X T : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (N : proEtaleRingModules T.scheme T.ring) :
    (SheafOfModules.toSheaf _).map ((pushComp a b).hom.app N) =
      (AlgebraicGeometry.ProEtale.lowerStarComp AddCommGrpCat.{u + 1} b.hom a.hom).hom.app
        ((SheafOfModules.toSheaf _).obj N) := by
  unfold pushComp LocallyClosedCoefficientImmersion.pullComp exchangeModuleComposition
  ext U m
  exact (exchangeModuleComposition_existsUnique b.hom a.hom X.ring S.ring T.ring
    a.coefficient b.coefficient).choose_spec.1 N U.unop m

private theorem push_congr_forget {S X : LocallyClosedCoefficients.{u}}
    {a b : LocallyClosedCoefficientImmersion S X} (h : a = b)
    (N : proEtaleRingModules S.scheme S.ring) :
    (SheafOfModules.toSheaf _).map
        ((eqToIso (congrArg LocallyClosedCoefficientImmersion.push h)).hom.app N) =
      (AlgebraicGeometry.ProEtale.lowerStarCongr AddCommGrpCat.{u + 1}
        (congrArg LocallyClosedCoefficientImmersion.hom h)).hom.app
          ((SheafOfModules.toSheaf _).obj N) := by
  cases h
  ext U m
  rfl

attribute [local irreducible] LocallyClosedCoefficientImmersion.pullComp
  exchangeModuleComposition

set_option maxHeartbeats 2000000 in
-- Comparing underlying direct images requires reducing several module structures.
private theorem push_assoc {S X T W : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (d : LocallyClosedCoefficientImmersion W T)
    (h : (a.comp b).comp d = a.comp (b.comp d)) :
    Functor.associator d.push b.push a.push ≪≫
        Functor.isoWhiskerLeft d.push (pushComp a b) ≪≫ pushComp (a.comp b) d =
      Functor.isoWhiskerRight (pushComp b d) a.push ≪≫ pushComp a (b.comp d) ≪≫
        (eqToIso (congrArg LocallyClosedCoefficientImmersion.push h)).symm := by
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply (SheafOfModules.toSheaf _).map_injective
  have hc := push_congr_forget h.symm N
  have ha := pushComp_forget (a.comp b) d N
  have hb := pushComp_forget a (b.comp d) N
  have hab := pushComp_forget a b (d.push.obj N)
  have hbd := pushComp_forget b d N
  have H := congrArg (fun e ↦ e.hom.app ((SheafOfModules.toSheaf _).obj N))
    (AlgebraicGeometry.ProEtale.legacy_lowerStarComp_assoc
      AddCommGrpCat.{u + 1} d.hom b.hom a.hom)
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.id_comp, Functor.map_comp] at H ⊢
  rw [hab, ha, hb]
  have hh : (eqToIso (congrArg LocallyClosedCoefficientImmersion.push h)).inv =
      (eqToIso (congrArg LocallyClosedCoefficientImmersion.push h.symm)).hom := by
    rfl
  simp only [Iso.symm_hom, hh]
  erw [hc]
  have hm : (SheafOfModules.toSheaf _).map (a.push.map ((pushComp b d).hom.app N)) =
      (AlgebraicGeometry.ProEtale.lowerStar AddCommGrpCat.{u + 1} a.hom).map
        ((SheafOfModules.toSheaf _).map ((pushComp b d).hom.app N)) := rfl
  erw [hm, hbd]
  exact H

attribute [local irreducible] proEtaleRingModuleDirectImage

private theorem pull_congr {S X : LocallyClosedCoefficients.{u}}
    {a b : LocallyClosedCoefficientImmersion S X} (h : a = b) :
    conjugateIsoEquiv (moduleAdj b) (moduleAdj a)
      (eqToIso (congrArg LocallyClosedCoefficientImmersion.pull h)) =
      (eqToIso (congrArg LocallyClosedCoefficientImmersion.push h)).symm := by
  cases h
  ext : 1
  simp

private theorem adjoint_compositor_associativity
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {La : D ⥤ C} {Lb : C ⥤ B} {Ld : B ⥤ A}
    {Lab : D ⥤ B} {Lbd : C ⥤ A} {Lleft Lright : D ⥤ A}
    {Ra : C ⥤ D} {Rb : B ⥤ C} {Rd : A ⥤ B}
    {Rab : B ⥤ D} {Rbd : A ⥤ C} {Rleft Rright : A ⥤ D}
    (aa : La ⊣ Ra) (ab : Lb ⊣ Rb) (ad : Ld ⊣ Rd)
    (aab : Lab ⊣ Rab) (abd : Lbd ⊣ Rbd)
    (al : Lleft ⊣ Rleft) (ar : Lright ⊣ Rright)
    (cab : Lab ≅ La ⋙ Lb) (cbd : Lbd ≅ Lb ⋙ Ld)
    (cl : Lleft ≅ Lab ⋙ Ld) (cr : Lright ≅ La ⋙ Lbd)
    (e : Lleft ≅ Lright)
    (hc : Functor.associator Rd Rb Ra ≪≫
        Functor.isoWhiskerLeft Rd (conjugateIsoEquiv (aa.comp ab) aab cab) ≪≫
          conjugateIsoEquiv (aab.comp ad) al cl =
      Functor.isoWhiskerRight (conjugateIsoEquiv (ab.comp ad) abd cbd) Ra ≪≫
        conjugateIsoEquiv (aa.comp abd) ar cr ≪≫ conjugateIsoEquiv ar al e) :
    cl ≪≫ Functor.isoWhiskerRight cab Ld ≪≫ Functor.associator La Lb Ld =
      e ≪≫ cr ≪≫ Functor.isoWhiskerLeft La cbd := by
  apply (conjugateIsoEquiv (aa.comp (ab.comp ad)) al).injective
  simp only [← Iso.trans_assoc]
  rw [conjugateIsoEquiv_trans _ ((aa.comp ab).comp ad) _,
    conjugateIsoEquiv_trans _ (aab.comp ad) _,
    conjugateIsoEquiv_trans _ (aa.comp abd) _,
    conjugateIsoEquiv_trans _ ar _]
  simpa only [conjugateIsoEquiv_associator, conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_isoWhiskerLeft, Iso.trans_assoc] using hc

set_option maxHeartbeats 2000000 in
-- The concrete conjugation involves large module functor and adjunction types.
private theorem pull_assoc {S X T W : LocallyClosedCoefficients.{u}}
    (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
    (d : LocallyClosedCoefficientImmersion W T)
    (h : (a.comp b).comp d = a.comp (b.comp d)) :
    (a.comp b).pullComp d ≪≫ Functor.isoWhiskerRight (a.pullComp b) d.pull ≪≫
        Functor.associator _ _ _ =
      eqToIso (congrArg LocallyClosedCoefficientImmersion.pull h) ≪≫
        a.pullComp (b.comp d) ≪≫ Functor.isoWhiskerLeft a.pull (b.pullComp d) := by
  apply adjoint_compositor_associativity (moduleAdj a) (moduleAdj b) (moduleAdj d)
    (moduleAdj (a.comp b)) (moduleAdj (b.comp d))
    (moduleAdj ((a.comp b).comp d)) (moduleAdj (a.comp (b.comp d)))
    (a.pullComp b) (b.pullComp d) ((a.comp b).pullComp d) (a.pullComp (b.comp d))
    (eqToIso (congrArg LocallyClosedCoefficientImmersion.pull h))
  erw [pull_congr h]
  simpa only [pushComp] using push_assoc a b d h

private theorem restriction_injective
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (L : D ⥤ C)
    [F.Full] [F.Faithful] (r : F ⋙ L ≅ 𝟭 C)
    {A : D} {M N : C} (e : A ≅ F.obj M) {f g : A ⟶ F.obj N}
    (h : L.map f = L.map g) : f = g := by
  apply (cancel_epi e.inv).mp
  obtain ⟨f', hf⟩ := F.map_surjective (e.inv ≫ f)
  obtain ⟨g', hg⟩ := F.map_surjective (e.inv ≫ g)
  have hn := r.hom.naturality f'
  have hm := r.hom.naturality g'
  dsimp only [Functor.comp_map, Functor.id_map] at hn hm
  have he : L.map (F.map f') = L.map (F.map g') := by
    rw [hf, hg, L.map_comp, L.map_comp, h]
  rw [he, hm] at hn
  have : f' = g' := (cancel_epi (r.hom.app M)).mp hn.symm
  rw [← hf, ← hg, this]

-- The normalized restrictions of both triple paths have the same three-factor tail.
private theorem normalized_associativity
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Ea : C ⥤ D) (Eb : B ⥤ C) (Ed : A ⥤ B)
    (Eab : B ⥤ D) (Ebd : A ⥤ C) (H : A ⥤ D) [H.Full] [H.Faithful]
    (La : D ⥤ C) (Lb : C ⥤ B) (Ld : B ⥤ A)
    (Lab : D ⥤ B) (Lbd : C ⥤ A) (L : D ⥤ A)
    (ra : Ea ⋙ La ≅ 𝟭 C) (rb : Eb ⋙ Lb ≅ 𝟭 B) (rd : Ed ⋙ Ld ≅ 𝟭 A)
    (rab : Eab ⋙ Lab ≅ 𝟭 B) (rbd : Ebd ⋙ Lbd ≅ 𝟭 A) (r : H ⋙ L ≅ 𝟭 A)
    (cab : Lab ≅ La ⋙ Lb) (cbd : Lbd ≅ Lb ⋙ Ld)
    (cx : L ≅ La ⋙ Lbd) (cy : L ≅ Lab ⋙ Ld)
    (gab : Eb ⋙ Ea ≅ Eab) (gbd : Ed ⋙ Eb ≅ Ebd)
    (gx : Ebd ⋙ Ea ≅ H) (gy : Ed ⋙ Eab ≅ H)
    (nab : LocallyClosedBinaryNormalization Ea Eb La Lb Lab Eab ra rb rab cab gab)
    (nbd : LocallyClosedBinaryNormalization Eb Ed Lb Ld Lbd Ebd rb rd rbd cbd gbd)
    (nx : LocallyClosedBinaryNormalization Ea Ebd La Lbd L H ra rbd r cx gx)
    (ny : LocallyClosedBinaryNormalization Eab Ed Lab Ld L H rab rd r cy gy)
    (hc : cy ≪≫ Functor.isoWhiskerRight cab Ld ≪≫ Functor.associator _ _ _ =
      cx ≪≫ Functor.isoWhiskerLeft La cbd) :
    Functor.isoWhiskerRight gbd Ea ≪≫ gx =
      Functor.associator Ed Eb Ea ≪≫ Functor.isoWhiskerLeft Ed gab ≪≫ gy := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply restriction_injective H L r
    (((Functor.isoWhiskerRight gbd Ea) ≪≫ gx).app M)
  apply (cancel_mono (r.hom.app M)).mp
  change L.map (Ea.map (gbd.hom.app M) ≫ gx.hom.app M) ≫ r.hom.app M =
    L.map (𝟙 _ ≫ gab.hom.app (Ed.obj M) ≫ gy.hom.app M) ≫ r.hom.app M
  simp only [Category.id_comp, Functor.map_comp, Category.assoc]
  have hnab := nab (Ed.obj M)
  have hnbd := nbd M
  have hnx := nx M
  have hny := ny M
  dsimp only [LocallyClosedBinaryNormalization,
    LocallyClosedCompositeRestrictionMap] at hnab hnbd hnx hny
  have hleft : L.map (Ea.map (gbd.hom.app M)) ≫ L.map (gx.hom.app M) ≫ r.hom.app M =
      cx.hom.app (Ea.obj (Eb.obj (Ed.obj M))) ≫
        cbd.hom.app (La.obj (Ea.obj (Eb.obj (Ed.obj M)))) ≫
          Ld.map (Lb.map (ra.hom.app (Eb.obj (Ed.obj M)))) ≫
            Ld.map (rb.hom.app (Ed.obj M)) ≫ rd.hom.app M := by
    rw [hnx, ← Category.assoc,
      cx.hom.naturality (Ea.map (gbd.hom.app M))]
    dsimp only [Functor.comp_map]
    simp only [Category.assoc]
    have hnra := ra.hom.naturality (gbd.hom.app M)
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map] at hnra
    rw [← Lbd.map_comp_assoc, hnra]
    rw [Lbd.map_comp, Category.assoc, hnbd]
    have hnc := cbd.hom.naturality (ra.hom.app (Eb.obj (Ed.obj M)))
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hnc
    rw [reassoc_of% hnc]
    simp only [Functor.comp_obj]
  have hright : L.map (gab.hom.app (Ed.obj M)) ≫ L.map (gy.hom.app M) ≫
      r.hom.app M =
      cy.hom.app (Ea.obj (Eb.obj (Ed.obj M))) ≫
        Ld.map (cab.hom.app (Ea.obj (Eb.obj (Ed.obj M)))) ≫
          Ld.map (Lb.map (ra.hom.app (Eb.obj (Ed.obj M)))) ≫
            Ld.map (rb.hom.app (Ed.obj M)) ≫ rd.hom.app M := by
    rw [hny, ← Category.assoc, cy.hom.naturality (gab.hom.app (Ed.obj M))]
    dsimp only [Functor.comp_map]
    simp only [Category.assoc]
    rw [← Ld.map_comp_assoc, hnab, Ld.map_comp, Ld.map_comp]
    simp only [Category.assoc, Functor.comp_obj]
  rw [hleft, hright]
  have hc' := congrArg (fun e ↦ e.hom.app (Ea.obj (Eb.obj (Ed.obj M)))) hc
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Category.comp_id] at hc'
  rw [← Category.assoc, ← Category.assoc,
    ← Category.assoc, ← Category.assoc, hc']
  simp only [Category.assoc]

private theorem normalization_transport
    {A C D : Type*} [Category A] [Category C] [Category D]
    (Ea : C ⥤ D) (Eb : A ⥤ C) (La : D ⥤ C) (Lb : C ⥤ A)
    (L L' : D ⥤ A) (H H' : A ⥤ D)
    (ra : Ea ⋙ La ≅ 𝟭 C) (rb : Eb ⋙ Lb ≅ 𝟭 A)
    (r : H ⋙ L ≅ 𝟭 A) (r' : H' ⋙ L' ≅ 𝟭 A)
    (e : H ≅ H') (c : L ≅ L') (cab : L' ≅ La ⋙ Lb)
    (g : Eb ⋙ Ea ≅ H')
    (ht : ∀ M, L.map (e.inv.app M) ≫ r.hom.app M =
      c.hom.app (H'.obj M) ≫ r'.hom.app M)
    (ng : LocallyClosedBinaryNormalization Ea Eb La Lb L' H' ra rb r' cab g) :
    LocallyClosedBinaryNormalization Ea Eb La Lb L H ra rb r (c ≪≫ cab)
      (g ≪≫ e.symm) := by
  intro M
  change L.map (g.hom.app M ≫ e.inv.app M) ≫ r.hom.app M = _
  rw [Functor.map_comp, Category.assoc, ht, ← Category.assoc, c.hom.naturality]
  rw [Category.assoc, ng M]
  simp only [LocallyClosedCompositeRestrictionMap, Iso.trans_hom,
    NatTrans.comp_app, Functor.comp_obj, Category.assoc]

-- Perform equality transport before specializing to the concrete module functors.
private theorem associativity_with_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (Ea : C ⥤ D) (Eb : B ⥤ C) (Ed : A ⥤ B)
    (Eab : B ⥤ D) (Ebd : A ⥤ C) (H H' : A ⥤ D) [H.Full] [H.Faithful]
    (La : D ⥤ C) (Lb : C ⥤ B) (Ld : B ⥤ A)
    (Lab : D ⥤ B) (Lbd : C ⥤ A) (L L' : D ⥤ A)
    (ra : Ea ⋙ La ≅ 𝟭 C) (rb : Eb ⋙ Lb ≅ 𝟭 B) (rd : Ed ⋙ Ld ≅ 𝟭 A)
    (rab : Eab ⋙ Lab ≅ 𝟭 B) (rbd : Ebd ⋙ Lbd ≅ 𝟭 A)
    (r : H ⋙ L ≅ 𝟭 A) (r' : H' ⋙ L' ≅ 𝟭 A)
    (cab : Lab ≅ La ⋙ Lb) (cbd : Lbd ≅ Lb ⋙ Ld)
    (cy : L ≅ Lab ⋙ Ld) (cr : L' ≅ La ⋙ Lbd)
    (e : H ≅ H') (c : L ≅ L')
    (gab : Eb ⋙ Ea ≅ Eab) (gbd : Ed ⋙ Eb ≅ Ebd)
    (gx : Ebd ⋙ Ea ≅ H') (gy : Ed ⋙ Eab ≅ H)
    (nab : LocallyClosedBinaryNormalization Ea Eb La Lb Lab Eab ra rb rab cab gab)
    (nbd : LocallyClosedBinaryNormalization Eb Ed Lb Ld Lbd Ebd rb rd rbd cbd gbd)
    (nx : LocallyClosedBinaryNormalization Ea Ebd La Lbd L' H' ra rbd r' cr gx)
    (ny : LocallyClosedBinaryNormalization Eab Ed Lab Ld L H rab rd r cy gy)
    (ht : ∀ M, L.map (e.inv.app M) ≫ r.hom.app M =
      c.hom.app (H'.obj M) ≫ r'.hom.app M)
    (hc : cy ≪≫ Functor.isoWhiskerRight cab Ld ≪≫ Functor.associator _ _ _ =
      c ≪≫ cr ≪≫ Functor.isoWhiskerLeft La cbd) :
    Functor.isoWhiskerRight gbd Ea ≪≫ gx =
      Functor.associator Ed Eb Ea ≪≫ Functor.isoWhiskerLeft Ed gab ≪≫ gy ≪≫ e := by
  have nt := normalization_transport Ea Ebd La Lbd L L' H H' ra rbd r r'
    e c cr gx ht nx
  have hc' : cy ≪≫ Functor.isoWhiskerRight cab Ld ≪≫ Functor.associator _ _ _ =
      (c ≪≫ cr) ≪≫ Functor.isoWhiskerLeft La cbd := by
    simpa only [Iso.trans_assoc] using hc
  have he := normalized_associativity Ea Eb Ed Eab Ebd H La Lb Ld Lab Lbd L
    ra rb rd rab rbd r cab cbd (c ≪≫ cr) cy gab gbd (gx ≪≫ e.symm) gy
    nab nbd nt ny hc'
  have he' := congrArg (fun z ↦ z ≪≫ e) he
  simpa only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl] using he'

private theorem restriction_transport {S X : LocallyClosedCoefficients.{u}}
    {a b : LocallyClosedCoefficientImmersion S X} (h : a = b)
    (M : proEtaleRingModules S.scheme S.ring) :
    a.pull.map ((eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h)).inv.app M)
        ≫ a.modelRestriction.hom.app M =
      (eqToIso (congrArg LocallyClosedCoefficientImmersion.pull h)).hom.app
        (b.modelExtension.obj M) ≫ b.modelRestriction.hom.app M := by
  cases h
  simp

set_option maxHeartbeats 2000000 in
-- Instantiating the categorical argument requires reduction of concrete module functors.
/-- Associativity for normalized locally closed model extensions.

Source: Stacks Project, Tag 02V0; the associativity portion of locally closed extension
coherence.
Proof: conjugating the ring inverse-image compositors along their adjunctions turns the
pro-etale direct-image associativity `legacy_lowerStarComp_assoc` into associativity of the
ring compositors; with naturality this identifies the composite coefficients, so
`(a.comp b).comp d = a.comp (b.comp d)`. The module compositors `pullComp` are conjugate to
the direct-image compositors (the normalization of `exchangeModuleComposition_existsUnique`),
hence are associative up to this equality. Expanding the binary normalizations of the four
supplied comparisons along both triple paths, each path's restriction becomes the same
compositor prefix followed by the three model restrictions; since the model extension is
fully faithful and its restriction is an isomorphism, the two triple paths agree.
(blueprint: lem-sfb-locally-closed-module-extension-associativity-part).
-/
theorem locallyClosedModel_associativity_part (G : LocallyClosedModelComposition.{u}) :
    ∀ {S X T W : LocallyClosedCoefficients.{u}}
      (a : LocallyClosedCoefficientImmersion S X) (b : LocallyClosedCoefficientImmersion T S)
      (d : LocallyClosedCoefficientImmersion W T),
      ∃ h : (a.comp b).comp d = a.comp (b.comp d),
        Functor.isoWhiskerRight (G.gamma b d) a.modelExtension ≪≫ G.gamma a (b.comp d) =
          Functor.associator d.modelExtension b.modelExtension a.modelExtension ≪≫
            Functor.isoWhiskerLeft d.modelExtension (G.gamma a b) ≪≫
              G.gamma (a.comp b) d ≪≫
                eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h) := by
  intro S X T W a b d
  let h := immersion_assoc a b d
  refine ⟨h, ?_⟩
  exact associativity_with_transport
    a.modelExtension b.modelExtension d.modelExtension
    (a.comp b).modelExtension (b.comp d).modelExtension
    ((a.comp b).comp d).modelExtension (a.comp (b.comp d)).modelExtension
    a.pull b.pull d.pull (a.comp b).pull (b.comp d).pull
    ((a.comp b).comp d).pull (a.comp (b.comp d)).pull
    a.modelRestriction b.modelRestriction d.modelRestriction
    (a.comp b).modelRestriction (b.comp d).modelRestriction
    ((a.comp b).comp d).modelRestriction (a.comp (b.comp d)).modelRestriction
    (a.pullComp b) (b.pullComp d) ((a.comp b).pullComp d) (a.pullComp (b.comp d))
    (eqToIso (congrArg LocallyClosedCoefficientImmersion.modelExtension h))
    (eqToIso (congrArg LocallyClosedCoefficientImmersion.pull h))
    (G.gamma a b) (G.gamma b d) (G.gamma a (b.comp d)) (G.gamma (a.comp b) d)
    (G.normalized a b) (G.normalized b d)
    (G.normalized a (b.comp d)) (G.normalized (a.comp b) d)
    (restriction_transport h) (pull_assoc a b d h)

end AlgebraicGeometry.Scheme
