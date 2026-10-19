/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem
import Sheaf.CategoryTheory.RingedAugmentedCechRestriction
import Sheaf.Paper.ExtendedCechCompletionModel

/-! # Unit-normalized restrictions of Cech completion

Source: Stacks Project, sites-cohomology.tex, Tag 08JB.
(blueprint: lem-weil-pbc-ringed-cech-completion-restriction).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

private def homRestrictionIso
    {A B : Type*} [Category A] [Category B]
    (H : Aᵒᵖ × A ⥤ A) (H' : Bᵒᵖ × B ⥤ B) (R : A ⥤ B)
    (e : H ⋙ R ≅ (R.op.prod R) ⋙ H')
    {K : A} {K' : B} (k : R.obj K ≅ K') :
    (Functor.curry.obj H).obj (op K) ⋙ R ≅
      R ⋙ (Functor.curry.obj H').obj (op K') := by
  refine NatIso.ofComponents (fun E ↦ e.app (op K, E) ≪≫
    H'.mapIso (k.symm.op.prod (Iso.refl (R.obj E)))) ?_
  intro E E' f
  have he := e.hom.naturality (X := (op K, E)) (Y := (op K, E')) (𝟙 _, f)
  dsimp at he ⊢
  simp only [Functor.map_id, op_id] at he
  rw [← Category.assoc, he]
  simp only [Category.assoc, ← H'.map_comp]
  congr 2
  ext <;> simp

private theorem homRestrictionIso_augmentation
    {A B : Type*} [Category A] [Category B]
    (H : Aᵒᵖ × A ⥤ A) (H' : Bᵒᵖ × B ⥤ B) (R : A ⥤ B)
    (e : H ⋙ R ≅ (R.op.prod R) ⋙ H')
    {K O : A} {K' O' : B} (k : R.obj K ≅ K') (o : R.obj O ≅ O')
    (a : K ⟶ O) (a' : K' ⟶ O')
    (ha : R.map a ≫ o.hom = k.hom ≫ a') (E : A) :
    R.map (H.map (a.op, 𝟙 E)) ≫ (homRestrictionIso H H' R e k).hom.app E =
      (homRestrictionIso H H' R e o).hom.app E ≫ H'.map (a'.op, 𝟙 (R.obj E)) := by
  have he := e.hom.naturality (X := (op O, E)) (Y := (op K, E)) (a.op, 𝟙 E)
  simp only [homRestrictionIso, NatIso.ofComponents_hom_app, Iso.trans_hom,
    Functor.mapIso_hom, Iso.prod_hom, Iso.op_hom, Iso.symm_hom, Iso.refl_hom,
    Iso.app_hom]
  dsimp at he
  simp only [Functor.map_id] at he
  rw [← Category.assoc, he]
  simp only [Category.assoc, ← H'.map_comp]
  congr 2
  ext
  · change (k.inv ≫ R.map a).op = (a' ≫ o.inv).op
    congr 1
    apply (cancel_mono o.hom).mp
    simp [Category.assoc, ha]
  · simp

private theorem normalizeRestrictionIso
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ A} {L' : B ⥤ B} (R : A ⥤ B)
    (eta : 𝟭 A ⟶ L) (eta' : 𝟭 B ⟶ L')
    (e : L ⋙ R ≅ R ⋙ L') (sigma : R ≅ R)
    (he : ∀ E, R.map (eta.app E) ≫ e.hom.app E =
      sigma.hom.app E ≫ eta'.app (R.obj E)) :
    ∃ t : L ⋙ R ≅ R ⋙ L',
      ∀ E, R.map (eta.app E) ≫ t.hom.app E = eta'.app (R.obj E) := by
  refine ⟨e ≪≫ Functor.isoWhiskerRight sigma.symm L', ?_⟩
  intro E
  dsimp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Iso.symm_hom]
  rw [← Category.assoc, he, Category.assoc, ← eta'.naturality]
  simp

private theorem normalizedHomRestriction_exists
    {A B : Type*} [Category A] [Category B]
    (H : Aᵒᵖ × A ⥤ A) (H' : Bᵒᵖ × B ⥤ B) (R : A ⥤ B)
    (e : H ⋙ R ≅ (R.op.prod R) ⋙ H')
    {K O : A} {K' O' : B} (k : R.obj K ≅ K') (o : R.obj O ≅ O')
    (a : K ⟶ O) (a' : K' ⟶ O')
    (ha : R.map a ≫ o.hom = k.hom ≫ a')
    (d : 𝟭 A ≅ (Functor.curry.obj H).obj (op O))
    (d' : 𝟭 B ≅ (Functor.curry.obj H').obj (op O'))
    (eta : 𝟭 A ⟶ (Functor.curry.obj H).obj (op K))
    (eta' : 𝟭 B ⟶ (Functor.curry.obj H').obj (op K'))
    (heta : ∀ E, eta.app E = d.hom.app E ≫ H.map (a.op, 𝟙 E))
    (heta' : ∀ E, eta'.app E = d'.hom.app E ≫ H'.map (a'.op, 𝟙 E)) :
    ∃ t : (Functor.curry.obj H).obj (op K) ⋙ R ≅
        R ⋙ (Functor.curry.obj H').obj (op K'),
      ∀ E, R.map (eta.app E) ≫ t.hom.app E = eta'.app (R.obj E) := by
  let eO := homRestrictionIso H H' R e o
  let sigma : R ≅ R := Functor.isoWhiskerRight d R ≪≫ eO ≪≫
    Functor.isoWhiskerLeft R d'.symm
  apply normalizeRestrictionIso R eta eta' (homRestrictionIso H H' R e k) sigma
  intro E
  rw [heta E, Functor.map_comp, Category.assoc,
    homRestrictionIso_augmentation H H' R e k o a a' ha E, heta']
  dsimp only [sigma, eO, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp




set_option backward.isDefEq.respectTransparency false in
private def derivedHomUnitIso
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (O : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))] :
    𝟭 (ringedSiteDerived O) ≅ ringedCechCompletionFunctor O (ringedSiteRingComplex O) := by
  have hdelta (E : ringedSiteDerived O) : IsIso (ringedDerivedHomUnit O E) := by
    let A := SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O)
    let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
    have : QuasiIso ((CochainComplex.toKInjectiveResolution.{u} A).app
        (DerivedCategory.Q.objPreimage E)) :=
      (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A _).2
    let e := DerivedCategory.Q.objObjPreimageIso E
    dsimp only [ringedDerivedHomUnit]
    repeat' apply IsIso.comp_isIso'
    all_goals first | infer_instance | skip
    change IsIso ((derivedInternalHom J O).mapIso ((Iso.refl _).prod e)).hom
    infer_instance
  refine NatIso.ofComponents (fun E ↦ @asIso _ _ _ _ (ringedDerivedHomUnit O E)
    (hdelta E)) ?_
  intro E E' g
  have hn := completion_unit_natural O (ringedSiteRingComplex O) (𝟙 _) E E' g
  simp only [ringedCechCompletionUnit, Functor.map_id, op_id] at hn
  change (ringedDerivedHomUnit O E ≫ (derivedInternalHom J O).map (𝟙 _)) ≫ _ =
    g ≫ ringedDerivedHomUnit O E' ≫ (derivedInternalHom J O).map (𝟙 _) at hn
  simpa only [Functor.map_id, Category.comp_id, asIso_hom, Functor.id_map] using hn.symm

private theorem augmentedCompletionRestriction
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (O : Sheaf J CommRingCat.{u}) (P : Sheaf K CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose K (forget₂ CommRingCat RingCat)).obj P))]
    (R : ringedSiteDerived O ⥤ ringedSiteDerived P)
    (e : derivedInternalHom J O ⋙ R ≅ (R.op.prod R) ⋙ derivedInternalHom K P)
    (X : ringedSiteComplex O) (a : X ⟶ ringedSiteRingComplex O)
    (X' : ringedSiteComplex P) (a' : X' ⟶ ringedSiteRingComplex P)
    (h : Arrow.mk (R.map (DerivedCategory.Q.map a)) ≅
      Arrow.mk (DerivedCategory.Q.map a')) :
    ∃ t : ringedCechCompletionFunctor O X ⋙ R ≅ R ⋙ ringedCechCompletionFunctor P X',
      ∀ E, R.map (ringedCechCompletionUnit O X a E) ≫ t.hom.app E =
        ringedCechCompletionUnit P X' a' (R.obj E) := by
  let eta : 𝟭 _ ⟶ ringedCechCompletionFunctor O X :=
    { app := ringedCechCompletionUnit O X a
      naturality := fun {E E'} g ↦ (completion_unit_natural O X a E E' g).symm }
  let eta' : 𝟭 _ ⟶ ringedCechCompletionFunctor P X' :=
    { app := ringedCechCompletionUnit P X' a'
      naturality := fun {E E'} g ↦ (completion_unit_natural P X' a' E E' g).symm }
  exact normalizedHomRestriction_exists (derivedInternalHom J O) (derivedInternalHom K P)
    R e (Arrow.leftFunc.mapIso h) (Arrow.rightFunc.mapIso h)
    (DerivedCategory.Q.map a) (DerivedCategory.Q.map a') h.hom.w.symm
    (derivedHomUnitIso O) (derivedHomUnitIso P) eta eta'
    (fun _ ↦ by simp only [eta, derivedHomUnitIso, NatIso.ofComponents_hom_app,
      asIso_hom, ringedCechCompletionUnit])
    (fun _ ↦ by simp only [eta', derivedHomUnitIso, NatIso.ofComponents_hom_app,
      asIso_hom, ringedCechCompletionUnit])

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)
variable [HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose J (forget₂ CommRingCat RingCat)).obj O))]
variable [∀ U : C, HasDerivedCategory.{w} (SheafOfModules.{u}
  ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U)))]

/-- Restriction comparisons for the Cech internal-Hom model preserve the actual
augmentation units. No strict Koszul presentation or coherence assertion is assumed.

Source: Stacks Project, sites-cohomology.tex, Tag 08JB.
(blueprint: lem-weil-pbc-ringed-cech-completion-restriction).

Proof: restriction commutes with sectionwise localization and its sheafification,
finite tensor products and finite totalizations. Induct on the number of factors to
identify the restricted augmented Cech complex with the Cech complex of the restricted
sections, carrying the augmentation to the augmentation. Apply the natural derived
internal-Hom restriction comparison, using that exact slice restriction preserves
K-injectives. Naturality in the augmented first variable relates the comparison at K to its
comparison at O. Evaluation at one identifies the latter with a natural automorphism
of restriction. Postcompose the K comparison by completion of its inverse; naturality
of the completion unit then proves the exact unit equation. Apply the same sectionwise
construction to
Over.map f for the further comparison; the two families of restricted sections agree
on every object over V. The construction uses neither the strict Koszul comparison
nor its coherence, so is independent of those claims. Empty lists restrict O[0] and
its identity augmentation; zero rings and zero or invertible sections require no change.
-/
theorem exists_ringed_cech_completion_restriction :
    ∃ (e : ∀ U : C,
      ringedCechCompletionFunctor O (ringedExtendedCech O r b).1 ⋙
          ringedDerivedRestriction O U ≅
        ringedDerivedRestriction O U ⋙ ringedCechCompletionFunctor (O.over U)
          (ringedExtendedCech (O.over U) r
            (fun i ↦ ringedKoszulSliceSection O (b i) U)).1)
      (s : ∀ (U V : C) (f : V ⟶ U),
        ringedCechCompletionFunctor (O.over U)
            (ringedExtendedCech (O.over U) r
              (fun i ↦ ringedKoszulSliceSection O (b i) U)).1 ⋙
                ringedKoszulDerivedOverMap O f ≅
          ringedKoszulDerivedOverMap O f ⋙ ringedCechCompletionFunctor (O.over V)
            (ringedExtendedCech (O.over V) r
              (fun i ↦ ringedKoszulSliceSection O (b i) V)).1),
      (∀ (U : C) E,
        (ringedDerivedRestriction O U).map
            (ringedCechCompletionUnit O (ringedExtendedCech O r b).1
              (ringedExtendedCech O r b).2 E) ≫ (e U).hom.app E =
          ringedCechCompletionUnit (O.over U)
            (ringedExtendedCech (O.over U) r
              (fun i ↦ ringedKoszulSliceSection O (b i) U)).1
            (ringedExtendedCech (O.over U) r
              (fun i ↦ ringedKoszulSliceSection O (b i) U)).2
            ((ringedDerivedRestriction O U).obj E)) ∧
      (∀ (U V : C) (f : V ⟶ U) E,
        (ringedKoszulDerivedOverMap O f).map
            (ringedCechCompletionUnit (O.over U)
              (ringedExtendedCech (O.over U) r
                (fun i ↦ ringedKoszulSliceSection O (b i) U)).1
              (ringedExtendedCech (O.over U) r
                (fun i ↦ ringedKoszulSliceSection O (b i) U)).2 E) ≫
            (s U V f).hom.app E =
          ringedCechCompletionUnit (O.over V)
            (ringedExtendedCech (O.over V) r
              (fun i ↦ ringedKoszulSliceSection O (b i) V)).1
            (ringedExtendedCech (O.over V) r
              (fun i ↦ ringedKoszulSliceSection O (b i) V)).2
            ((ringedKoszulDerivedOverMap O f).obj E)) := by
  let (U : C) : HasDerivedCategory.{w} (ringedSiteModules.{u}
      (((sheafCompose J (forget₂ CommRingCat RingCat)).obj O).over U)) :=
    inferInstanceAs (HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose (J.over U) (forget₂ CommRingCat RingCat)).obj (O.over U))))
  obtain ⟨he, hs, _⟩ := ringedInternalHom_restriction J O
  obtain ⟨ha, hb⟩ := exists_ringed_augmented_cech_restriction O r b
  have hU (U : C) := augmentedCompletionRestriction O (O.over U)
    (ringedDerivedRestriction O U) (he U)
    (ringedExtendedCech O r b).1 (ringedExtendedCech O r b).2
    (ringedExtendedCech (O.over U) r
      (fun i ↦ ringedKoszulSliceSection O (b i) U)).1
    (ringedExtendedCech (O.over U) r
      (fun i ↦ ringedKoszulSliceSection O (b i) U)).2 (ha U).some
  have hUV (U V : C) (f : V ⟶ U) :=
    augmentedCompletionRestriction (O.over U) (O.over V)
      (ringedKoszulDerivedOverMap O f) (hs U V f)
      (ringedExtendedCech (O.over U) r
        (fun i ↦ ringedKoszulSliceSection O (b i) U)).1
      (ringedExtendedCech (O.over U) r
        (fun i ↦ ringedKoszulSliceSection O (b i) U)).2
      (ringedExtendedCech (O.over V) r
        (fun i ↦ ringedKoszulSliceSection O (b i) V)).1
      (ringedExtendedCech (O.over V) r
        (fun i ↦ ringedKoszulSliceSection O (b i) V)).2 (hb U V f).some
  choose e he using hU
  choose s hs using hUV
  exact ⟨e, s, he, hs⟩

end CategoryTheory
