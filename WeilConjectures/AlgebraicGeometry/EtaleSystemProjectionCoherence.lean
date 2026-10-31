/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.EtaleSystemProjectionData
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.AlgebraicGeometry.IntegralResidueMatePasting

/-! # Composition and unit of the system coefficient mate

Source: Zheng, Constructions 4.1 and 5.14--5.15, Lemma 5.16; Stacks Tag 0GL6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

set_option backward.defeqAttrib.useBackward true in
private theorem conjugate_uniqueness
    {A B : Type*} [Category A] [Category B]
    {L L' : A ⥤ B} {R R' : B ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (e : R ≅ R') :
    conjugateEquiv b a ((a.ofNatIsoRight e).leftAdjointUniq b).hom = e.inv := by
  have hi : conjugateEquiv a b ((a.ofNatIsoRight e).leftAdjointUniq b).inv =
      e.hom := by
    ext N
    rw [conjugateEquiv_apply_app, Adjunction.leftAdjointUniq_inv_app,
      ← Category.assoc, Adjunction.unit_leftAdjointUniq_hom_app]
    simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
    rw [Category.assoc, ← e.hom.naturality, ← Category.assoc,
      a.right_triangle_components, Category.id_comp]
  apply (cancel_mono e.hom).1
  conv_rhs => rw [Iso.inv_hom_id]
  rw [← hi]
  exact conjugateEquiv_comm b a (by simp)

set_option backward.defeqAttrib.useBackward true in
private theorem scalar_mate_composition
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    {L₀₁ : A₀ ⥤ A₁} {R₁₀ : A₁ ⥤ A₀}
    {L₁₂ : A₁ ⥤ A₂} {R₂₁ : A₂ ⥤ A₁}
    {L₀₂ : A₀ ⥤ A₂} {R₂₀ : A₂ ⥤ A₀}
    {S₀₁ : B₀ ⥤ B₁} {T₁₀ : B₁ ⥤ B₀}
    {S₁₂ : B₁ ⥤ B₂} {T₂₁ : B₂ ⥤ B₁}
    {S₀₂ : B₀ ⥤ B₂} {T₂₀ : B₂ ⥤ B₀}
    (a : L₀₁ ⊣ R₁₀) (b : L₁₂ ⊣ R₂₁) (c : L₀₂ ⊣ R₂₀)
    (d : S₀₁ ⊣ T₁₀) (e : S₁₂ ⊣ T₂₁) (f : S₀₂ ⊣ T₂₀)
    {F₀ : A₀ ⥤ B₀} {F₁ : A₁ ⥤ B₁} {F₂ : A₂ ⥤ B₂}
    (r : R₁₀ ⋙ F₀ ⟶ F₁ ⋙ T₁₀) (s : R₂₁ ⋙ F₁ ⟶ F₂ ⋙ T₂₁)
    (t : R₂₀ ⋙ F₀ ⟶ F₂ ⋙ T₂₀)
    (δ : R₂₁ ⋙ R₁₀ ≅ R₂₀) (ε : T₂₁ ⋙ T₁₀ ≅ T₂₀)
    (h : ∀ N, r.app (R₂₁.obj N) ≫ T₁₀.map (s.app N) ≫ ε.hom.app (F₂.obj N) =
      F₀.map (δ.hom.app N) ≫ t.app N) (M : A₀) :
    (((d.comp e).ofNatIsoRight ε).leftAdjointUniq f).hom.app (F₀.obj M) ≫
        ((mateEquiv c f).symm t).natTrans.app M =
      S₁₂.map (((mateEquiv a d).symm r).natTrans.app M) ≫
        ((mateEquiv b e).symm s).natTrans.app (L₀₁.obj M) ≫
        F₂.map ((((a.comp b).ofNatIsoRight δ).leftAdjointUniq c).hom.app M) := by
  let q := (mateEquiv a d).symm r
  let q' := (mateEquiv b e).symm s
  let q'' := (mateEquiv c f).symm t
  let α := TwoSquare.vComp q q'
  let i := ((a.comp b).ofNatIsoRight δ).leftAdjointUniq c
  let j := ((d.comp e).ofNatIsoRight ε).leftAdjointUniq f
  have hm : mateEquiv (a.comp b) (d.comp e) α = TwoSquare.hComp s r := by
    rw [mateEquiv_hcomp]
    simp only [q, q', Equiv.apply_symm_apply]
  have hl := conjugateEquiv_mateEquiv_vcomp c (a.comp b) (d.comp e) i.hom α
  have hr := mateEquiv_conjugateEquiv_vcomp c f (d.comp e) q'' j.hom
  rw [hm, conjugate_uniqueness] at hl
  simp only [q'', Equiv.apply_symm_apply, j, conjugate_uniqueness] at hr
  have he : α.whiskerLeft i.hom = q''.whiskerRight j.hom := by
    apply (mateEquiv c (d.comp e)).injective
    rw [hl, hr]
    ext N
    dsimp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp]
    simp only [Category.id_comp, Category.comp_id]
    change F₀.map (δ.inv.app N) ≫
        (r.app (R₂₁.obj N) ≫ T₁₀.map (s.app N)) =
      t.app N ≫ ε.inv.app (F₂.obj N)
    apply (cancel_mono (ε.hom.app (F₂.obj N))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [h, ← Category.assoc, ← F₀.map_comp]
    simp
  have hx := congrArg (fun z ↦ z.natTrans.app M) he
  dsimp [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, α, TwoSquare.vComp] at hx
  simpa only [Category.id_comp, Category.comp_id, Category.assoc] using hx.symm

set_option backward.defeqAttrib.useBackward true in
private theorem scalar_mate_unit
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ A} {R : A ⥤ A} {S : B ⥤ B} {T : B ⥤ B}
    (a : L ⊣ R) (b : S ⊣ T) (F : A ⥤ B)
    (r : R ⋙ F ⟶ F ⋙ T) (δ : R ≅ 𝟭 A) (ε : T ≅ 𝟭 B)
    (h : ∀ N, F.map (δ.inv.app N) ≫ r.app N = ε.inv.app (F.obj N)) (M : A) :
    ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ r)).natTrans.app M ≫
        F.map (((a.ofNatIsoRight δ).leftAdjointUniq Adjunction.id).hom.app M) =
      ((b.ofNatIsoRight ε).leftAdjointUniq Adjunction.id).hom.app (F.obj M) := by
  let i := (a.ofNatIsoRight δ).leftAdjointUniq Adjunction.id
  let j := (b.ofNatIsoRight ε).leftAdjointUniq Adjunction.id
  have hi : a.unit.app M ≫ R.map (i.hom.app M) = δ.inv.app M := by
    have ht := Adjunction.homEquiv_leftAdjointUniq_hom_app
      (a.ofNatIsoRight δ) Adjunction.id M
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit] at ht
    apply (cancel_mono (δ.hom.app M)).1
    simpa only [i, Functor.id_obj, Adjunction.id_unit, NatTrans.id_app, Iso.inv_hom_id_app,
      Category.assoc] using ht
  have hj : b.unit.app (F.obj M) ≫ T.map (j.hom.app (F.obj M)) =
      ε.inv.app (F.obj M) := by
    have ht := Adjunction.homEquiv_leftAdjointUniq_hom_app
      (b.ofNatIsoRight ε) Adjunction.id (F.obj M)
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit] at ht
    apply (cancel_mono (ε.hom.app (F.obj M))).1
    simpa only [j, Functor.id_obj, Adjunction.id_unit, NatTrans.id_app, Iso.inv_hom_id_app,
      Category.assoc] using ht
  have hm := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ r) M
  change F.map (a.unit.app M) ≫ r.app (L.obj M) =
    b.unit.app (F.obj M) ≫
      T.map (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ r)).natTrans.app M) at hm
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [← hm]
  simp only [Category.assoc]
  erw [← r.naturality (i.hom.app M)]
  change F.map (a.unit.app M) ≫ F.map (R.map (i.hom.app M)) ≫ r.app M = _
  rw [← F.map_comp_assoc, hi, h, hj]


set_option backward.defeqAttrib.useBackward true in
private theorem mate_whisker
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {F F' : A ⥤ C} {G G' : B ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') (t : TwoSquare F L L' G)
    (f : F' ⟶ F) (g : G ⟶ G') :
    (mateEquiv a b ((t.whiskerTop f).whiskerBottom g)).natTrans =
      Functor.whiskerLeft R f ≫ (mateEquiv a b t).natTrans ≫
        Functor.whiskerRight g R' := by
  ext N
  dsimp only [TwoSquare.natTrans]
  simp only [mateEquiv_apply, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Category.id_comp, Functor.map_comp, Category.assoc]
  rw [← b.unit_naturality_assoc]
  dsimp only [TwoSquare.natTrans]
  simp only [Functor.comp_map]
  have hg := congrArg R'.map (g.naturality (a.counit.app N))
  simp only [R'.map_comp] at hg
  rw [← reassoc_of% hg]
  simp

set_option backward.defeqAttrib.useBackward true in
private theorem mate_pasting
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    {L₀ : A₀ ⥤ B₀} {R₀ : B₀ ⥤ A₀} {L₁ : A₁ ⥤ B₁} {R₁ : B₁ ⥤ A₁}
    {L₂ : A₂ ⥤ B₂} {R₂ : B₂ ⥤ A₂}
    {U : A₀ ⥤ A₁} {V : A₁ ⥤ A₂} {W : A₀ ⥤ A₂}
    {U' : B₀ ⥤ B₁} {V' : B₁ ⥤ B₂} {W' : B₀ ⥤ B₂}
    (a : L₀ ⊣ R₀) (b : L₁ ⊣ R₁) (c : L₂ ⊣ R₂)
    (r : U ⋙ L₁ ⟶ L₀ ⋙ U') (s : V ⋙ L₂ ⟶ L₁ ⋙ V')
    (t : W ⋙ L₂ ⟶ L₀ ⋙ W') (i : W ≅ U ⋙ V) (j : W' ≅ U' ⋙ V')
    (h : ∀ M, L₂.map (i.hom.app M) ≫ s.app (U.obj M) ≫ V'.map (r.app M) =
      t.app M ≫ j.hom.app (L₀.obj M)) (N : B₀) :
    i.hom.app (R₀.obj N) ≫ V.map ((mateEquiv a b (TwoSquare.mk _ _ _ _ r)).natTrans.app N) ≫
        (mateEquiv b c (TwoSquare.mk _ _ _ _ s)).natTrans.app (U'.obj N) =
      (mateEquiv a c (TwoSquare.mk _ _ _ _ t)).natTrans.app N ≫ R₂.map (j.hom.app N) := by
  let α : TwoSquare (U ⋙ V) L₀ L₂ (U' ⋙ V') :=
    TwoSquare.hComp (TwoSquare.mk _ _ _ _ r) (TwoSquare.mk _ _ _ _ s)
  have ht : TwoSquare.mk _ _ _ _ t = (α.whiskerTop i.hom).whiskerBottom j.inv := by
    ext M
    dsimp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, α, TwoSquare.hComp]
    simp only [Category.id_comp, Category.comp_id, Category.assoc]
    apply (cancel_mono (j.hom.app (L₀.obj M))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    simpa [TwoSquare.mk, TwoSquare.natTrans, Category.assoc] using (h M).symm
  have hm := congrArg (fun z ↦ (mateEquiv a c z).natTrans) ht
  rw [mate_whisker] at hm
  have hp := congrArg TwoSquare.natTrans (mateEquiv_vcomp a b c (TwoSquare.mk _ _ _ _ r)
    (TwoSquare.mk _ _ _ _ s))
  change (mateEquiv a c α).natTrans = _ at hp
  rw [hp] at hm
  have hn := congrArg (fun z ↦ z.app N) hm
  simp only [TwoSquare.vComp, TwoSquare.natTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc] at hn
  change _ = (mateEquiv a c (TwoSquare.mk _ _ _ _ t)).app N ≫ R₂.map (j.hom.app N)
  rw [hn]
  simp only [← R₂.map_comp, Iso.inv_hom_id_app, R₂.map_id, Category.assoc]
  simp only [TwoSquare.natTrans]
  erw [Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
private theorem mate_identity
    {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {R : B ⥤ A}
    (a : L ⊣ R) {U : A ⥤ A} {V : B ⥤ B}
    (r : U ⋙ L ⟶ L ⋙ V) (i : U ≅ 𝟭 A) (j : V ≅ 𝟭 B)
    (h : ∀ M, L.map (i.hom.app M) = r.app M ≫ j.hom.app (L.obj M)) (N : B) :
    (mateEquiv a a (TwoSquare.mk _ _ _ _ r)).natTrans.app N ≫ R.map (j.hom.app N) =
      i.hom.app (R.obj N) := by
  have hr : r.app (R.obj N) ≫ j.hom.app (L.obj (R.obj N)) =
      L.map (i.hom.app (R.obj N)) := (h _).symm
  rw [mateEquiv_apply]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Functor.comp_map, TwoSquare.natTrans, TwoSquare.mk, Category.id_comp,
    Category.assoc]
  erw [Category.id_comp]
  change a.unit.app (U.obj (R.obj N)) ≫ R.map (r.app (R.obj N)) ≫
    R.map (V.map (a.counit.app N)) ≫ R.map (j.hom.app N) = _
  have hj := j.hom.naturality (a.counit.app N)
  dsimp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hj
  rw [← R.map_comp, hj, R.map_comp]
  rw [← R.map_comp_assoc, hr]
  have hu := a.unit.naturality (i.hom.app (R.obj N))
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hu
  rw [← reassoc_of% hu]
  rw [a.right_triangle_components, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
private theorem inverseMate_identity
    {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {R : B ⥤ A}
    (a : L ⊣ R) {F : A ⥤ A} {G : B ⥤ B}
    (r : R ⋙ F ⟶ G ⋙ R) (i : F ≅ 𝟭 A) (j : G ≅ 𝟭 B)
    (h : ∀ N, r.app N ≫ R.map (j.hom.app N) = i.hom.app (R.obj N)) (M : A) :
    L.map (i.hom.app M) =
      ((mateEquiv a a).symm (TwoSquare.mk _ _ _ _ r)).natTrans.app M ≫
        j.hom.app (L.obj M) := by
  have hm := unit_mateEquiv_symm a a (TwoSquare.mk _ _ _ _ r) M
  change F.map (a.unit.app M) ≫ r.app (L.obj M) =
    a.unit.app (F.obj M) ≫
      R.map (((mateEquiv a a).symm (TwoSquare.mk _ _ _ _ r)).natTrans.app M) at hm
  apply (a.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [← hm]
  simp only [Category.assoc]
  rw [h]
  have hu := a.unit.naturality (i.hom.app M)
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  rw [← hu]
  exact (i.hom.naturality (a.unit.app M)).symm

private theorem reverse_square
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y : A} {U V : B} (i : X ≅ Y) (j : U ≅ V)
    (r : F.obj Y ⟶ V) (s : F.obj X ⟶ U)
    (h : F.map i.inv ≫ s = r ≫ j.inv) :
    F.map i.hom ≫ r = s ≫ j.hom := by
  apply (cancel_epi (F.map i.inv)).1
  simp only [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
  rw [reassoc_of% h]
  simp

private theorem exact_unit_square
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (R : A ⥤ A) (S : B ⥤ B) (T : A ⥤ B)
    [R.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (ρ : R ⋙ T ≅ T ⋙ S) (η : R ≅ 𝟭 A) (θ : S ≅ 𝟭 B)
    (h : ∀ M, ρ.hom.app M ≫ θ.hom.app (T.obj M) = T.map (η.hom.app M))
    (M : DerivedCategory A) :
    (Functor.mapDerivedCategorySquareIso ρ).hom.app M ≫
        (Functor.exactDerivedRestrictionUnit S θ).hom.app (T.mapDerivedCategory.obj M) =
      T.mapDerivedCategory.map ((Functor.exactDerivedRestrictionUnit R η).hom.app M) := by
  have hρ : ρ ≪≫ Functor.isoWhiskerLeft T θ = Functor.isoWhiskerRight η T := by
    ext N
    exact h N
  have hd := congrArg (fun i ↦ (Functor.mapDerivedCategoryNatIso i).hom) hρ
  rw [Functor.mapDerivedCategoryNatIso_trans] at hd
  have hl := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft T θ
  have hr := Functor.mapDerivedCategoryNatIso_isoWhiskerRight η T
  have hul := Functor.mapDerivedCategoryCompIso_id_comp T
  have hur := Functor.mapDerivedCategoryCompIso_comp_id T
  have hl' := congrArg (fun t ↦ t ≫ Functor.whiskerLeft T.mapDerivedCategory
    (Functor.mapDerivedCategoryIdIso B).hom) hl
  have hr' := congrArg (fun t ↦ t ≫ Functor.whiskerRight
    (Functor.mapDerivedCategoryIdIso A).hom T.mapDerivedCategory) hr
  simp only [Category.assoc, hur] at hl'
  simp only [Category.assoc, hul] at hr'
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso R T).hom.app M)).1
  simp only [Functor.mapDerivedCategorySquareIso, Functor.exactDerivedRestrictionUnit,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_app_assoc]
  have hlM := NatTrans.congr_app hl' M
  have hrM := NatTrans.congr_app hr' M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hlM hrM
  rw [← hlM, ← hrM]
  simpa only [NatTrans.comp_app, Category.assoc] using
    congrArg (fun f ↦ f ≫ NatTrans.app (𝟙 T.mapDerivedCategory) M) (NatTrans.congr_app hd M)

open WeilConjectures.SemilinearSections

private abbrev ordinaryComp (W : Scheme.{u}) {B C D : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    (a : B ⟶ C) (b : C ⟶ D) :
    res (ringMap W b) ⋙ res (ringMap W a) ≅ res (ringMap W (a ≫ b)) :=
  SheafOfModules.systemScalarRestrictionComposition.{u + 1, u, u + 1}
    (ringMap W a) (ringMap W b) (ringMap W (a ≫ b))
    ((coefficientFunctor W).map_comp a b)

private abbrev derivedComp (W : Scheme.{u}) {B C D : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    (a : B ⟶ C) (b : C ⟶ D) :
    restriction W b ⋙ restriction W a ≅ restriction W (a ≫ b) :=
  Functor.exactDerivedRestrictionComposition _ _ _ (ordinaryComp W a b)

private abbrev ordinaryUnit (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    res (ringMap W (𝟙 B)) ≅ 𝟭 (Modules W B) :=
  SheafOfModules.systemScalarRestrictionUnit.{u + 1, u, u + 1}
    (ringMap W (𝟙 B)) ((coefficientFunctor W).map_id B)

private abbrev derivedUnit (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    restriction W (𝟙 B) ≅ 𝟭 (Derived W B) :=
  Functor.exactDerivedRestrictionUnit _ (ordinaryUnit W B)

private theorem ordinary_image_comp
    {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B C D : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {a : B ⟶ C} {b : C ⟶ D}
    {d : Image g B} {e : Image g C} {f : Image g D}
    (r : RestrictionImage a d e) (s : RestrictionImage b e f)
    (t : RestrictionImage (a ≫ b) d f) (M : Modules X D) :
    d.toDirectImage.push.map ((ordinaryComp X a b).hom.app M) ≫ t.ordinary.hom.app M =
      r.ordinary.hom.app ((res (ringMap X b)).obj M) ≫
        (res (ringMap Y a)).map (s.ordinary.hom.app M) ≫
        (ordinaryComp Y a b).hom.app (f.toDirectImage.push.obj M) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rcases U with ⟨n, U⟩
  ext x
  change (t.ordinary.hom.app M).val.app (op (n, U)) x =
    (s.ordinary.hom.app M).val.app (op (n, U))
      ((r.ordinary.hom.app ((res (ringMap X b)).obj M)).val.app (op (n, U)) x)
  rw [eq_of_heq (r.sections _ n (op U) x)]
  exact (eq_of_heq (t.sections M n (op U) x)).trans
    (eq_of_heq (s.sections M n (op U) x)).symm

private theorem ordinary_image_unit
    {X Y : Scheme.{u}} {g : X ⟶ Y} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    {d : Image g B} (r : RestrictionImage (𝟙 B) d d) (M : Modules X B) :
    r.ordinary.hom.app M ≫ (ordinaryUnit Y B).hom.app (d.toDirectImage.push.obj M) =
      d.toDirectImage.push.map ((ordinaryUnit X B).hom.app M) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rcases U with ⟨n, U⟩
  ext x
  exact eq_of_heq (r.sections M n (op U) x)

private theorem ordinary_inverse_comp
    {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B C D : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {a : B ⟶ C} {b : C ⟶ D}
    {d : Image g B} {e : Image g C} {f : Image g D}
    (r : RestrictionImage a d e) (s : RestrictionImage b e f)
    (t : RestrictionImage (a ≫ b) d f) (M : Modules Y D) :
    d.inverse.map ((ordinaryComp Y a b).hom.app M) ≫ t.inverseImage.hom.app M =
      r.inverseImage.hom.app ((res (ringMap Y b)).obj M) ≫
        (res (ringMap X a)).map (s.inverseImage.hom.app M) ≫
        (ordinaryComp X a b).hom.app (f.inverse.obj M) := by
  have h := inverseMate_pasting f.adjunction e.adjunction d.adjunction
    s.ordinary.inv r.ordinary.inv t.ordinary.inv
    (ordinaryComp Y a b).inv (ordinaryComp X a b).inv (fun N ↦ by
      simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app, Category.assoc] using
        ((IsIso.inv_eq_inv).2 (ordinary_image_comp r s t N)).symm) M
  rw [← r.inverseImage_mate, ← s.inverseImage_mate, ← t.inverseImage_mate] at h
  exact reverse_square d.inverse ((ordinaryComp Y a b).app M)
    ((ordinaryComp X a b).app (f.inverse.obj M)) _ _ h

private theorem ordinary_inverse_unit
    {X Y : Scheme.{u}} {g : X ⟶ Y} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    {d : Image g B} (r : RestrictionImage (𝟙 B) d d) (M : Modules Y B) :
    r.inverseImage.hom.app M ≫ (ordinaryUnit X B).hom.app (d.inverse.obj M) =
      d.inverse.map ((ordinaryUnit Y B).hom.app M) := by
  rw [r.inverseImage_mate]
  symm
  apply inverseMate_identity d.adjunction r.ordinary.inv (ordinaryUnit Y B)
    (ordinaryUnit X B) (fun N ↦ ?_) M
  apply (cancel_epi (r.ordinary.hom.app N)).1
  simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using
    (ordinary_image_unit r N).symm

private theorem derived_inverse_comp
    {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B C D : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {a : B ⟶ C} {b : C ⟶ D}
    {d : Image g B} {e : Image g C} {f : Image g D}
    (r : RestrictionImage a d e) (s : RestrictionImage b e f)
    (t : RestrictionImage (a ≫ b) d f) (M : Derived Y D) :
    d.P.map ((derivedComp Y a b).hom.app M) ≫ t.derivedInverse.hom.app M =
      r.derivedInverse.hom.app ((restriction Y b).obj M) ≫
        (restriction X a).map (s.derivedInverse.hom.app M) ≫
        (derivedComp X a b).hom.app (f.P.obj M) := by
  have := d.inverseAdditive
  have := d.inverseLimits
  have := d.inverseColimits
  have := e.inverseAdditive
  have := e.inverseLimits
  have := e.inverseColimits
  have := f.inverseAdditive
  have := f.inverseLimits
  have := f.inverseColimits
  have hd := Functor.mapDerivedCategorySquareIso_comp
    (res (ringMap Y b)) (res (ringMap Y a)) (res (ringMap Y (a ≫ b)))
    (res (ringMap X b)) (res (ringMap X a)) (res (ringMap X (a ≫ b)))
    f.inverse e.inverse d.inverse s.inverseImage r.inverseImage t.inverseImage
    (ordinaryComp Y a b).symm (ordinaryComp X a b).symm (fun N ↦ ?_)
  · rw [← r.derivedInverse_termwise, ← s.derivedInverse_termwise,
      ← t.derivedInverse_termwise] at hd
    have h := congrArg (fun z ↦ z.hom.app M) hd
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.comp_app,
      Category.id_comp, Category.comp_id] at h
    have h' : d.P.map ((derivedComp Y a b).inv.app M) ≫
        r.derivedInverse.hom.app ((restriction Y b).obj M) ≫
          (restriction X a).map (s.derivedInverse.hom.app M) =
        t.derivedInverse.hom.app M ≫ (derivedComp X a b).inv.app (f.P.obj M) := by
      simpa only [derivedComp,
        Functor.exactDerivedRestrictionComposition, Functor.mapDerivedCategoryNatIso_symm,
        Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app, Category.assoc] using h
    simpa only [Category.assoc, Iso.app_hom, Functor.comp_obj] using
      reverse_square d.P ((derivedComp Y a b).app M)
        ((derivedComp X a b).app (f.P.obj M)) _ _ h'
  · exact reverse_square d.inverse
      ((ordinaryComp Y a b).app N).symm
      ((ordinaryComp X a b).app (f.inverse.obj N)).symm _ _
      (ordinary_inverse_comp r s t N)

private theorem derived_inverse_unit
    {X Y : Scheme.{u}} {g : X ⟶ Y} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    {d : Image g B} (r : RestrictionImage (𝟙 B) d d) (M : Derived Y B) :
    r.derivedInverse.hom.app M ≫ (derivedUnit X B).hom.app (d.P.obj M) =
      d.P.map ((derivedUnit Y B).hom.app M) := by
  have := d.inverseAdditive
  have := d.inverseLimits
  have := d.inverseColimits
  rw [r.derivedInverse_termwise]
  exact exact_unit_square _ _ d.inverse r.inverseImage (ordinaryUnit Y B)
    (ordinaryUnit X B) (ordinary_inverse_unit r) M

private theorem derived_image_comp
    {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B C D : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {a : B ⟶ C} {b : C ⟶ D}
    {d : Image g B} {e : Image g C} {f : Image g D}
    (r : RestrictionImage a d e) (s : RestrictionImage b e f)
    (t : RestrictionImage (a ≫ b) d f) (M : Derived X D) :
    t.derived.hom.app M ≫ d.R.map ((derivedComp X a b).inv.app M) =
      (derivedComp Y a b).inv.app (f.R.obj M) ≫
        (restriction Y a).map (s.derived.hom.app M) ≫
        r.derived.hom.app ((restriction X b).obj M) := by
  rw [r.derived_mate, s.derived_mate, t.derived_mate]
  exact (mate_pasting f.derivedAdjunction e.derivedAdjunction d.derivedAdjunction
    s.derivedInverse.hom r.derivedInverse.hom t.derivedInverse.hom
    (derivedComp Y a b).symm (derivedComp X a b).symm (fun N ↦ by
      simpa only [Category.assoc, Iso.app_hom, Iso.app_inv, Iso.symm_hom, Iso.symm_inv,
        Functor.comp_obj] using
        reverse_square d.P ((derivedComp Y a b).app N).symm
          ((derivedComp X a b).app (f.P.obj N)).symm _ _
          (by simpa only [Category.assoc, Iso.app_hom, Iso.symm_inv,
            Functor.comp_obj] using derived_inverse_comp r s t N)) M).symm

private theorem derived_image_unit
    {X Y : Scheme.{u}} {g : X ⟶ Y} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    {d : Image g B} (r : RestrictionImage (𝟙 B) d d) (M : Derived X B) :
    r.derived.hom.app M ≫ d.R.map ((derivedUnit X B).hom.app M) =
      (derivedUnit Y B).hom.app (d.R.obj M) := by
  rw [r.derived_mate]
  exact mate_identity d.derivedAdjunction r.derivedInverse.hom
    (derivedUnit Y B) (derivedUnit X B) (fun N ↦ (derived_inverse_unit r N).symm) M

private theorem ordinary_open_comp
    {X Z : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    {B C D : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {a : B ⟶ C} {b : C ⟶ D}
    {d : OpenImage j B} {e : OpenImage j C} {f : OpenImage j D}
    (r : RestrictionOpen a d e) (s : RestrictionOpen b e f)
    (t : RestrictionOpen (a ≫ b) d f) (M : Modules X D) :
    d.extension.map ((ordinaryComp X a b).hom.app M) ≫ t.ordinary.hom.app M =
      r.ordinary.hom.app ((res (ringMap X b)).obj M) ≫
        (res (ringMap Z a)).map (s.ordinary.hom.app M) ≫
        (ordinaryComp Z a b).hom.app (f.extension.obj M) := by
  have h := inverseMate_pasting f.openAdjunction e.openAdjunction d.openAdjunction
    s.image.inverseImage.inv r.image.inverseImage.inv t.image.inverseImage.inv
    (ordinaryComp X a b).inv (ordinaryComp Z a b).inv (fun N ↦ by
      simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app, Category.assoc] using
        ((IsIso.inv_eq_inv).2 (ordinary_inverse_comp r.image s.image t.image N)).symm) M
  rw [← r.mate, ← s.mate, ← t.mate] at h
  exact reverse_square d.extension ((ordinaryComp X a b).app M)
    ((ordinaryComp Z a b).app (f.extension.obj M)) _ _ h

private theorem ordinary_open_unit
    {X Z : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {d : OpenImage j B}
    (r : RestrictionOpen (𝟙 B) d d) (M : Modules X B) :
    r.ordinary.hom.app M ≫ (ordinaryUnit Z B).hom.app (d.extension.obj M) =
      d.extension.map ((ordinaryUnit X B).hom.app M) := by
  rw [r.mate]
  symm
  apply inverseMate_identity d.openAdjunction r.image.inverseImage.inv (ordinaryUnit X B)
    (ordinaryUnit Z B) (fun N ↦ ?_) M
  apply (cancel_epi (r.image.inverseImage.hom.app N)).1
  simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using
    (ordinary_inverse_unit r.image N).symm

private theorem derived_open_comp
    {X Y : Scheme.{u}} {g : X ⟶ Y} [IsOpenImmersion g]
    {B C D : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {a : B ⟶ C} {b : C ⟶ D}
    {d : OpenImage g B} {e : OpenImage g C} {f : OpenImage g D}
    (r : RestrictionOpen a d e) (s : RestrictionOpen b e f)
    (t : RestrictionOpen (a ≫ b) d f) (M : Derived X D) :
    d.J.map ((derivedComp X a b).hom.app M) ≫ t.derived.hom.app M =
      r.derived.hom.app ((restriction X b).obj M) ≫
        (restriction Y a).map (s.derived.hom.app M) ≫
        (derivedComp Y a b).hom.app (f.J.obj M) := by
  have := d.extensionAdditive
  have := d.extensionLimits
  have := d.extensionColimits
  have := e.extensionAdditive
  have := e.extensionLimits
  have := e.extensionColimits
  have := f.extensionAdditive
  have := f.extensionLimits
  have := f.extensionColimits
  have hd := Functor.mapDerivedCategorySquareIso_comp
    (res (ringMap X b)) (res (ringMap X a)) (res (ringMap X (a ≫ b)))
    (res (ringMap Y b)) (res (ringMap Y a)) (res (ringMap Y (a ≫ b)))
    f.extension e.extension d.extension s.ordinary r.ordinary t.ordinary
    (ordinaryComp X a b).symm (ordinaryComp Y a b).symm (fun N ↦ ?_)
  · have h := congrArg (fun z ↦ z.hom.app M) hd
    simp only [Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.comp_app,
      Category.id_comp, Category.comp_id] at h
    have h' : d.J.map ((derivedComp X a b).inv.app M) ≫
        r.derived.hom.app ((restriction X b).obj M) ≫
          (restriction Y a).map (s.derived.hom.app M) =
        t.derived.hom.app M ≫ (derivedComp Y a b).inv.app (f.J.obj M) := by
      simpa only [RestrictionOpen.derived, Functor.mapDerivedCategorySquareIso,
        Iso.trans_hom, derivedComp,
        Functor.exactDerivedRestrictionComposition, Functor.mapDerivedCategoryNatIso_symm,
        Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app, Category.assoc] using h
    simpa only [Category.assoc, Iso.app_hom, Functor.comp_obj] using
      reverse_square d.J ((derivedComp X a b).app M)
        ((derivedComp Y a b).app (f.J.obj M)) _ _ h'
  · exact reverse_square d.extension
      ((ordinaryComp X a b).app N).symm
      ((ordinaryComp Y a b).app (f.extension.obj N)).symm _ _
      (ordinary_open_comp r s t N)

private theorem derived_open_unit
    {X Z : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {d : OpenImage j B}
    (r : RestrictionOpen (𝟙 B) d d) (M : Derived X B) :
    r.derived.hom.app M ≫ (derivedUnit Z B).hom.app (d.J.obj M) =
      d.J.map ((derivedUnit X B).hom.app M) := by
  have := d.extensionAdditive
  have := d.extensionLimits
  have := d.extensionColimits
  exact exact_unit_square _ _ d.extension r.ordinary (ordinaryUnit X B)
    (ordinaryUnit Z B) (ordinary_open_unit r) M

private theorem derived_image_inverse_comp
    {X Y : Scheme.{u}} {g : X ⟶ Y}
    {B C D : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {a : B ⟶ C} {b : C ⟶ D}
    {d : Image g B} {e : Image g C} {f : Image g D}
    (r : RestrictionImage a d e) (s : RestrictionImage b e f)
    (t : RestrictionImage (a ≫ b) d f) (M : Derived X D) :
    d.R.map ((derivedComp X a b).hom.app M) ≫ t.derived.inv.app M =
      r.derived.inv.app ((restriction X b).obj M) ≫
        (restriction Y a).map (s.derived.inv.app M) ≫
        (derivedComp Y a b).hom.app (f.R.obj M) := by
  simpa only [IsIso.inv_comp, ← Functor.map_inv, NatIso.inv_hom_app, NatIso.inv_inv_app,
    Category.assoc] using (IsIso.inv_eq_inv).2 (derived_image_comp r s t M)

private theorem derived_image_inverse_unit
    {X Y : Scheme.{u}} {g : X ⟶ Y} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    {d : Image g B} (r : RestrictionImage (𝟙 B) d d) (M : Derived X B) :
    r.derived.inv.app M ≫ (derivedUnit Y B).hom.app (d.R.obj M) =
      d.R.map ((derivedUnit X B).hom.app M) := by
  apply (cancel_epi (r.derived.hom.app M)).1
  simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using
    (derived_image_unit r M).symm

private theorem support_inverse_comp
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {B C D : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {a : B ⟶ C} {b : C ⟶ D}
    {d : Support c B} {e : Support c C} {g : Support c D}
    (r : RestrictionSupport a d e) (s : RestrictionSupport b e g)
    (t : RestrictionSupport (a ≫ b) d g) (M : Derived X D) :
    d.F.map ((derivedComp X a b).hom.app M) ≫ t.iso.inv.app M =
      r.iso.inv.app ((restriction X b).obj M) ≫
        (restriction Y a).map (s.iso.inv.app M) ≫
        (derivedComp Y a b).hom.app (g.F.obj M) := by
  have hn := r.proper.derived.inv.naturality (s.openImage.derived.hom.app M)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  dsimp only [RestrictionSupport.iso, Support.F, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_map, Functor.comp_obj]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  rw [← d.proper.R.map_comp_assoc, derived_open_comp r.openImage s.openImage t.openImage M]
  simp only [Functor.map_comp, Category.assoc]
  rw [derived_image_inverse_comp r.proper s.proper t.proper]
  rw [reassoc_of% hn]

private theorem support_inverse_unit
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {d : Support c B}
    (r : RestrictionSupport (𝟙 B) d d) (M : Derived X B) :
    r.iso.inv.app M ≫ (derivedUnit Y B).hom.app (d.F.obj M) =
      d.F.map ((derivedUnit X B).hom.app M) := by
  dsimp only [RestrictionSupport.iso, Support.F, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.comp_map, Functor.comp_obj]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  rw [derived_image_inverse_unit r.proper, ← d.proper.R.map_comp, derived_open_unit r.openImage]

/-- Normalized scalar mates obey coefficient composition and the identity law.
Source: Zheng Construction 2.26, Lemma 5.16; Stacks Tag 0GL6
(blueprint: lem-pur-etale-system-projection-coherence).

Proof: On ordinary sheaves the scalar-restriction/direct-image comparisons are
identity on every section, so they obey composition and the identity law. Taking
inverse-image mates preserves these equations by mate pasting. Exact localization
preserves compositions, identities and their canonical compositors. For the open
factor, apply the same pasting identities to its defining inverse-image mate.
Consequently the proper/open restriction comparison obeys the coefficient cocycle
and identity law, with the canonical exact restriction compositors. Take inverse
scalar-adjunction mates. The conjugate of the restriction compositor is precisely
the balanced associator used in Theory.path, because both are normalized by
successive scalar unit insertion. Mate pasting therefore gives the first equation.
For identity coefficients, its conjugate is the unit comparison in the statement;
the scalar triangle identity gives the second equation. These equations are on
entire system categories, before evaluating any object at a coefficient level. -/
theorem etaleSystemProjection_coherence
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (l : ℕ) (t : Theory c l) :
    (∀ (B C D : Coefficients.{u} l) (a : B.rings ⟶ C.rings) (b : C.rings ⟶ D.rings),
        t.q (a ≫ b) = t.path a b) ∧
    (∀ (B : Coefficients.{u} l) (M : Derived X B.rings),
        (t.q (𝟙 B.rings)).app M ≫
          (t.support B).F.map ((unit X B.rings (t.scalarX (𝟙 B.rings))).hom.app M) =
        (unit Y B.rings (t.scalarY (𝟙 B.rings))).hom.app ((t.support B).F.obj M)) := by
  constructor
  · intro B C D a b
    apply NatTrans.ext
    funext M
    apply (cancel_epi ((associator Y (t.scalarY a) (t.scalarY b)
      (t.scalarY (a ≫ b))).hom.app ((t.support B).F.obj M))).1
    simp only [Theory.path, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Iso.hom_inv_id_app_assoc]
    exact scalar_mate_composition
      (t.scalarX a).adjunction (t.scalarX b).adjunction (t.scalarX (a ≫ b)).adjunction
      (t.scalarY a).adjunction (t.scalarY b).adjunction (t.scalarY (a ≫ b)).adjunction
      (t.restriction a).iso.inv (t.restriction b).iso.inv (t.restriction (a ≫ b)).iso.inv
      (derivedComp X a b) (derivedComp Y a b)
      (fun N ↦ (support_inverse_comp (t.restriction a) (t.restriction b)
        (t.restriction (a ≫ b)) N).symm) M
  · intro B M
    exact scalar_mate_unit (t.scalarX (𝟙 B.rings)).adjunction
      (t.scalarY (𝟙 B.rings)).adjunction (t.support B).F
      (t.restriction (𝟙 B.rings)).iso.inv (derivedUnit X B.rings) (derivedUnit Y B.rings)
      (fun N ↦ by
        apply (cancel_mono ((derivedUnit Y B.rings).hom.app ((t.support B).F.obj N))).1
        rw [Category.assoc, support_inverse_unit (t.restriction (𝟙 B.rings)) N,
          ← (t.support B).F.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
          Iso.inv_hom_id_app]
        rfl) M

end AlgebraicGeometry.Etale.SystemProjection
