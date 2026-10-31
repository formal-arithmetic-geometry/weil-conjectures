/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenCalculus
import all WeilConjectures.SixFunctors.AmbientCompositor.Operations.AmbientAdjunctionCompositorNormalization
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.RingSheaf.UpperStarSquare
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedPullbackTensorComposition
import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.OrdinaryAmbientProperOpenLaws
import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.PublishedSystemTensorComposition

/-! # Assembly of ambient proper/open coherence
Source: Stacks 0F7B--0F7D, 03EL and 07A4. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u g h v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AmbientProperOpen
variable {G : Type g} [Category.{h} G] {geo : G ⥤ Scheme.{u}}

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  upperStar lowerStar Functor.rightDerivedFunctor
  Functor.leftAdjoint constantSheaf

private theorem three_two_congr {C : Type*} [Category C]
    {X₀ X₁ X₂ X₃ X₄ : C}
    {a a' : X₀ ⟶ X₁} {b b' : X₁ ⟶ X₂} {c c' : X₂ ⟶ X₃}
    {d d' : X₀ ⟶ X₄} {e e' : X₄ ⟶ X₃}
    (ha : a = a') (hb : b = b') (hc : c = c') (hd : d = d') (he : e = e')
    (h : a' ≫ b' ≫ c' = d' ≫ e') : a ≫ b ≫ c = d ≫ e := by
  rw [ha, hb, hc, hd, he]
  exact h

private theorem two_one_congr {C : Type*} [Category C] {X₀ X₁ X₂ : C}
    {a a' : X₀ ⟶ X₁} {b b' : X₁ ⟶ X₂} {c c' : X₀ ⟶ X₂}
    (ha : a = a') (hb : b = b') (hc : c = c') (h : a' ≫ b' = c') : a ≫ b = c := by
  rw [ha, hb, hc]
  exact h

private abbrev coherenceD (o : Calculus.{u, g, h, v, w} G geo)
    {X Y Z : G} (f : X ⟶ Y) (g : Y ⟶ Z) := (o.pComp f g).symm

-- The two generic conjugation calculations use only the public mate API.
attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem conjugate_left_unit {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {R : D ⥤ C} {I RI : D ⥤ D}
    (a : F ⊣ R) (b : I ⊣ RI) (e : I ≅ 𝟭 D) (k : F ≅ F ⋙ I)
    (h : k ≪≫ Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F = Iso.refl F) :
    conjugateIsoEquiv (a.comp b) a k =
      Functor.isoWhiskerRight (conjugateIsoEquiv b Adjunction.id e.symm) R ≪≫
        Functor.leftUnitor R := by
  have hk : k = (Functor.rightUnitor F).symm ≪≫
      Functor.isoWhiskerLeft F e.symm := by
    apply Iso.ext
    have hh := congrArg Iso.hom h
    change k.hom ≫ (Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F).hom = 𝟙 _ at hh
    have hi := (Iso.comp_hom_eq_id
      (Functor.isoWhiskerLeft F e ≪≫ Functor.rightUnitor F)).1 hh
    simpa only [Iso.trans_hom, Iso.trans_inv, Functor.isoWhiskerLeft_symm,
      Iso.symm_hom, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerLeft_hom] using hi
  rw [hk, conjugateIsoEquiv_trans (a.comp b) (a.comp Adjunction.id) a,
    conjugateIsoEquiv_isoWhiskerLeft b Adjunction.id a,
    conjugateIsoEquiv_iso_symm a (a.comp Adjunction.id),
    conjugateIsoEquiv_rightUnitor, Iso.symm_symm_eq]

private theorem conjugate_transport
    {A B I : Type*} [Category A] [Category B]
    (L : I → A ⥤ B) (R₀ : I → B ⥤ A) (a : ∀ i, L i ⊣ R₀ i)
    {L' : A ⥤ B} {R' : B ⥤ A} (a' : L' ⊣ R')
    {i j : I} (e : i = j) (d : L i ≅ L') :
    conjugateIsoEquiv a' (a j) (eqToIso (congrArg L e.symm) ≪≫ d) =
      conjugateIsoEquiv a' (a i) d ≪≫ eqToIso (congrArg R₀ e) := by
  cases e
  simp

private theorem jId_eq (o : Calculus.{u, g, h, v, w} G geo) (X : G)
    [IsOpenImmersion (geo.map (𝟙 X))] :
    o.jId X = Adjunction.leftAdjointIdIso (o.openAdj (𝟙 X)) (o.pId X) := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply ((o.openAdj (𝟙 X)).homEquiv M M).injective
  erw [Calculus.jId, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  have hh := unit_conjugateEquiv Adjunction.id (o.openAdj (𝟙 X))
    ((o.openAdj (𝟙 X)).leftAdjointIdIso (o.pId X)).hom M
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom] at hh
  simpa only [Adjunction.homEquiv_unit, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Adjunction.id_unit,
    NatTrans.id_app, Functor.id_obj, Category.id_comp, Iso.symm_hom] using hh

private structure PullCoherence (o : Calculus.{u, g, h, v, w} G geo) : Prop where
  left_unit : ∀ {X Y : G} (f : X ⟶ Y),
    eqToIso (congrArg o.P (Category.id_comp f).symm) ≪≫ o.pComp (𝟙 X) f ≪≫
      Functor.isoWhiskerLeft (o.P f) (o.pId X) ≪≫ Functor.rightUnitor (o.P f) = Iso.refl _
  right_unit : ∀ {X Y : G} (f : X ⟶ Y),
    eqToIso (congrArg o.P (Category.comp_id f).symm) ≪≫ o.pComp f (𝟙 Y) ≪≫
      Functor.isoWhiskerRight (o.pId Y) (o.P f) ≪≫ Functor.leftUnitor (o.P f) = Iso.refl _

private theorem p_unital (o : Calculus.{u, g, h, v, w} G geo) (hp : PullCoherence o)
    {X Y : G} (f : X ⟶ Y) (M : o.D Y) :
    ((o.pComp (𝟙 X) f).hom.app M ≫ (o.pId X).hom.app ((o.P f).obj M) =
      (o.pCongr (Category.id_comp f)).hom.app M) ∧
    ((o.pComp f (𝟙 Y)).hom.app M ≫ (o.P f).map ((o.pId Y).hom.app M) =
      (o.pCongr (Category.comp_id f)).hom.app M) := by
  constructor
  · have hh := congr_app (congrArg Iso.hom (hp.left_unit f)) M
    change (eqToIso (congrArg o.P (Category.id_comp f))).inv.app M ≫
      ((o.pComp (𝟙 X) f).hom.app M ≫ (o.pId X).hom.app ((o.P f).obj M) ≫ 𝟙 _) =
        𝟙 _ at hh
    simp only [Category.comp_id] at hh
    change _ = (eqToIso (congrArg o.P (Category.id_comp f))).hom.app M
    apply (cancel_epi
      ((eqToIso (congrArg o.P (Category.id_comp f))).inv.app M)).1
    simpa only [Iso.inv_hom_id_app] using hh
  · have hh := congr_app (congrArg Iso.hom (hp.right_unit f)) M
    change (eqToIso (congrArg o.P (Category.comp_id f))).inv.app M ≫
      ((o.pComp f (𝟙 Y)).hom.app M ≫ (o.P f).map ((o.pId Y).hom.app M) ≫ 𝟙 _) =
        𝟙 _ at hh
    simp only [Category.comp_id] at hh
    change _ = (eqToIso (congrArg o.P (Category.comp_id f))).hom.app M
    apply (cancel_epi
      ((eqToIso (congrArg o.P (Category.comp_id f))).inv.app M)).1
    simpa only [Iso.inv_hom_id_app] using hh

private theorem j_comp_transport (o : Calculus.{u, g, h, v, w} G geo) {X Y Z : G}
    (f : X ⟶ Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    [IsOpenImmersion (geo.map f)] [IsOpenImmersion (geo.map g)]
    [IsOpenImmersion (geo.map k)] (e : f ≫ g = k) :
    Adjunction.leftAdjointCompIso (o.openAdj f) (o.openAdj g)
      (o.openAdj k) (coherenceD o f g ≪≫ eqToIso (congrArg o.P e)) =
        o.jComp f g ≪≫ o.jCongr e := by
  subst k
  simp only [Calculus.jCongr, eqToIso_refl, Iso.trans_refl, Calculus.jComp]

private theorem conjugate_right_unit
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {R : D ⥤ C} {I RI : C ⥤ C}
    (a : F ⊣ R) (b : I ⊣ RI) (e : I ≅ 𝟭 C) (k : F ≅ I ⋙ F)
    (h : k ≪≫ Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F = Iso.refl F) :
    conjugateIsoEquiv (b.comp a) a k =
      Functor.isoWhiskerLeft R (conjugateIsoEquiv b Adjunction.id e.symm) ≪≫
        Functor.rightUnitor R := by
  have hk : k = (Functor.leftUnitor F).symm ≪≫
      Functor.isoWhiskerRight e.symm F := by
    apply Iso.ext
    have hh := congrArg Iso.hom h
    change k.hom ≫ (Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F).hom = 𝟙 _ at hh
    have hi := (Iso.comp_hom_eq_id
      (Functor.isoWhiskerRight e F ≪≫ Functor.leftUnitor F)).1 hh
    simpa only [Iso.trans_hom, Iso.trans_inv, Functor.isoWhiskerRight_symm,
      Iso.symm_hom, Functor.isoWhiskerRight_inv, Functor.isoWhiskerRight_hom] using hi
  rw [hk, conjugateIsoEquiv_trans (b.comp a) (Adjunction.id.comp a) a,
    conjugateIsoEquiv_isoWhiskerRight b Adjunction.id a,
    conjugateIsoEquiv_iso_symm a (Adjunction.id.comp a),
    conjugateIsoEquiv_leftUnitor, Iso.symm_symm_eq]

private theorem c_eq (o : Calculus.{u, g, h, v, w} G geo) {X Y Z : G}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    o.sComp f g = conjugateIsoEquiv ((o.adj g).comp (o.adj f))
      (o.adj (f ≫ g)) (o.pComp f g) := rfl

private theorem sId_eq (o : Calculus.{u, g, h, v, w} G geo) (X : G) :
    o.sId X = conjugateIsoEquiv (o.adj (𝟙 X)) Adjunction.id (o.pId X).symm := rfl

private theorem s_unital (o : Calculus.{u, g, h, v, w} G geo) (hp : PullCoherence o)
    {X Y : G} (f : X ⟶ Y) (M : o.D X) :
    ((o.sComp (𝟙 X) f).hom.app M ≫
        (eqToIso (congrArg o.S (Category.id_comp f))).hom.app M =
      (o.S f).map ((o.sId X).hom.app M)) ∧
    ((o.sComp f (𝟙 Y)).hom.app M ≫
        (eqToIso (congrArg o.S (Category.comp_id f))).hom.app M =
      (o.sId Y).hom.app ((o.S f).obj M)) := by
  constructor
  · have hh := conjugate_left_unit (o.adj f)
      (o.adj (𝟙 X)) (o.pId X)
      (eqToIso (congrArg o.P (Category.id_comp f).symm) ≪≫ o.pComp (𝟙 X) f)
      (by simpa only [Iso.trans_assoc] using hp.left_unit f)
    rw [conjugate_transport o.P o.S
      (fun t ↦ o.adj t) ((o.adj f).comp (o.adj (𝟙 X)))
      (Category.id_comp f) (o.pComp (𝟙 X) f)] at hh
    have hm := congr_app (congrArg Iso.hom hh) M
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Functor.leftUnitor_hom_app] at hm
    conv_rhs at hm => erw [Category.comp_id]
    simpa only [c_eq, sId_eq, jId_eq] using hm
  · have hh := conjugate_right_unit (o.adj f) (o.adj (𝟙 Y)) (o.pId Y)
      (eqToIso (congrArg o.P (Category.comp_id f).symm) ≪≫ o.pComp f (𝟙 Y))
      (by simpa only [Iso.trans_assoc] using hp.right_unit f)
    rw [conjugate_transport o.P o.S
      (fun t ↦ o.adj t) ((o.adj (𝟙 Y)).comp (o.adj f))
      (Category.comp_id f) (o.pComp f (𝟙 Y))] at hh
    have hm := congr_app (congrArg Iso.hom hh) M
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.rightUnitor_hom_app] at hm
    conv_rhs at hm => erw [Category.comp_id]
    simpa only [c_eq, sId_eq, jId_eq] using hm

private theorem j_unital (o : Calculus.{u, g, h, v, w} G geo) (hp : PullCoherence o)
    {X Y : G} (j : X ⟶ Y) [IsOpenImmersion (geo.map j)] (M : o.D X) :
    ((o.jComp (𝟙 X) j).hom.app M ≫ (o.jCongr (Category.id_comp j)).hom.app M =
      (o.J j).map ((o.jId X).hom.app M)) ∧
    ((o.jComp j (𝟙 Y)).hom.app M ≫ (o.jCongr (Category.comp_id j)).hom.app M =
      (o.jId Y).hom.app ((o.J j).obj M)) := by
  constructor
  · have he : coherenceD o (𝟙 X) j ≪≫ eqToIso (congrArg o.P (Category.id_comp j)) =
        Functor.isoWhiskerLeft (o.P j) (o.pId X) ≪≫ Functor.rightUnitor (o.P j) := by
      apply Iso.ext
      have hh := congrArg Iso.hom (hp.left_unit j)
      simp only [Iso.trans_hom, Iso.refl_hom] at hh
      have hh' : (eqToIso (congrArg o.P (Category.id_comp j).symm) ≪≫
          o.pComp (𝟙 X) j).hom ≫
          (Functor.isoWhiskerLeft (o.P j) (o.pId X) ≪≫
            Functor.rightUnitor (o.P j)).hom = 𝟙 _ := by
        simpa only [Iso.trans_hom, Category.assoc] using hh
      simpa only [coherenceD, Iso.symm_hom, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
        eqToIso.inv, eqToIso.hom] using
        ((Iso.hom_comp_eq_id _).1 hh').symm
    have hh := Adjunction.leftAdjointCompIso_id_comp
      (o.openAdj (𝟙 X)) (o.openAdj j)
      (coherenceD o (𝟙 X) j ≪≫ eqToIso (congrArg o.P (Category.id_comp j))) (o.pId X) he
    rw [j_comp_transport o (𝟙 X) j j (Category.id_comp j)] at hh
    have hm := congr_app (congrArg Iso.hom hh) M
    simp only [Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app] at hm
    conv_rhs at hm => erw [Category.comp_id]
    simpa only [c_eq, sId_eq, jId_eq] using hm
  · have he : coherenceD o j (𝟙 Y) ≪≫ eqToIso (congrArg o.P (Category.comp_id j)) =
        Functor.isoWhiskerRight (o.pId Y) (o.P j) ≪≫ Functor.leftUnitor (o.P j) := by
      apply Iso.ext
      have hh := congrArg Iso.hom (hp.right_unit j)
      simp only [Iso.trans_hom, Iso.refl_hom] at hh
      have hh' : (eqToIso (congrArg o.P (Category.comp_id j).symm) ≪≫
          o.pComp j (𝟙 Y)).hom ≫
          (Functor.isoWhiskerRight (o.pId Y) (o.P j) ≪≫
            Functor.leftUnitor (o.P j)).hom = 𝟙 _ := by
        simpa only [Iso.trans_hom, Category.assoc] using hh
      simpa only [coherenceD, Iso.symm_hom, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
        eqToIso.inv, eqToIso.hom] using
        ((Iso.hom_comp_eq_id _).1 hh').symm
    have hh := Adjunction.leftAdjointCompIso_comp_id
      (o.openAdj j) (o.openAdj (𝟙 Y))
      (coherenceD o j (𝟙 Y) ≪≫ eqToIso (congrArg o.P (Category.comp_id j))) (o.pId Y) he
    rw [j_comp_transport o j (𝟙 Y) j (Category.comp_id j)] at hh
    have hm := congr_app (congrArg Iso.hom hh) M
    simp only [Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.rightUnitor_hom_app] at hm
    conv_rhs at hm => erw [Category.comp_id]
    simpa only [c_eq, sId_eq, jId_eq] using hm

private theorem alpha_vertical_of_gamma (o : Calculus.{u, g, h, v, w} G geo)
    {A C₀ E B D F : G}
    (k : A ⟶ B) (i : C₀ ⟶ D) (j : E ⟶ F)
    (r₁ : A ⟶ C₀) (r₂ : C₀ ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F)
    [IsOpenImmersion (geo.map k)] [IsOpenImmersion (geo.map i)]
    [IsOpenImmersion (geo.map j)]
    [QuasiCompact (geo.map k)] [QuasiCompact (geo.map i)] [QuasiCompact (geo.map j)]
    [IsProper (geo.map r₁)] [IsProper (geo.map r₂)]
    [IsProper (geo.map p₁)] [IsProper (geo.map p₂)]
    [IsProper (geo.map (r₁ ≫ r₂))] [IsProper (geo.map (p₁ ≫ p₂))]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (hg : ∀ M : o.D A,
    (o.J j).map ((o.sComp r₁ r₂).hom.app M) ≫
        (o.gamma k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
        (o.sComp p₁ p₂).inv.app ((o.J k).obj M) =
      (o.gamma i r₂ p₂ j h₂).app ((o.S r₁).obj M) ≫
        (o.S p₂).map ((o.gamma k r₁ p₁ i h₁).app M)) (M : o.D E) :
    (o.pComp p₁ p₂).inv.app ((o.J j).obj M) ≫
        (o.alpha k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
        (o.J k).map ((o.pComp r₁ r₂).hom.app M) =
      (o.P p₁).map ((o.alpha i r₂ p₂ j h₂).app M) ≫
        (o.alpha k r₁ p₁ i h₁).app ((o.P r₂).obj M) := by
  let a₁ := TwoSquare.mk _ _ _ _ (o.alpha k r₁ p₁ i h₁)
  let a₂ := TwoSquare.mk _ _ _ _ (o.alpha i r₂ p₂ j h₂)
  let a := TwoSquare.mk _ _ _ _ (o.alpha k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
  have hm : mateEquiv ((o.adj r₂).comp (o.adj r₁))
      ((o.adj p₂).comp (o.adj p₁)) (TwoSquare.vComp a₂ a₁) =
    mateEquiv ((o.adj r₂).comp (o.adj r₁)) ((o.adj p₂).comp (o.adj p₁))
      ((a.whiskerLeft (o.pComp r₁ r₂).hom).whiskerRight
        (o.pComp p₁ p₂).inv) := by
    rw [mateEquiv_hcomp]
    rw [mateEquiv_conjugateEquiv_vcomp _ (o.adj (p₁ ≫ p₂))]
    rw [conjugateEquiv_mateEquiv_vcomp _ (o.adj (r₁ ≫ r₂))]
    apply TwoSquare.ext
    intro M
    have hγ := (hg M).symm
    dsimp only [a₁, a₂, a, Calculus.gamma, Calculus.sComp,
      TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.mk] at hγ ⊢
    simpa only [conjugateIsoEquiv_apply_hom,
    conjugateIsoEquiv_apply_inv, TwoSquare.hComp, TwoSquare.whiskerTop,
    TwoSquare.whiskerBottom, TwoSquare.mk, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc] using hγ
  have ha := (mateEquiv ((o.adj r₂).comp (o.adj r₁))
    ((o.adj p₂).comp (o.adj p₁))).injective hm
  have hn := congrArg (fun t ↦ t.app M) ha
  dsimp only [a₁, a₂, a, TwoSquare.vComp, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.mk] at hn
  simpa only [TwoSquare.vComp, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.mk, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc] using hn.symm

private theorem alpha_horizontal_of_gamma (o : Calculus.{u, g, h, v, w} G geo)
    {A B E C₀ D F : G}
    (k : A ⟶ B) (l : B ⟶ E) (i : C₀ ⟶ D) (j : D ⟶ F)
    (r : A ⟶ C₀) (p : B ⟶ D) (q : E ⟶ F)
    [IsOpenImmersion (geo.map k)] [IsOpenImmersion (geo.map l)]
    [IsOpenImmersion (geo.map i)] [IsOpenImmersion (geo.map j)]
    [QuasiCompact (geo.map k)] [QuasiCompact (geo.map l)]
    [QuasiCompact (geo.map i)] [QuasiCompact (geo.map j)]
    [IsProper (geo.map r)] [IsProper (geo.map p)] [IsProper (geo.map q)]
    [IsOpenImmersion (geo.map (k ≫ l))] [IsOpenImmersion (geo.map (i ≫ j))]
    [QuasiCompact (geo.map (k ≫ l))] [QuasiCompact (geo.map (i ≫ j))]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (hg : ∀ M : o.D A,
    (o.jComp i j).hom.app ((o.S r).obj M) ≫
        (o.gamma (k ≫ l) r q (i ≫ j) h).app M ≫
        (o.S q).map ((o.jComp k l).inv.app M) =
      (o.J j).map ((o.gamma k r p i h₁).app M) ≫
        (o.gamma l p q j h₂).app ((o.J k).obj M)) (M : o.D C₀) :
    (o.P q).map ((o.jComp i j).hom.app M) ≫
        (o.alpha (k ≫ l) r q (i ≫ j) h).app M ≫
        (o.jComp k l).inv.app ((o.P r).obj M) =
      (o.alpha l p q j h₂).app ((o.J i).obj M) ≫
        (o.J l).map ((o.alpha k r p i h₁).app M) := by
  let a₁ := TwoSquare.mk _ _ _ _ (o.alpha k r p i h₁)
  let a₂ := TwoSquare.mk _ _ _ _ (o.alpha l p q j h₂)
  let a := TwoSquare.mk _ _ _ _ (o.alpha (k ≫ l) r q (i ≫ j) h)
  have hm : mateEquiv (o.adj r) (o.adj q) (TwoSquare.hComp a₁ a₂) =
      mateEquiv (o.adj r) (o.adj q)
        ((a.whiskerTop (o.jComp i j).hom).whiskerBottom (o.jComp k l).inv) := by
    rw [mateEquiv_vcomp (o.adj r) (o.adj p) (o.adj q)]
    rw [mateEquiv_whiskerTop_whiskerBottom]
    apply TwoSquare.ext
    intro M
    have hγ := (hg M).symm
    dsimp only [a₁, a₂, a, Calculus.gamma, TwoSquare.vComp, TwoSquare.mk,
      TwoSquare.whiskerLeft, TwoSquare.whiskerRight] at hγ ⊢
    simpa only [TwoSquare.vComp, TwoSquare.mk,
      TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id, Category.assoc] using hγ
  have ha := (mateEquiv (o.adj r) (o.adj q)).injective hm
  have hn := congrArg (fun t ↦ t.app M) ha
  dsimp only [a₁, a₂, a, TwoSquare.hComp, TwoSquare.whiskerTop,
    TwoSquare.whiskerBottom, TwoSquare.mk] at hn
  simpa only [TwoSquare.hComp, TwoSquare.whiskerTop,
    TwoSquare.whiskerBottom, TwoSquare.mk, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc] using hn.symm

attribute [local irreducible] HasDerivedCategory.standard

attribute [local irreducible] SemilinearProperOpen.R
  SemilinearProperOpen.J SemilinearProperOpen.adj SemilinearProperOpen.jAdj
  SemilinearProperOpen.alpha SemilinearProperOpen.pComp SemilinearProperOpen.pId

private theorem ambient_system_pComp_eq (C : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    WeilConjectures.AmbientCompositor.pComp
      (WeilConjectures.AmbientCompositor.systems C τ) f g =
      SemilinearProperOpen.pComp C τ f g := by
  rw [WeilConjectures.AmbientCompositor.pComp_eq]
  unfold SemilinearProperOpen.pComp
  rfl

private theorem ambient_system_pId_eq (C : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n) (X : Scheme.{u}) :
    (WeilConjectures.AmbientCompositor.systems C τ).pId X =
      SemilinearProperOpen.pId C τ X := by
  unfold SemilinearProperOpen.pId
  rfl

private theorem native_system_pull_coherence (C : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n) :
    WeilConjectures.AmbientCompositor.PullCoherence
      (WeilConjectures.AmbientCompositor.systems C τ) :=
  WeilConjectures.AmbientCompositor.descend_pull_coherence _
    (WeilConjectures.AmbientCompositor.system_ordinary_pull_coherence C τ)

private theorem ambient_system_P_eq (C : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (WeilConjectures.AmbientCompositor.systems C τ).P f =
      SemilinearProperOpen.P C τ f := rfl

attribute [local irreducible] SemilinearProperOpen.P

private theorem systems_pull_coherence_of_native (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    (hh : WeilConjectures.AmbientCompositor.PullCoherence
      (WeilConjectures.AmbientCompositor.systems C τ)) :
    PullCoherence (systems F C τ) := by
  constructor
  · intro X Y f
    have hu := hh.left_unit f.hom.left
    simp only [ambient_system_pComp_eq, ambient_system_pId_eq,
      ambient_system_P_eq] at hu
    exact hu
  · intro X Y f
    have hu := hh.right_unit f.hom.left
    simp only [ambient_system_pComp_eq, ambient_system_pId_eq,
      ambient_system_P_eq] at hu
    exact hu

private theorem systems_pull_coherence (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    PullCoherence (systems F C τ) :=
  systems_pull_coherence_of_native F C τ (native_system_pull_coherence C τ)

private theorem systems_sComp_eq (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y Z : Spaces F} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (systems F C τ).sComp f g = SemilinearProperOpen.sComp C τ f.hom.left g.hom.left := rfl

private theorem systems_sId_eq (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) (X : Spaces F) :
    (systems F C τ).sId X = SemilinearProperOpen.sId C τ X.obj.left := rfl

private theorem systems_jComp_eq (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y Z : Spaces F} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : IsOpenImmersion ((geometry F).map f)]
    [hg : IsOpenImmersion ((geometry F).map g)]
    [IsOpenImmersion ((geometry F).map (f ≫ g))] :
    (systems F C τ).jComp f g = @SemilinearProperOpen.jComp C τ
      X.obj.left Y.obj.left Z.obj.left f.hom.left g.hom.left hf hg := rfl

private theorem systems_jId_eq (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) (X : Spaces F) :
    (systems F C τ).jId X = SemilinearProperOpen.jId C τ X.obj.left := by
  rw [jId_eq]
  rfl

-- The equality specification retains the constructed arrow without reducing its app field.
-- Both the witness and its uniqueness are proved; specifiedArrow_eq recovers that arrow.
private theorem specifiedArrow_unique {A : Type v} (a : A) : ∃! b : A, b = a :=
  ⟨a, rfl, fun _ h ↦ h⟩

private def specifiedArrow {A : Type v} (a : A) : A :=
  (specifiedArrow_unique a).choose

private theorem specifiedArrow_eq {A : Type v} (a : A) : specifiedArrow a = a :=
  (specifiedArrow_unique a).choose_spec.1

private theorem systems_gamma_eq (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {U V W Z : Spaces F} (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [hk : IsOpenImmersion ((geometry F).map k)]
    [hi : IsOpenImmersion ((geometry F).map i)]
    [hqk : QuasiCompact ((geometry F).map k)]
    [hqi : QuasiCompact ((geometry F).map i)]
    [hpr : IsProper ((geometry F).map r)] [hpp : IsProper ((geometry F).map p)]
    (h : k ≫ p = r ≫ i) :
    (systems F C τ).gamma k r p i h = specifiedArrow (@SemilinearProperOpen.gamma C τ
      U.obj.left V.obj.left W.obj.left Z.obj.left k.hom.left r.hom.left p.hom.left
      i.hom.left hk hi hqk hqi hpr hpp (congrArg (fun f ↦ f.hom.left) h)) := by
  rw [specifiedArrow_eq]
  rfl

attribute [local irreducible] Calculus.sComp SemilinearProperOpen.sComp
  Calculus.jComp SemilinearProperOpen.jComp Calculus.sId SemilinearProperOpen.sId
  Calculus.jId SemilinearProperOpen.jId Calculus.gamma SemilinearProperOpen.gamma

private theorem systems_p_assoc (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    ∀ {X Y Z T : Spaces F} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (M : (systems F C τ).D T),
    ((systems F C τ).pComp (f ≫ g) h).hom.app M ≫ ((systems F C τ).pComp f g).hom.app (((systems F
      C τ).P h).obj M) =
      ((systems F C τ).pCongr (Category.assoc f g h)).hom.app M ≫ ((systems F C τ).pComp f (g ≫
      h)).hom.app M ≫
        ((systems F C τ).P f).map (((systems F C τ).pComp g h).hom.app M) := by
  intro X Y Z T f g h M
  exact (SemilinearProperOpen.compositor_associativity C τ).1
    f.hom.left g.hom.left h.hom.left M

private theorem systems_p_unit (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    ∀ {X Y : Spaces F} (f : X ⟶ Y) (M : (systems F C τ).D Y),
    (((systems F C τ).pComp (𝟙 X) f).hom.app M ≫ ((systems F C τ).pId X).hom.app (((systems F C
      τ).P f).obj M) =
      ((systems F C τ).pCongr (Category.id_comp f)).hom.app M) ∧
    (((systems F C τ).pComp f (𝟙 Y)).hom.app M ≫ ((systems F C τ).P f).map (((systems F C τ).pId
      Y).hom.app M) =
      ((systems F C τ).pCongr (Category.comp_id f)).hom.app M) := by
  have hp := systems_pull_coherence F C τ
  intro X Y f M
  exact p_unital (systems F C τ) hp f M

private theorem systems_s_assoc (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    ∀ {X Y Z T : Spaces F} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) (M : (systems F C τ).D X),
    ((systems F C τ).S h).map (((systems F C τ).sComp f g).hom.app M) ≫ ((systems F C τ).sComp (f ≫
      g) h).hom.app M =
      ((systems F C τ).sComp g h).hom.app (((systems F C τ).S f).obj M) ≫ ((systems F C τ).sComp f
      (g ≫ h)).hom.app M ≫
        ((systems F C τ).sCongr (Category.assoc f g h)).inv.app M := by
  intro X Y Z T f g h M
  simp only [systems_sComp_eq]
  exact (SemilinearProperOpen.compositor_associativity C τ).2.1
    f.hom.left g.hom.left h.hom.left M

private theorem systems_s_unit (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    ∀ {X Y : Spaces F} (f : X ⟶ Y) (M : (systems F C τ).D X),
    (((systems F C τ).sComp (𝟙 X) f).hom.app M ≫ ((systems F C τ).sCongr (Category.id_comp
      f)).hom.app M =
      ((systems F C τ).S f).map (((systems F C τ).sId X).hom.app M)) ∧
    (((systems F C τ).sComp f (𝟙 Y)).hom.app M ≫ ((systems F C τ).sCongr (Category.comp_id
      f)).hom.app M =
      ((systems F C τ).sId Y).hom.app (((systems F C τ).S f).obj M)) := by
  have hp := systems_pull_coherence F C τ
  intro X Y f M
  exact s_unital (systems F C τ) hp f M

private theorem systems_jCongr_eq (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n)
    {X Y : Spaces F} {f g : X ⟶ Y}
    [hf : IsOpenImmersion ((geometry F).map f)]
    [hg : IsOpenImmersion ((geometry F).map g)] (e : f = g) :
    (systems F C τ).jCongr e =
      @SemilinearProperOpen.jCongr C τ X.obj.left Y.obj.left f.hom.left g.hom.left
        hf hg (congrArg (fun k ↦ k.hom.left) e) := by
  cases e
  rfl

attribute [local irreducible] Calculus.jCongr SemilinearProperOpen.jCongr

private theorem systems_j_assoc (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    ∀ {X Y Z T : Spaces F} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsOpenImmersion ((geometry F).map f)] [IsOpenImmersion ((geometry F).map g)]
    [IsOpenImmersion ((geometry F).map h)] (M : (systems F C τ).D X),
    ((systems F C τ).J h).map (((systems F C τ).jComp f g).hom.app M) ≫ ((systems F C τ).jComp (f ≫
      g) h).hom.app M =
      ((systems F C τ).jComp g h).hom.app (((systems F C τ).J f).obj M) ≫ ((systems F C τ).jComp f
      (g ≫ h)).hom.app M ≫
        ((systems F C τ).jCongr (Category.assoc f g h)).inv.app M := by
  intro X Y Z T f g h hf hg hh M
  have : IsOpenImmersion f.hom.left := hf
  have : IsOpenImmersion g.hom.left := hg
  have : IsOpenImmersion h.hom.left := hh
  simp only [systems_jComp_eq, systems_jCongr_eq]
  exact (SemilinearProperOpen.compositor_associativity C τ).2.2
    f.hom.left g.hom.left h.hom.left M

private theorem systems_j_unit (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    ∀ {X Y : Spaces F} (j : X ⟶ Y) [IsOpenImmersion ((geometry F).map j)] (M : (systems F C τ).D X),
    (((systems F C τ).jComp (𝟙 X) j).hom.app M ≫ ((systems F C τ).jCongr (Category.id_comp
      j)).hom.app M =
      ((systems F C τ).J j).map (((systems F C τ).jId X).hom.app M)) ∧
    (((systems F C τ).jComp j (𝟙 Y)).hom.app M ≫ ((systems F C τ).jCongr (Category.comp_id
      j)).hom.app M =
      ((systems F C τ).jId Y).hom.app (((systems F C τ).J j).obj M)) := by
  have hp := systems_pull_coherence F C τ
  intro X Y j hj M
  exact j_unital (systems F C τ) hp j M

section
open SemilinearProperOpen

private theorem native_gamma_vertical (C : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n) :
    (∀ {A C₀ E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (i : C₀ ⟶ D) (j : E ⟶ F)
      (r₁ : A ⟶ C₀) (r₂ : C₀ ⟶ E) (p₁ : B₀ ⟶ D) (p₂ : D ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact i] [QuasiCompact j]
      [IsProper r₁] [IsProper r₂] [IsProper p₁] [IsProper p₂]
      (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
      (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : Derived C τ A),
      (J C τ j).map ((sComp C τ r₁ r₂).hom.app M) ≫
          (specifiedArrow (gamma C τ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)).app M ≫
          (sComp C τ p₁ p₂).inv.app ((J C τ k).obj M) =
        (specifiedArrow (gamma C τ i r₂ p₂ j h₂)).app ((R C τ r₁).obj M) ≫
          (R C τ p₂).map ((specifiedArrow (gamma C τ k r₁ p₁ i h₁)).app M)) := by
  intro A C₀ E B₀ D F k i j r₁ r₂ p₁ p₂ hk hi hj hqk hqi hqj hr₁ hr₂ hp₁ hp₂
    h₁ h₂ h M
  simpa only [specifiedArrow_eq] using
    (semilinearProperOpenMatePasting C τ).1 k i j r₁ r₂ p₁ p₂ h₁ h₂ h M

private theorem native_gamma_horizontal (C : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n) :
    (∀ {A C₀ E B₀ D F : Scheme.{u}}
      (k : A ⟶ B₀) (l : B₀ ⟶ E) (i : C₀ ⟶ D) (j : D ⟶ F)
      (r : A ⟶ C₀) (p : B₀ ⟶ D) (q : E ⟶ F)
      [IsOpenImmersion k] [IsOpenImmersion l] [IsOpenImmersion i] [IsOpenImmersion j]
      [QuasiCompact k] [QuasiCompact l] [QuasiCompact i] [QuasiCompact j]
      [IsProper r] [IsProper p] [IsProper q]
      (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
      (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : Derived C τ A),
      (jComp C τ i j).hom.app ((R C τ r).obj M) ≫
          (specifiedArrow (gamma C τ (k ≫ l) r q (i ≫ j) h)).app M ≫
          (R C τ q).map ((jComp C τ k l).inv.app M) =
        (J C τ j).map ((specifiedArrow (gamma C τ k r p i h₁)).app M) ≫
          (specifiedArrow (gamma C τ l p q j h₂)).app ((J C τ k).obj M)) := by
  intro A C₀ E B₀ D F k l i j r p q hk hl hi hj hqk hql hqi hqj hr hp hq h₁ h₂ h M
  simpa only [specifiedArrow_eq] using
    (semilinearProperOpenMatePasting C τ).2.1 k l i j r p q h₁ h₂ h M

private theorem native_gamma_vertical_id (C : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n) :
    (∀ {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
      (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : Derived C τ U),
      (specifiedArrow (gamma C τ j (𝟙 U) (𝟙 X) j h)).app M ≫
          (sId C τ X).hom.app ((J C τ j).obj M) =
        (J C τ j).map ((sId C τ U).hom.app M)) := by
  intro U X j hj hqj h M
  simpa only [specifiedArrow_eq] using (gamma_identities C τ).1 j h M

private theorem native_gamma_horizontal_id (C : ℕ → CommRingCat.{u + 1})
    (τ : ∀ n, C (n + 1) ⟶ C n) :
    (∀ {U X : Scheme.{u}} (p : U ⟶ X) [IsProper p]
      (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : Derived C τ U),
      (specifiedArrow (gamma C τ (𝟙 U) p p (𝟙 X) h)).app M ≫
          (R C τ p).map ((jId C τ U).hom.app M) =
        (jId C τ X).hom.app ((R C τ p).obj M)) := by
  intro U X p hp h M
  simpa only [specifiedArrow_eq] using (gamma_identities C τ).2 p h M

end

private theorem systems_gamma_vertical (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    ∀ {A C₀ E B D F₀ : Spaces F}
    (k : A ⟶ B) (i : C₀ ⟶ D) (j : E ⟶ F₀)
    (r₁ : A ⟶ C₀) (r₂ : C₀ ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F₀)
    [IsOpenImmersion ((geometry F).map k)] [IsOpenImmersion ((geometry F).map i)]
    [IsOpenImmersion ((geometry F).map j)]
    [QuasiCompact ((geometry F).map k)] [QuasiCompact ((geometry F).map i)]
    [QuasiCompact ((geometry F).map j)]
    [IsProper ((geometry F).map r₁)] [IsProper ((geometry F).map r₂)]
    [IsProper ((geometry F).map p₁)] [IsProper ((geometry F).map p₂)]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : (systems F C τ).D A),
    ((systems F C τ).J j).map (((systems F C τ).sComp r₁ r₂).hom.app M) ≫
        ((systems F C τ).gamma k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
        ((systems F C τ).sComp p₁ p₂).inv.app (((systems F C τ).J k).obj M) =
      ((systems F C τ).gamma i r₂ p₂ j h₂).app (((systems F C τ).S r₁).obj M) ≫
        ((systems F C τ).S p₂).map (((systems F C τ).gamma k r₁ p₁ i h₁).app M) := by
  intro A C₀ E B D F₀ k i j r₁ r₂ p₁ p₂ hk hi hj hqk hqi hqj hr₁ hr₂ hp₁ hp₂ h₁ h₂ h M
  have : IsOpenImmersion k.hom.left := hk
  have : IsOpenImmersion i.hom.left := hi
  have : IsOpenImmersion j.hom.left := hj
  have : QuasiCompact k.hom.left := hqk
  have : QuasiCompact i.hom.left := hqi
  have : QuasiCompact j.hom.left := hqj
  have : IsProper r₁.hom.left := hr₁
  have : IsProper r₂.hom.left := hr₂
  have : IsProper p₁.hom.left := hp₁
  have : IsProper p₂.hom.left := hp₂
  refine three_two_congr ?_ ?_ ?_ ?_ ?_ (native_gamma_vertical C τ
    k.hom.left i.hom.left j.hom.left r₁.hom.left r₂.hom.left p₁.hom.left p₂.hom.left
    (congrArg (fun f ↦ f.hom.left) h₁) (congrArg (fun f ↦ f.hom.left) h₂)
    (congrArg (fun f ↦ f.hom.left) h) M)
  · exact
      congrArg ((systems F C τ).J j).map
        (congr_app (congrArg Iso.hom (systems_sComp_eq F C τ r₁ r₂)) M)
  · exact
      congr_app (systems_gamma_eq F C τ k (r₁ ≫ r₂) (p₁ ≫ p₂) j h) M
  · exact
      congr_app (congrArg Iso.inv (systems_sComp_eq F C τ p₁ p₂))
        (((systems F C τ).J k).obj M)
  · exact
      congr_app (systems_gamma_eq F C τ i r₂ p₂ j h₂) (((systems F C τ).S r₁).obj M)
  · exact
      congrArg ((systems F C τ).S p₂).map
        (congr_app (systems_gamma_eq F C τ k r₁ p₁ i h₁) M)

private theorem systems_gamma_horizontal (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    ∀ {A B E C₀ D F₀ : Spaces F}
    (k : A ⟶ B) (l : B ⟶ E) (i : C₀ ⟶ D) (j : D ⟶ F₀)
    (r : A ⟶ C₀) (p : B ⟶ D) (q : E ⟶ F₀)
    [IsOpenImmersion ((geometry F).map k)] [IsOpenImmersion ((geometry F).map l)]
    [IsOpenImmersion ((geometry F).map i)] [IsOpenImmersion ((geometry F).map j)]
    [QuasiCompact ((geometry F).map k)] [QuasiCompact ((geometry F).map l)]
    [QuasiCompact ((geometry F).map i)] [QuasiCompact ((geometry F).map j)]
    [IsProper ((geometry F).map r)] [IsProper ((geometry F).map p)] [IsProper ((geometry F).map q)]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : (systems F C τ).D A),
    ((systems F C τ).jComp i j).hom.app (((systems F C τ).S r).obj M) ≫
        ((systems F C τ).gamma (k ≫ l) r q (i ≫ j) h).app M ≫
        ((systems F C τ).S q).map (((systems F C τ).jComp k l).inv.app M) =
      ((systems F C τ).J j).map (((systems F C τ).gamma k r p i h₁).app M) ≫
        ((systems F C τ).gamma l p q j h₂).app (((systems F C τ).J k).obj M) := by
  intro A B E C₀ D F₀ k l i j r p q hk hl hi hj hqk hql hqi hqj hr hp hq h₁ h₂ h M
  have : IsOpenImmersion k.hom.left := hk
  have : IsOpenImmersion l.hom.left := hl
  have : IsOpenImmersion i.hom.left := hi
  have : IsOpenImmersion j.hom.left := hj
  have : QuasiCompact k.hom.left := hqk
  have : QuasiCompact l.hom.left := hql
  have : QuasiCompact i.hom.left := hqi
  have : QuasiCompact j.hom.left := hqj
  have : IsProper r.hom.left := hr
  have : IsProper p.hom.left := hp
  have : IsProper q.hom.left := hq
  refine three_two_congr ?_ ?_ ?_ ?_ ?_ (native_gamma_horizontal C τ
    k.hom.left l.hom.left i.hom.left j.hom.left r.hom.left p.hom.left q.hom.left
    (congrArg (fun f ↦ f.hom.left) h₁) (congrArg (fun f ↦ f.hom.left) h₂)
    (congrArg (fun f ↦ f.hom.left) h) M)
  · exact
      congr_app (congrArg Iso.hom (systems_jComp_eq F C τ i j))
        (((systems F C τ).S r).obj M)
  · exact
      congr_app (systems_gamma_eq F C τ (k ≫ l) r q (i ≫ j) h) M
  · exact
      congrArg ((systems F C τ).S q).map
        (congr_app (congrArg Iso.inv (systems_jComp_eq F C τ k l)) M)
  · exact
      congrArg ((systems F C τ).J j).map
        (congr_app (systems_gamma_eq F C τ k r p i h₁) M)
  · exact
      congr_app (systems_gamma_eq F C τ l p q j h₂) (((systems F C τ).J k).obj M)

private theorem systems_gamma_vertical_id (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    ∀ {U X : Spaces F} (j : U ⟶ X)
    [IsOpenImmersion ((geometry F).map j)] [QuasiCompact ((geometry F).map j)]
    (h : j ≫ (𝟙 X) = (𝟙 U) ≫ j) (M : (systems F C τ).D U),
    ((systems F C τ).gamma j (𝟙 U) (𝟙 X) j h).app M ≫ ((systems F C τ).sId X).hom.app (((systems F
      C τ).J j).obj M) =
      ((systems F C τ).J j).map (((systems F C τ).sId U).hom.app M) := by
  intro U X j hj hq h M
  have : IsOpenImmersion j.hom.left := hj
  have : QuasiCompact j.hom.left := hq
  refine two_one_congr ?_ ?_ ?_ (native_gamma_vertical_id C τ j.hom.left
    (congrArg (fun f ↦ f.hom.left) h) M)
  · exact
      congr_app (systems_gamma_eq F C τ j (𝟙 U) (𝟙 X) j h) M
  · exact
      congr_app (congrArg Iso.hom (systems_sId_eq F C τ X)) (((systems F C τ).J j).obj M)
  · exact
      congrArg ((systems F C τ).J j).map
        (congr_app (congrArg Iso.hom (systems_sId_eq F C τ U)) M)

private theorem systems_gamma_horizontal_id (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    ∀ {U X : Spaces F} (p : U ⟶ X) [IsProper ((geometry F).map p)]
    (h : (𝟙 U) ≫ p = p ≫ (𝟙 X)) (M : (systems F C τ).D U),
    ((systems F C τ).gamma (𝟙 U) p p (𝟙 X) h).app M ≫ ((systems F C τ).S p).map (((systems F C
      τ).jId U).hom.app M) =
      ((systems F C τ).jId X).hom.app (((systems F C τ).S p).obj M)
 := by
  intro U X p hp h M
  have : IsProper p.hom.left := hp
  refine two_one_congr ?_ ?_ ?_ (native_gamma_horizontal_id C τ p.hom.left
    (congrArg (fun f ↦ f.hom.left) h) M)
  · exact
      congr_app (systems_gamma_eq F C τ (𝟙 U) p p (𝟙 X) h) M
  · exact
      congrArg ((systems F C τ).S p).map
        (congr_app (congrArg Iso.hom (systems_jId_eq F C τ U)) M)
  · exact
      congr_app (congrArg Iso.hom (systems_jId_eq F C τ X)) (((systems F C τ).S p).obj M)

private theorem systems_alpha_vertical (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    ∀ {A C₀ E B D F₀ : Spaces F}
    (k : A ⟶ B) (i : C₀ ⟶ D) (j : E ⟶ F₀)
    (r₁ : A ⟶ C₀) (r₂ : C₀ ⟶ E) (p₁ : B ⟶ D) (p₂ : D ⟶ F₀)
    [IsOpenImmersion ((geometry F).map k)] [IsOpenImmersion ((geometry F).map i)]
    [IsOpenImmersion ((geometry F).map j)]
    [QuasiCompact ((geometry F).map k)] [QuasiCompact ((geometry F).map i)]
    [QuasiCompact ((geometry F).map j)]
    [IsProper ((geometry F).map r₁)] [IsProper ((geometry F).map r₂)]
    [IsProper ((geometry F).map p₁)] [IsProper ((geometry F).map p₂)]
    (h₁ : k ≫ p₁ = r₁ ≫ i) (h₂ : i ≫ p₂ = r₂ ≫ j)
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (M : (systems F C τ).D E),
    ((systems F C τ).pComp p₁ p₂).inv.app (((systems F C τ).J j).obj M) ≫
        ((systems F C τ).alpha k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
        ((systems F C τ).J k).map (((systems F C τ).pComp r₁ r₂).hom.app M) =
      ((systems F C τ).P p₁).map (((systems F C τ).alpha i r₂ p₂ j h₂).app M) ≫
        ((systems F C τ).alpha k r₁ p₁ i h₁).app (((systems F C τ).P r₂).obj M) := by
  intro A C₀ E B D F₀ k i j r₁ r₂ p₁ p₂ hk hi hj hqk hqi hqj hr₁ hr₂ hp₁ hp₂ h₁ h₂ h M
  exact alpha_vertical_of_gamma (systems F C τ) k i j r₁ r₂ p₁ p₂ h₁ h₂ h
    (systems_gamma_vertical F C τ k i j r₁ r₂ p₁ p₂ h₁ h₂ h) M

private theorem systems_alpha_horizontal (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    ∀ {A B E C₀ D F₀ : Spaces F}
    (k : A ⟶ B) (l : B ⟶ E) (i : C₀ ⟶ D) (j : D ⟶ F₀)
    (r : A ⟶ C₀) (p : B ⟶ D) (q : E ⟶ F₀)
    [IsOpenImmersion ((geometry F).map k)] [IsOpenImmersion ((geometry F).map l)]
    [IsOpenImmersion ((geometry F).map i)] [IsOpenImmersion ((geometry F).map j)]
    [QuasiCompact ((geometry F).map k)] [QuasiCompact ((geometry F).map l)]
    [QuasiCompact ((geometry F).map i)] [QuasiCompact ((geometry F).map j)]
    [IsProper ((geometry F).map r)] [IsProper ((geometry F).map p)] [IsProper ((geometry F).map q)]
    (h₁ : k ≫ p = r ≫ i) (h₂ : l ≫ q = p ≫ j)
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (M : (systems F C τ).D C₀),
    ((systems F C τ).P q).map (((systems F C τ).jComp i j).hom.app M) ≫
        ((systems F C τ).alpha (k ≫ l) r q (i ≫ j) h).app M ≫
        ((systems F C τ).jComp k l).inv.app (((systems F C τ).P r).obj M) =
      ((systems F C τ).alpha l p q j h₂).app (((systems F C τ).J i).obj M) ≫
        ((systems F C τ).J l).map (((systems F C τ).alpha k r p i h₁).app M) := by
  intro A B E C₀ D F₀ k l i j r p q hk hl hi hj hqk hql hqi hqj hr hp hq h₁ h₂ h M
  exact alpha_horizontal_of_gamma (systems F C τ) k l i j r p q h₁ h₂ h
    (systems_gamma_horizontal F C τ k l i j r p q h₁ h₂ h) M

private theorem systems_laws (F : WeilConjectures.FiniteFieldDatum.{u})
    (C : ℕ → CommRingCat.{u + 1}) (τ : ∀ n, C (n + 1) ⟶ C n) :
    Laws (systems F C τ) where
  p_assoc := systems_p_assoc F C τ
  p_unit := systems_p_unit F C τ
  s_assoc := systems_s_assoc F C τ
  s_unit := systems_s_unit F C τ
  j_assoc := systems_j_assoc F C τ
  j_unit := systems_j_unit F C τ
  alpha_vertical := systems_alpha_vertical F C τ
  alpha_horizontal := systems_alpha_horizontal F C τ
  gamma_vertical := systems_gamma_vertical F C τ
  gamma_horizontal := systems_gamma_horizontal F C τ
  gamma_vertical_id := systems_gamma_vertical_id F C τ
  gamma_horizontal_id := systems_gamma_horizontal_id F C τ

private theorem ordinary_tensor (F : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] :
    OrdinaryTensorComposition F Λ := by
  intro X Y Z f g M N
  let : NatTrans.IsMonoidal (upperStarComp (ModuleCat.{u + 1} Λ)
      f.hom.left g.hom.left).inv := RingSheaf.isMonoidal_upperStarComp_inv _ _
  have hh := leftDerivedUpperStarTensorComparison_comp (ModuleCat.{u + 1} Λ)
    f.hom.left g.hom.left M N
  simpa only [ordinary, ProperOpenTensor, ProperOpenPull,
    ObjectProperty.FullSubcategory.comp_hom, Over.comp_left] using hh

/-- The canonical ambient proper/open calculus obeys all composition and identity
laws, in both coefficient settings, together with canonical tensor/composition coherence.
The finite coefficient level is n+1. The statements apply to the full unbounded categories.
Source: Stacks 0F7B--0F7D, 03CB, 03EL, 07A4 and 07A7; Zheng 4.1 and 4.10
(blueprint: lem-sf-ambient-proper-open-pasting).

Proof: The ordinary geometric laws are ordinaryAmbientProperOpenLaws. The generic
left-derived tensor composition law, applied to the monoidal ordinary pullback
compositor, gives OrdinaryTensorComposition. For systems, use the existing semilinear
compositor associativity and mate-pasting theorems. Adjunction conjugation transports
pullback unit coherence to direct image and open extension. Injectivity of the mate
equivalence recovers intrinsic alpha pasting from the two gamma pasting equations;
the canonical identity comparisons give the remaining units. Finally,
publishedSystemTensorComposition identifies the published representative-normalized
system tensor comparisons and compositors, giving its tensor equation before evaluation. -/
theorem ambientProperOpenPasting (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (_hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    (Laws (ordinary F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ∧
    OrdinaryTensorComposition F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))) ∧
    Laws (systems F (WeilConjectures.IntegralSystemRealization.scalarRings l E)
      (WeilConjectures.IntegralSystemRealization.scalarTransitions l E)) ∧
    ∀ (o : WeilConjectures.IntegralSystemRealization.Operations l E)
      (c : WeilConjectures.IntegralSystemRealization.Compositors l E o),
      SystemTensorComposition F l E o c := by
  refine ⟨ordinaryAmbientProperOpenLaws F l _hl E n, ?_, ?_, ?_⟩
  · exact ordinary_tensor F
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))
  · exact systems_laws F
      (WeilConjectures.IntegralSystemRealization.scalarRings l E)
      (WeilConjectures.IntegralSystemRealization.scalarTransitions l E)
  · exact publishedSystemTensorComposition F l _hl E

end AlgebraicGeometry.ProEtale.AmbientProperOpen
