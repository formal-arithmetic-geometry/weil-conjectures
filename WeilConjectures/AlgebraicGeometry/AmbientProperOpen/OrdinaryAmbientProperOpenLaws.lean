/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.AmbientProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.OrdinaryAmbientAlphaPasting
import WeilConjectures.AlgebraicGeometry.AmbientProperOpen.OrdinaryAmbientAlphaUnits
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import all WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerDirectImageCoherence
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperStarCompCoherence
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-! # OrdinaryAmbientProperOpenLaws
Source: Stacks 0F7B--0F7D, 03EL, 07A4 and 07A7. -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u g h v w
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.ProEtale.AmbientProperOpen

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
  upperStar lowerStar Functor.rightDerivedFunctor
  Functor.leftAdjoint constantSheaf

variable {G : Type g} [Category.{h} G] {geo : G ⥤ Scheme.{u}}

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
  assoc : ∀ {X Y Z T : G} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T),
    o.pComp f (g ≫ h) ≪≫ Functor.isoWhiskerRight (o.pComp g h) (o.P f) =
      eqToIso (congrArg o.P (Category.assoc f g h).symm) ≪≫
        o.pComp (f ≫ g) h ≪≫ Functor.isoWhiskerLeft (o.P h) (o.pComp f g)
  left_unit : ∀ {X Y : G} (f : X ⟶ Y),
    eqToIso (congrArg o.P (Category.id_comp f).symm) ≪≫ o.pComp (𝟙 X) f ≪≫
      Functor.isoWhiskerLeft (o.P f) (o.pId X) ≪≫ Functor.rightUnitor (o.P f) = Iso.refl _
  right_unit : ∀ {X Y : G} (f : X ⟶ Y),
    eqToIso (congrArg o.P (Category.comp_id f).symm) ≪≫ o.pComp f (𝟙 Y) ≪≫
      Functor.isoWhiskerRight (o.pId Y) (o.P f) ≪≫ Functor.leftUnitor (o.P f) = Iso.refl _

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

private theorem s_associative (o : Calculus.{u, g, h, v, w} G geo) (hp : PullCoherence o)
    {X Y Z T : G}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (M : o.D X) :
    (o.S h).map ((o.sComp f g).hom.app M) ≫ (o.sComp (f ≫ g) h).hom.app M =
      (o.sComp g h).hom.app ((o.S f).obj M) ≫ (o.sComp f (g ≫ h)).hom.app M ≫
        (eqToIso (congrArg o.S (Category.assoc f g h))).inv.app M := by
  have hp := congrArg Iso.hom (hp.assoc f g h)
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom] at hp
  have hh := ProEtale.StrictTower.conjugate_triangle_assoc
    (o.adj h) (o.adj g) (o.adj f)
    (o.adj (g ≫ h)) (o.adj (f ≫ g)) (o.adj (f ≫ g ≫ h))
    (o.pComp g h) (o.pComp f g)
    (eqToIso (congrArg (o.P) (Category.assoc f g h).symm) ≪≫
      o.pComp (f ≫ g) h) (o.pComp f (g ≫ h))
    (by simpa only [Iso.trans_hom, Category.assoc] using hp.symm)
  have ht := congrArg Iso.hom (conjugate_transport (o.P) (o.S)
    (fun f ↦ o.adj f) ((o.adj h).comp (o.adj (f ≫ g)))
    (Category.assoc f g h) (o.pComp (f ≫ g) h))
  simp only [Iso.trans_hom, conjugateIsoEquiv_apply_hom] at ht
  simp only [Iso.trans_hom] at hh
  rw [ht] at hh
  have hm := congr_app hh M
  apply (cancel_mono
    ((eqToIso (congrArg (o.S) (Category.assoc f g h))).hom.app M)).1
  simpa only [c_eq, conjugateIsoEquiv_apply_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.assoc,
    Iso.inv_hom_id_app, Category.comp_id] using hm.symm

private theorem j_associative (o : Calculus.{u, g, h, v, w} G geo) (hp : PullCoherence o)
    {X Y Z T : G}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    [IsOpenImmersion (geo.map f)] [IsOpenImmersion (geo.map g)]
    [IsOpenImmersion (geo.map h)] (M : o.D X) :
    (o.J h).map ((o.jComp f g).hom.app M) ≫ (o.jComp (f ≫ g) h).hom.app M =
      (o.jComp g h).hom.app ((o.J f).obj M) ≫ (o.jComp f (g ≫ h)).hom.app M ≫
        (o.jCongr (Category.assoc f g h)).inv.app M := by
  have hi : Functor.isoWhiskerLeft (o.P h) (o.pComp f g).symm ≪≫
      ((o.pComp (f ≫ g) h).symm ≪≫
        eqToIso (congrArg (o.P) (Category.assoc f g h))) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (o.pComp g h).symm (o.P f) ≪≫
        (o.pComp f (g ≫ h)).symm := by
    have hp := congrArg Iso.symm (hp.assoc f g h)
    apply Iso.ext
    apply NatTrans.ext
    funext N
    simpa only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_inv_app, Category.id_comp, Category.assoc,
      Iso.symm_hom, eqToIso.inv, eqToIso.hom] using
        (congr_app (congrArg Iso.hom hp) N).symm
  have hh := Adjunction.leftAdjointCompIso_assoc
    (o.openAdj f) (o.openAdj g) (o.openAdj h)
    (o.openAdj (f ≫ g)) (o.openAdj (g ≫ h)) (o.openAdj (f ≫ g ≫ h))
    (o.pComp f g).symm (o.pComp g h).symm
    (o.pComp f (g ≫ h)).symm
    ((o.pComp (f ≫ g) h).symm ≪≫
      eqToIso (congrArg (o.P) (Category.assoc f g h))) hi
  rw [j_comp_transport o (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h)] at hh
  have hm := congr_app (congrArg Iso.hom hh) M
  apply (cancel_mono ((o.jCongr (Category.assoc f g h)).hom.app M)).1
  simpa only [Calculus.jComp, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc, Iso.inv_hom_id_app, Category.comp_id] using hm.symm

private theorem gamma_vertical_of_alpha (o : Calculus.{u, g, h, v, w} G geo)
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
    (h : k ≫ (p₁ ≫ p₂) = (r₁ ≫ r₂) ≫ j) (ha : ∀ M : o.D E,
    (o.pComp p₁ p₂).inv.app ((o.J j).obj M) ≫
        (o.alpha k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
        (o.J k).map ((o.pComp r₁ r₂).hom.app M) =
      (o.P p₁).map ((o.alpha i r₂ p₂ j h₂).app M) ≫
        (o.alpha k r₁ p₁ i h₁).app ((o.P r₂).obj M)) (M :  o.D A) :
    (o.J j).map ((o.sComp r₁ r₂).hom.app M) ≫
        (o.gamma k (r₁ ≫ r₂) (p₁ ≫ p₂) j h).app M ≫
        (o.sComp p₁ p₂).inv.app ((o.J k).obj M) =
      (o.gamma i r₂ p₂ j h₂).app ((o.S r₁).obj M) ≫
        (o.S p₂).map ((o.gamma k r₁ p₁ i h₁).app M) := by
  let a₁ := TwoSquare.mk _ _ _ _ (o.alpha k r₁ p₁ i h₁)
  let a₂ := TwoSquare.mk _ _ _ _ (o.alpha i r₂ p₂ j h₂)
  let a := TwoSquare.mk _ _ _ _ (o.alpha k (r₁ ≫ r₂) (p₁ ≫ p₂) j h)
  have he : TwoSquare.vComp a₂ a₁ =
      (a.whiskerLeft (o.pComp r₁ r₂).hom).whiskerRight (o.pComp p₁ p₂).inv := by
    apply TwoSquare.ext
    intro N
    dsimp only [a₁, a₂, a, TwoSquare.vComp, TwoSquare.whiskerLeft,
      TwoSquare.whiskerRight, TwoSquare.mk]
    simpa only [TwoSquare.vComp, TwoSquare.whiskerLeft,
      TwoSquare.whiskerRight, TwoSquare.mk, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id, Category.assoc] using (ha N).symm
  have hm := congrArg (mateEquiv ((o.adj r₂).comp (o.adj r₁))
    ((o.adj p₂).comp (o.adj p₁))) he
  rw [mateEquiv_hcomp] at hm
  rw [mateEquiv_conjugateEquiv_vcomp _ (o.adj (p₁ ≫ p₂))] at hm
  rw [conjugateEquiv_mateEquiv_vcomp _ (o.adj (r₁ ≫ r₂))] at hm
  have hn := congrArg (fun t ↦ t.app M) hm
  dsimp only [a₁, a₂, a, TwoSquare.mk] at hn
  simpa only [Calculus.gamma, Calculus.sComp,
    conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_apply_inv,
    TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    TwoSquare.mk, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc] using hn.symm

private theorem gamma_horizontal_of_alpha (o : Calculus.{u, g, h, v, w} G geo)
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
    (h : (k ≫ l) ≫ q = r ≫ (i ≫ j)) (ha : ∀ M : o.D C₀,
    (o.P q).map ((o.jComp i j).hom.app M) ≫
        (o.alpha (k ≫ l) r q (i ≫ j) h).app M ≫
        (o.jComp k l).inv.app ((o.P r).obj M) =
      (o.alpha l p q j h₂).app ((o.J i).obj M) ≫
        (o.J l).map ((o.alpha k r p i h₁).app M)) (M :  o.D A) :
    (o.jComp i j).hom.app ((o.S r).obj M) ≫
        (o.gamma (k ≫ l) r q (i ≫ j) h).app M ≫
        (o.S q).map ((o.jComp k l).inv.app M) =
      (o.J j).map ((o.gamma k r p i h₁).app M) ≫
        (o.gamma l p q j h₂).app ((o.J k).obj M) := by
  let a₁ := TwoSquare.mk _ _ _ _ (o.alpha k r p i h₁)
  let a₂ := TwoSquare.mk _ _ _ _ (o.alpha l p q j h₂)
  let a := TwoSquare.mk _ _ _ _ (o.alpha (k ≫ l) r q (i ≫ j) h)
  have he : TwoSquare.hComp a₁ a₂ =
      (a.whiskerTop (o.jComp i j).hom).whiskerBottom (o.jComp k l).inv := by
    apply TwoSquare.ext
    intro N
    dsimp only [a₁, a₂, a, TwoSquare.hComp, TwoSquare.whiskerTop,
      TwoSquare.whiskerBottom, TwoSquare.mk]
    simpa only [TwoSquare.hComp, TwoSquare.whiskerTop,
      TwoSquare.whiskerBottom, TwoSquare.mk, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.id_comp, Category.comp_id, Category.assoc] using (ha N).symm
  have hm := congrArg (mateEquiv (o.adj r) (o.adj q)) he
  rw [mateEquiv_vcomp (o.adj r) (o.adj p) (o.adj q)] at hm
  rw [mateEquiv_whiskerTop_whiskerBottom] at hm
  have hn := congrArg (fun t ↦ t.app M) hm
  dsimp only [a₁, a₂, a, TwoSquare.mk] at hn
  simpa only [Calculus.gamma, TwoSquare.vComp, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.mk, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.id_comp, Category.comp_id, Category.assoc] using hn.symm

private theorem ordinary_pCongr (F : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Spaces F} {f g : X ⟶ Y} (h : f = g) :
    (ordinary F Λ).pCongr h =
      leftDerivedUpperStarCongr (ModuleCat.{u + 1} Λ)
        (congrArg (fun a ↦ a.hom.left) h) := by
  cases h
  rfl

private theorem ordinary_p_assoc (F : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y Z T : Spaces F} (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (M : (ordinary F Λ).D T) :
    ((ordinary F Λ).pComp (f ≫ g) h).hom.app M ≫
        ((ordinary F Λ).pComp f g).hom.app (((ordinary F Λ).P h).obj M) =
      ((ordinary F Λ).pCongr (Category.assoc f g h)).hom.app M ≫
        ((ordinary F Λ).pComp f (g ≫ h)).hom.app M ≫
        ((ordinary F Λ).P f).map (((ordinary F Λ).pComp g h).hom.app M) := by
  rw [ordinary_pCongr]
  exact leftDerivedUpperStarComp_assoc_app f.hom.left g.hom.left h.hom.left M

private theorem ordinary_p_unit (F : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Spaces F} (f : X ⟶ Y) (M : (ordinary F Λ).D Y) :
    (((ordinary F Λ).pComp (𝟙 X) f).hom.app M ≫
        ((ordinary F Λ).pId X).hom.app (((ordinary F Λ).P f).obj M) =
      ((ordinary F Λ).pCongr (Category.id_comp f)).hom.app M) ∧
    (((ordinary F Λ).pComp f (𝟙 Y)).hom.app M ≫
        ((ordinary F Λ).P f).map (((ordinary F Λ).pId Y).hom.app M) =
      ((ordinary F Λ).pCongr (Category.comp_id f)).hom.app M) := by
  rw [ordinary_pCongr]
  exact ⟨leftDerivedUpperStarComp_id_left_app f.hom.left M,
    leftDerivedUpperStarComp_id_right_app f.hom.left M⟩

private theorem ordinary_pull_coherence (F : WeilConjectures.FiniteFieldDatum.{u})
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] : PullCoherence (ordinary F Λ) := by
  constructor
  · intro X Y Z T f g h
    apply Iso.ext
    apply NatTrans.ext
    funext M
    apply (cancel_epi (((ordinary F Λ).pCongr (Category.assoc f g h)).hom.app M)).mp
    change ((ordinary F Λ).pCongr (Category.assoc f g h)).hom.app M ≫
      (((ordinary F Λ).pComp f (g ≫ h)).hom.app M ≫
        ((ordinary F Λ).P f).map (((ordinary F Λ).pComp g h).hom.app M)) =
      ((ordinary F Λ).pCongr (Category.assoc f g h)).hom.app M ≫
        ((ordinary F Λ).pCongr (Category.assoc f g h)).inv.app M ≫
        (((ordinary F Λ).pComp (f ≫ g) h).hom.app M ≫
          ((ordinary F Λ).pComp f g).hom.app (((ordinary F Λ).P h).obj M))
    rw [Iso.hom_inv_id_app_assoc]
    exact (ordinary_p_assoc F Λ f g h M).symm
  · intro X Y f
    apply Iso.ext
    apply NatTrans.ext
    funext M
    change ((ordinary F Λ).pCongr (Category.id_comp f)).inv.app M ≫
      (((ordinary F Λ).pComp (𝟙 X) f).hom.app M ≫
        ((ordinary F Λ).pId X).hom.app (((ordinary F Λ).P f).obj M) ≫ 𝟙 _) = 𝟙 _
    simp only [Category.comp_id]
    rw [(ordinary_p_unit F Λ f M).1]
    exact Iso.inv_hom_id_app _ _
  · intro X Y f
    apply Iso.ext
    apply NatTrans.ext
    funext M
    change ((ordinary F Λ).pCongr (Category.comp_id f)).inv.app M ≫
      (((ordinary F Λ).pComp f (𝟙 Y)).hom.app M ≫
        ((ordinary F Λ).P f).map (((ordinary F Λ).pId Y).hom.app M) ≫ 𝟙 _) = 𝟙 _
    simp only [Category.comp_id]
    rw [(ordinary_p_unit F Λ f M).2]
    exact Iso.inv_hom_id_app _ _

attribute [local irreducible] ordinary

/-- Ordinary geometric proper/open pasting with its normalized compositors.
Source: Stacks 0F7B--0F7D, 03EL, 07A4 and 07A7
(blueprint: lem-sf-ordinary-ambient-proper-open-laws).
Proof: Use the underived intrinsic clopen-pasting theorem at coefficient level n. The
exact clopen comparison identifies its localization with properOpenAlpha through the
canonical total-derived/exact-derived pullback comparison. Exact localization preserves
vertical and horizontal square composition. The adjunction unit normalization identifies
localized open compositors with Calculus.jComp. Pullback composition coherence gives
associativity and units; conjugation gives these laws for pushforward and open extension.
The empty open and zero object obey these same equations because every clopen
projection is the identity on its image and zero on the complementary open.
Take adjunction mates of both alpha pasting equations. In each identity square alpha is
invertible because the underived identity word is invertible; pasting it with itself and
cancelling gives its unit equation. Taking mates gives both gamma identity equations. -/
theorem ordinaryAmbientProperOpenLaws (F : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ F.p)
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (n : ℕ) :
    Laws (ordinary F (ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)))) := by
  let Λ := ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1))
  let c := ordinary F Λ
  have hp : PullCoherence c := ordinary_pull_coherence F Λ
  have ha := ordinaryAmbientAlphaPasting F l hl E n
  have hu := ordinaryAmbientAlphaUnits F l hl E n
  refine
    { p_assoc := ordinary_p_assoc F Λ
      p_unit := ordinary_p_unit F Λ
      s_assoc := s_associative c hp
      s_unit := s_unital c hp
      j_assoc := j_associative c hp
      j_unit := j_unital c hp
      alpha_vertical := ha.1
      alpha_horizontal := ha.2
      gamma_vertical := ?_
      gamma_horizontal := ?_
      gamma_vertical_id := ?_
      gamma_horizontal_id := ?_ }
  · intro A C₀ E B D F k i j r₁ r₂ p₁ p₂ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
    exact gamma_vertical_of_alpha c k i j r₁ r₂ p₁ p₂ h₁ h₂ h
      (ha.1 k i j r₁ r₂ p₁ p₂ h₁ h₂ h) M
  · intro A B E C₀ D F k ll i j r p q _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h M
    exact gamma_horizontal_of_alpha c k ll i j r p q h₁ h₂ h
      (ha.2 k ll i j r p q h₁ h₂ h) M
  · intro U X j _ _ h M
    exact StrictTower.mate_identity_vertical (c.adj (𝟙 U)) (c.adj (𝟙 X))
      (c.pId U) (c.pId X) (c.J j) (c.alpha j (𝟙 U) (𝟙 X) j h)
      (hu.1 j h) M
  · intro U X p _ h M
    exact StrictTower.mate_identity_horizontal (c.adj p) (c.J (𝟙 X)) (c.J (𝟙 U))
      (c.jId X) (c.jId U) (c.alpha (𝟙 U) p p (𝟙 X) h) (hu.2 p h) M

end AlgebraicGeometry.ProEtale.AmbientProperOpen
