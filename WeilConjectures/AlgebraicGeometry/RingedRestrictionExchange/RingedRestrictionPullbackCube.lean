/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.OpenCube.RingedRestrictionOpenCube
public import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.RingedExchangeChainUnit
import Mathlib.CategoryTheory.Category.Cat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy

/-! # The ordinary inverse-image cube for restriction

Source: Stacks Project, sites.tex Tag 03CB and proetale.tex Tag 09A5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.RingedRestrictionExchange

private structure RingedVertex where
  scheme : Scheme.{u}
  ring : Sheaf (ProEt.topology scheme) CommRingCat.{u + 1}

private structure RingedMap (S X : RingedVertex.{u}) where
  hom : S.scheme ⟶ X.scheme
  coefficient : (proEtaleSheafInverseImage hom CommRingCat.{u + 1}).obj X.ring ≅ S.ring

private def RingedMap.comp {S X T : RingedVertex.{u}}
    (a : RingedMap S X) (b : RingedMap T S) : RingedMap T X where
  hom := b.hom ≫ a.hom
  coefficient := proEtaleRingCompositeCoefficients b.hom a.hom X.ring S.ring T.ring
    a.coefficient b.coefficient

private abbrev RingedMap.pull {S X : RingedVertex.{u}} (a : RingedMap S X) :=
  proEtaleRingModulePullback a.hom X.ring S.ring a.coefficient

private abbrev RingedMap.push {S X : RingedVertex.{u}} (a : RingedMap S X) :=
  proEtaleRingModuleDirectImage a.hom X.ring S.ring a.coefficient

private def RingedMap.pullComp {S X T : RingedVertex.{u}}
    (a : RingedMap S X) (b : RingedMap T S) :
    (a.comp b).pull ≅ a.pull ⋙ b.pull :=
  exchangeModuleComposition b.hom a.hom X.ring S.ring T.ring a.coefficient b.coefficient

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

private theorem immersion_eq {S X : RingedVertex.{u}}
    {a b : RingedMap S X} (h : a.hom = b.hom)
    (hc : (eqToIso (congrArg
      (fun f ↦ proEtaleSheafInverseImage f CommRingCat.{u + 1}) h)).app X.ring ≪≫
        b.coefficient = a.coefficient) : a = b := by
  rcases a with ⟨f, c⟩
  rcases b with ⟨g, d⟩
  dsimp only at h
  cases h
  have hc' : d = c := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Iso.app_hom, eqToIso.hom, eqToHom_refl,
      NatTrans.id_app, Category.id_comp] using congrArg Iso.hom hc
  cases hc'
  rfl

private theorem immersion_assoc {S X T W : RingedVertex.{u}}
    (a : RingedMap S X) (b : RingedMap T S)
    (d : RingedMap W T) :
    (a.comp b).comp d = a.comp (b.comp d) := by
  apply immersion_eq (Category.assoc d.hom b.hom a.hom).symm
  apply Iso.ext
  have h := congrArg (fun e ↦ e.hom.app X.ring) (ring_pull_assoc d.hom b.hom a.hom)
  dsimp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app] at h
  simp only [Category.comp_id] at h
  dsimp only [RingedMap.comp, proEtaleRingCompositeCoefficients,
    Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [(proEtaleRingInverseImageComp d.hom b.hom).hom.naturality_assoc a.coefficient.hom]
  dsimp only [Functor.comp_map]
  rw [← reassoc_of% h]

attribute [local irreducible] proEtaleRingModulePullback proEtaleRingModuleAdjunction
  proEtaleRingDirectImageMap proEtaleRingCompositeCoefficients proEtaleRingInverseImageComp
  StrictTowerRingedSquare.exchangeModuleSquare

private noncomputable abbrev moduleAdj {S X : RingedVertex.{u}}
    (a : RingedMap S X) :=
  proEtaleRingModuleAdjunction a.hom X.ring S.ring a.coefficient

@[irreducible] private noncomputable def pushComp {S X T : RingedVertex.{u}}
    (a : RingedMap S X) (b : RingedMap T S) :
    b.push ⋙ a.push ≅ (a.comp b).push :=
  conjugateIsoEquiv ((moduleAdj a).comp (moduleAdj b)) (moduleAdj (a.comp b)) (a.pullComp b)

-- The module compositor is fixed by its sectionwise right-adjoint normalization.
private theorem pushComp_forget {S X T : RingedVertex.{u}}
    (a : RingedMap S X) (b : RingedMap T S)
    (N : proEtaleRingModules T.scheme T.ring) :
    (SheafOfModules.toSheaf _).map ((pushComp a b).hom.app N) =
      (AlgebraicGeometry.ProEtale.lowerStarComp AddCommGrpCat.{u + 1} b.hom a.hom).hom.app
        ((SheafOfModules.toSheaf _).obj N) := by
  unfold pushComp RingedMap.pullComp exchangeModuleComposition
  ext U m
  exact (exchangeModuleComposition_existsUnique b.hom a.hom X.ring S.ring T.ring
    a.coefficient b.coefficient).choose_spec.1 N U.unop m

private theorem push_congr_forget {S X : RingedVertex.{u}}
    {a b : RingedMap S X} (h : a = b)
    (N : proEtaleRingModules S.scheme S.ring) :
    (SheafOfModules.toSheaf _).map
        ((eqToIso (congrArg RingedMap.push h)).hom.app N) =
      (AlgebraicGeometry.ProEtale.lowerStarCongr AddCommGrpCat.{u + 1}
        (congrArg RingedMap.hom h)).hom.app
          ((SheafOfModules.toSheaf _).obj N) := by
  cases h
  ext U m
  rfl

attribute [local irreducible] RingedMap.pullComp
  exchangeModuleComposition

-- Expand compositor coherence before specializing to the concrete module functors.
private theorem compositor_assoc_iff
    {A B C D E : Type*} [Category A] [Category B] [Category C] [Category D] [Category E]
    {Ra : C ⥤ D} {Rb : B ⥤ C} {Rd : A ⥤ B}
    {Rab : B ⥤ D} {Rbd : A ⥤ C} {Rl Rr : A ⥤ D}
    (F : D ⥤ E) [F.Faithful]
    (cab : Rb ⋙ Ra ≅ Rab) (cbd : Rd ⋙ Rb ≅ Rbd)
    (cl : Rd ⋙ Rab ≅ Rl) (cr : Rbd ⋙ Ra ≅ Rr) (e : Rr ≅ Rl) :
    Functor.associator Rd Rb Ra ≪≫ Functor.isoWhiskerLeft Rd cab ≪≫ cl =
        Functor.isoWhiskerRight cbd Ra ≪≫ cr ≪≫ e ↔
      ∀ N, F.map (cab.hom.app (Rd.obj N)) ≫ F.map (cl.hom.app N) =
        F.map (Ra.map (cbd.hom.app N)) ≫ F.map (cr.hom.app N) ≫ F.map (e.hom.app N) := by
  constructor
  · intro h N
    have hh := congrArg (fun z ↦ F.map (z.hom.app N)) h
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Category.id_comp, Functor.map_comp] using hh
  · intro h
    apply Iso.ext
    apply NatTrans.ext
    funext N
    apply F.map_injective
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, Category.id_comp, Functor.map_comp] using h N

set_option profiler true in
private theorem push_assoc {S X T W : RingedVertex.{u}}
    (a : RingedMap S X) (b : RingedMap T S)
    (d : RingedMap W T)
    (h : (a.comp b).comp d = a.comp (b.comp d)) :
    Functor.associator d.push b.push a.push ≪≫
        Functor.isoWhiskerLeft d.push (pushComp a b) ≪≫ pushComp (a.comp b) d =
      Functor.isoWhiskerRight (pushComp b d) a.push ≪≫ pushComp a (b.comp d) ≪≫
        (eqToIso (congrArg RingedMap.push h)).symm := by
  apply (compositor_assoc_iff (SheafOfModules.toSheaf _) (pushComp a b) (pushComp b d)
    (pushComp (a.comp b) d) (pushComp a (b.comp d))
    (eqToIso (congrArg RingedMap.push h)).symm).2
  intro N
  have hc := push_congr_forget h.symm N
  have ha := pushComp_forget (a.comp b) d N
  have hb := pushComp_forget a (b.comp d) N
  have hab := pushComp_forget a b (d.push.obj N)
  have hbd := pushComp_forget b d N
  have H := (compositor_assoc_iff (𝟭 _)
    (AlgebraicGeometry.ProEtale.lowerStarComp AddCommGrpCat.{u + 1} b.hom a.hom)
    (AlgebraicGeometry.ProEtale.lowerStarComp AddCommGrpCat.{u + 1} d.hom b.hom)
    (AlgebraicGeometry.ProEtale.lowerStarComp AddCommGrpCat.{u + 1} d.hom (b.hom ≫ a.hom))
    (AlgebraicGeometry.ProEtale.lowerStarComp AddCommGrpCat.{u + 1} (d.hom ≫ b.hom) a.hom)
    (AlgebraicGeometry.ProEtale.lowerStarCongr AddCommGrpCat.{u + 1}
      (Category.assoc d.hom b.hom a.hom))).1
    (AlgebraicGeometry.ProEtale.legacy_lowerStarComp_assoc
      AddCommGrpCat.{u + 1} d.hom b.hom a.hom) ((SheafOfModules.toSheaf _).obj N)
  have hm : (SheafOfModules.toSheaf _).map (a.push.map ((pushComp b d).hom.app N)) =
      (AlgebraicGeometry.ProEtale.lowerStar AddCommGrpCat.{u + 1} a.hom).map
        ((SheafOfModules.toSheaf _).map ((pushComp b d).hom.app N)) := rfl
  exact (congrArg₂ (· ≫ ·) hab ha).trans (H.trans
    (congrArg₂ (· ≫ ·)
      (hm.trans (congrArg
        (AlgebraicGeometry.ProEtale.lowerStar AddCommGrpCat.{u + 1} a.hom).map hbd))
      (congrArg₂ (· ≫ ·) hb hc)).symm)

attribute [local irreducible] proEtaleRingModuleDirectImage

private theorem pull_congr {S X : RingedVertex.{u}}
    {a b : RingedMap S X} (h : a = b) :
    conjugateIsoEquiv (moduleAdj b) (moduleAdj a)
      (eqToIso (congrArg RingedMap.pull h)) =
      (eqToIso (congrArg RingedMap.push h)).symm := by
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

-- The concrete conjugation involves large module functor and adjunction types.
private theorem pull_assoc {S X T W : RingedVertex.{u}}
    (a : RingedMap S X) (b : RingedMap T S)
    (d : RingedMap W T)
    (h : (a.comp b).comp d = a.comp (b.comp d)) :
    (a.comp b).pullComp d ≪≫ Functor.isoWhiskerRight (a.pullComp b) d.pull ≪≫
        Functor.associator _ _ _ =
      eqToIso (congrArg RingedMap.pull h) ≪≫
        a.pullComp (b.comp d) ≪≫ Functor.isoWhiskerLeft a.pull (b.pullComp d) := by
  apply adjoint_compositor_associativity (moduleAdj a) (moduleAdj b) (moduleAdj d)
    (moduleAdj (a.comp b)) (moduleAdj (b.comp d))
    (moduleAdj ((a.comp b).comp d)) (moduleAdj (a.comp (b.comp d)))
    (a.pullComp b) (b.pullComp d) ((a.comp b).pullComp d) (a.pullComp (b.comp d))
    (eqToIso (congrArg RingedMap.pull h))
  erw [pull_congr h]
  simpa only [pushComp] using push_assoc a b d h

private abbrev rcomp {A B C : RingedVertex.{u}} (a : RingedMap A B) (b : RingedMap B C) :=
  b.comp a

local infixr:80 " ≫ᵣ " => rcomp

private theorem rcomp_assoc {A B C D : RingedVertex.{u}}
    (a : RingedMap A B) (b : RingedMap B C) (c : RingedMap C D) :
    (a ≫ᵣ b) ≫ᵣ c = a ≫ᵣ b ≫ᵣ c := (immersion_assoc c b a).symm

private theorem inverse_associativity
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {La : D ⥤ C} {Lb : C ⥤ B} {Ld : B ⥤ A}
    {Lab : D ⥤ B} {Lbd : C ⥤ A} {Ll Lr : D ⥤ A}
    (cab : Lab ≅ La ⋙ Lb) (cbd : Lbd ≅ Lb ⋙ Ld)
    (cl : Ll ≅ Lab ⋙ Ld) (cr : Lr ≅ La ⋙ Lbd) (e : Ll ≅ Lr)
    (h : cl ≪≫ Functor.isoWhiskerRight cab Ld ≪≫ Functor.associator La Lb Ld =
      e ≪≫ cr ≪≫ Functor.isoWhiskerLeft La cbd) (M : D) :
    cbd.inv.app (La.obj M) ≫ cr.inv.app M ≫ e.inv.app M =
      Ld.map (cab.inv.app M) ≫ cl.inv.app M := by
  have hh := congrArg (fun z ↦ z.inv.app M) h
  simpa only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc] using hh.symm

private theorem transported_associativity
    {CA CB CC CD : Type*} [Category CA] [Category CB] [Category CC] [Category CD]
    {P Q R PQ QR T : Type*}
    (compPQ : P → Q → PQ) (compQR : Q → R → QR)
    (compL : PQ → R → T) (compR : P → QR → T)
    (F₁ : P → (CB ⥤ CA)) (F₂ : Q → (CC ⥤ CB)) (F₃ : R → (CD ⥤ CC))
    (FPQ : PQ → (CC ⥤ CA)) (FQR : QR → (CD ⥤ CB)) (FT : T → (CD ⥤ CA))
    (kPQ : ∀ p q, FPQ (compPQ p q) ≅ F₂ q ⋙ F₁ p)
    (kQR : ∀ q r, FQR (compQR q r) ≅ F₃ r ⋙ F₂ q)
    (kL : ∀ pq r, FT (compL pq r) ≅ F₃ r ⋙ FPQ pq)
    (kR : ∀ p qr, FT (compR p qr) ≅ FQR qr ⋙ F₁ p)
    (ha : ∀ p q r, compR p (compQR q r) = compL (compPQ p q) r)
    (h : ∀ p q r,
      kR p (compQR q r) ≪≫ Functor.isoWhiskerRight (kQR q r) (F₁ p) ≪≫
          Functor.associator (F₃ r) (F₂ q) (F₁ p) =
        eqToIso (congrArg FT (ha p q r)) ≪≫ kL (compPQ p q) r ≪≫
          Functor.isoWhiskerLeft (F₃ r) (kPQ p q))
    (p : P) (q : Q) (r : R) (pq : PQ) (qr : QR) (t : T)
    (hpq : compPQ p q = pq) (hqr : compQR q r = qr)
    (ht : compL pq r = t) (ht' : compR p qr = t) (M : CD) :
    ((kPQ p q).symm ≪≫ eqToIso (congrArg FPQ hpq)).hom.app ((F₃ r).obj M) ≫
        ((kL pq r).symm ≪≫ eqToIso (congrArg FT ht)).hom.app M =
      (F₁ p).map (((kQR q r).symm ≪≫ eqToIso (congrArg FQR hqr)).hom.app M) ≫
        ((kR p qr).symm ≪≫ eqToIso (congrArg FT ht')).hom.app M := by
  subst pq qr
  cases ht'
  simpa only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, eqToIso.hom,
    eqToIso.inv, eqToHom_refl, NatTrans.id_app, Category.comp_id, Category.assoc]
    using inverse_associativity (kQR q r) (kPQ p q)
      (kR p (compQR q r)) (kL (compPQ p q) r)
      (eqToIso (congrArg FT (ha p q r))) (h p q r) M

private def abstractCubeComposition
    (D : RingedVertex.{u} → Type*) [∀ A, Category (D A)]
    (F : ∀ {A B : RingedVertex.{u}}, RingedMap A B → (D B ⥤ D A))
    (K : ∀ {A B C : RingedVertex.{u}} (a : RingedMap A B) (b : RingedMap B C),
      F (a ≫ᵣ b) ≅ F b ⋙ F a)
    {A B C : RingedVertex.{u}}
    (a : RingedMap A B) (b : RingedMap B C) (t : RingedMap A C) (h : a ≫ᵣ b = t) :
    (F b) ⋙ (F a) ≅ (F t) :=
  (K a b).symm ≪≫ eqToIso (congrArg F h)

private theorem abstractCubeComposition_refl
    (D : RingedVertex.{u} → Type*) [∀ A, Category (D A)]
    (F : ∀ {A B : RingedVertex.{u}}, RingedMap A B → (D B ⥤ D A))
    (K : ∀ {A B C : RingedVertex.{u}} (a : RingedMap A B) (b : RingedMap B C),
      F (a ≫ᵣ b) ≅ F b ⋙ F a)
    {A B C : RingedVertex.{u}}
    (a : RingedMap A B) (b : RingedMap B C) :
    abstractCubeComposition D F K a b (a ≫ᵣ b) rfl = (K a b).symm :=
  Iso.trans_refl _

private theorem abstractCubeComposition_assoc
    (D : RingedVertex.{u} → Type*) [∀ A, Category (D A)]
    (F : ∀ {A B : RingedVertex.{u}}, RingedMap A B → (D B ⥤ D A))
    (K : ∀ {A B C : RingedVertex.{u}} (a : RingedMap A B) (b : RingedMap B C),
      F (a ≫ᵣ b) ≅ F b ⋙ F a)
    (H : ∀ {A B C D' : RingedVertex.{u}}
      (a : RingedMap A B) (b : RingedMap B C) (c : RingedMap C D'),
      K a (b ≫ᵣ c) ≪≫ Functor.isoWhiskerRight (K b c) (F a) ≪≫
          Functor.associator (F c) (F b) (F a) =
        eqToIso (congrArg F (immersion_assoc c b a)) ≪≫ K (a ≫ᵣ b) c ≪≫
          Functor.isoWhiskerLeft (F c) (K a b))
    {A B C D' : RingedVertex.{u}} (a : RingedMap A B) (b : RingedMap B C)
    (c : RingedMap C D') (ab : RingedMap A C) (bc : RingedMap B D') (t : RingedMap A D')
    (hab : a ≫ᵣ b = ab) (hbc : b ≫ᵣ c = bc)
    (ht : ab ≫ᵣ c = t) (ht' : a ≫ᵣ bc = t)
    (M : D D') :
    (abstractCubeComposition D F K a b ab hab).hom.app ((F c).obj M) ≫
      (abstractCubeComposition D F K ab c t ht).hom.app M =
    (F a).map ((abstractCubeComposition D F K b c bc hbc).hom.app M) ≫
      (abstractCubeComposition D F K a bc t ht').hom.app M :=
  transported_associativity
    (CA := D A) (CB := D B) (CC := D C) (CD := D D')
    (P := RingedMap A B) (Q := RingedMap B C) (R := RingedMap C D')
    (PQ := RingedMap A C) (QR := RingedMap B D') (T := RingedMap A D')
    (@rcomp A B C) (@rcomp B C D') (@rcomp A C D') (@rcomp A B D')
    (@F A B) (@F B C) (@F C D') (@F A C) (@F B D') (@F A D')
    (@K A B C) (@K B C D') (@K A C D') (@K A B D')
    (fun a b c ↦ immersion_assoc c b a) (@H A B C D')
    a b c ab bc t hab hbc ht ht' M

private def abstractCubeSquare
    (D : RingedVertex.{u} → Type*) [∀ A, Category (D A)]
    (F : ∀ {A B : RingedVertex.{u}}, RingedMap A B → (D B ⥤ D A))
    (K : ∀ {A B C : RingedVertex.{u}} (a : RingedMap A B) (b : RingedMap B C),
      F (a ≫ᵣ b) ≅ F b ⋙ F a)
    {A B C D' : RingedVertex.{u}}
    (a : RingedMap A B) (b : RingedMap B D') (d : RingedMap A C) (e : RingedMap C D')
    (h : a ≫ᵣ b = d ≫ᵣ e) : (F b) ⋙ (F a) ⟶ (F e) ⋙ (F d) :=
  (abstractCubeComposition D F K a b (d ≫ᵣ e) h).hom ≫
    (abstractCubeComposition D F K d e (d ≫ᵣ e) rfl).inv

private theorem abstractCubeSquare_cube
    (D : RingedVertex.{u} → Type*) [∀ A, Category (D A)]
    (F : ∀ {A B : RingedVertex.{u}}, RingedMap A B → (D B ⥤ D A))
    (K : ∀ {A B C : RingedVertex.{u}} (a : RingedMap A B) (b : RingedMap B C),
      F (a ≫ᵣ b) ≅ F b ⋙ F a)
    (H : ∀ {A B C D' : RingedVertex.{u}}
      (a : RingedMap A B) (b : RingedMap B C) (c : RingedMap C D'),
      K a (b ≫ᵣ c) ≪≫ Functor.isoWhiskerRight (K b c) (F a) ≪≫
          Functor.associator (F c) (F b) (F a) =
        eqToIso (congrArg F (immersion_assoc c b a)) ≪≫ K (a ≫ᵣ b) c ≪≫
          Functor.isoWhiskerLeft (F c) (K a b))
    {X X' S S' U U' V V' : RingedVertex.{u}}
    (f : RingedMap X S) (f' : RingedMap X' S') (g : RingedMap S' S) (g' : RingedMap X' X)
    (h : g' ≫ᵣ f = f' ≫ᵣ g)
    (iU : RingedMap U X) (iU' : RingedMap U' X') (iV : RingedMap V S) (iV' : RingedMap V' S')
    (f₀ : RingedMap U V) (f₀' : RingedMap U' V') (g₀ : RingedMap V' V) (j : RingedMap U' U)
    (hd : f₀ ≫ᵣ iV = iU ≫ᵣ f) (hd' : f₀' ≫ᵣ iV' = iU' ≫ᵣ f')
    (he : g₀ ≫ᵣ iV = iV' ≫ᵣ g) (hj : j ≫ᵣ iU = iU' ≫ᵣ g')
    (h₀ : j ≫ᵣ f₀ = f₀' ≫ᵣ g₀) (M : D S) :
    (abstractCubeSquare D F K f₀' g₀ j f₀ h₀.symm).app ((F iV).obj M) ≫
        (F j).map ((abstractCubeSquare D F K f₀ iV iU f hd).app M) ≫
        (abstractCubeSquare D F K j iU iU' g' hj).app ((F f).obj M) =
      (F f₀').map ((abstractCubeSquare D F K g₀ iV iV' g he).app M) ≫
        (abstractCubeSquare D F K f₀' iV' iU' f' hd').app ((F g).obj M) ≫
        (F iU').map ((abstractCubeSquare D F K f' g g' f h.symm).app M) := by
  classical
  let t := j ≫ᵣ (iU ≫ᵣ f)
  have ht₄ : (iU' ≫ᵣ g') ≫ᵣ f = t := by
    dsimp only [t]
    rw [← hj, rcomp_assoc]
  have ht₅ : (j ≫ᵣ f₀) ≫ᵣ iV = t := by
    dsimp only [t]
    rw [rcomp_assoc, hd]
  have ht₃ : f₀' ≫ᵣ (iV' ≫ᵣ g) = t := by
    dsimp only [t]
    rw [← he, ← rcomp_assoc, ← h₀, rcomp_assoc, hd]
  have ht₂ : (iU' ≫ᵣ f') ≫ᵣ g = t := by
    rw [rcomp_assoc, ← h, ← rcomp_assoc, ht₄]
  have ht₆ : iU' ≫ᵣ (g' ≫ᵣ f) = t := by
    rw [← rcomp_assoc, ht₄]
  have ha := abstractCubeComposition_assoc D F K H j iU f (iU' ≫ᵣ g') (iU ≫ᵣ f) t
    hj rfl ht₄ rfl M
  have hb := abstractCubeComposition_assoc D F K H j f₀ iV (j ≫ᵣ f₀) (iU ≫ᵣ f) t
    rfl hd ht₅ rfl M
  have hc := abstractCubeComposition_assoc D F K H f₀' g₀ iV (j ≫ᵣ f₀) (iV' ≫ᵣ g) t
    h₀.symm he ht₅ ht₃ M
  have hd₁ := abstractCubeComposition_assoc D F K H iU' g' f (iU' ≫ᵣ g') (g' ≫ᵣ f) t
    rfl rfl ht₄ ht₆ M
  have hd₂ := abstractCubeComposition_assoc D F K H iU' f' g (iU' ≫ᵣ f') (g' ≫ᵣ f) t
    rfl h.symm ht₂ ht₆ M
  have hd₃ := abstractCubeComposition_assoc D F K H f₀' iV' g (iU' ≫ᵣ f') (iV' ≫ᵣ g) t
    hd' rfl ht₂ ht₃ M
  apply (cancel_mono
    ((abstractCubeComposition D F K iU' g' (iU' ≫ᵣ g') rfl).hom.app ((F f).obj M) ≫
      (abstractCubeComposition D F K (iU' ≫ᵣ g') f t ht₄).hom.app M)).mp
  simp only [abstractCubeSquare, NatTrans.comp_app, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [ha]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hb]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hc]
  rw [hd₁]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [← hd₂]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [hd₃]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Category.comp_id]

attribute [local irreducible] abstractCubeSquare abstractCubeComposition

private theorem abstractCubeSquare_cube_faces
    (D : RingedVertex.{u} → Type*) [∀ A, Category (D A)]
    (F : ∀ {A B : RingedVertex.{u}}, RingedMap A B → (D B ⥤ D A))
    (K : ∀ {A B C : RingedVertex.{u}} (a : RingedMap A B) (b : RingedMap B C),
      F (a ≫ᵣ b) ≅ F b ⋙ F a)
    (H : ∀ {A B C D' : RingedVertex.{u}}
      (a : RingedMap A B) (b : RingedMap B C) (c : RingedMap C D'),
      K a (b ≫ᵣ c) ≪≫ Functor.isoWhiskerRight (K b c) (F a) ≪≫
          Functor.associator (F c) (F b) (F a) =
        eqToIso (congrArg F (immersion_assoc c b a)) ≪≫ K (a ≫ᵣ b) c ≪≫
          Functor.isoWhiskerLeft (F c) (K a b))
    {X X' S S' U U' V V' : RingedVertex.{u}}
    (f : RingedMap X S) (f' : RingedMap X' S') (g : RingedMap S' S) (g' : RingedMap X' X)
    (h : g' ≫ᵣ f = f' ≫ᵣ g)
    (iU : RingedMap U X) (iU' : RingedMap U' X') (iV : RingedMap V S) (iV' : RingedMap V' S')
    (f₀ : RingedMap U V) (f₀' : RingedMap U' V') (g₀ : RingedMap V' V) (j : RingedMap U' U)
    (hd : f₀ ≫ᵣ iV = iU ≫ᵣ f) (hd' : f₀' ≫ᵣ iV' = iU' ≫ᵣ f')
    (he : g₀ ≫ᵣ iV = iV' ≫ᵣ g) (hj : j ≫ᵣ iU = iU' ≫ᵣ g')
    (h₀ : j ≫ᵣ f₀ = f₀' ≫ᵣ g₀)
    (s1 : (F iV) ⋙ (F g₀) ⟶ (F g) ⋙ (F iV'))
    (s2 : (F iV') ⋙ (F f₀') ⟶ (F f') ⋙ (F iU'))
    (s3 : (F g) ⋙ (F f') ⟶ (F f) ⋙ (F g'))
    (s4 : (F g₀) ⋙ (F f₀') ⟶ (F f₀) ⋙ (F j))
    (s5 : (F iV) ⋙ (F f₀) ⟶ (F f) ⋙ (F iU))
    (s6 : (F iU) ⋙ (F j) ⟶ (F g') ⋙ (F iU'))
    (e1 : abstractCubeSquare D F K g₀ iV iV' g he = s1)
    (e2 : abstractCubeSquare D F K f₀' iV' iU' f' hd' = s2)
    (e3 : abstractCubeSquare D F K f' g g' f h.symm = s3)
    (e4 : abstractCubeSquare D F K f₀' g₀ j f₀ h₀.symm = s4)
    (e5 : abstractCubeSquare D F K f₀ iV iU f hd = s5)
    (e6 : abstractCubeSquare D F K j iU iU' g' hj = s6)
    (M : D S) :
    (F f₀').map (s1.app M) ≫ s2.app ((F g).obj M) ≫ (F iU').map (s3.app M) =
      s4.app ((F iV).obj M) ≫ (F j).map (s5.app M) ≫ s6.app ((F f).obj M) := by
  subst s1 s2 s3 s4 s5 s6
  exact (abstractCubeSquare_cube D F K H f f' g g' h iU iU' iV iV'
    f₀ f₀' g₀ j hd hd' he hj h₀ M).symm

private abbrev moduleCompositor {A B C : RingedVertex.{u}}
    (a : RingedMap A B) (b : RingedMap B C) := b.pullComp a

private def cubeSquare {A B C D : RingedVertex.{u}}
    (a : RingedMap A B) (b : RingedMap B D) (d : RingedMap A C) (e : RingedMap C D)
    (h : a ≫ᵣ b = d ≫ᵣ e) : b.pull ⋙ a.pull ⟶ e.pull ⋙ d.pull :=
  abstractCubeSquare
    (fun A : RingedVertex.{u} ↦ proEtaleRingModules A.scheme A.ring)
    (fun {S X : RingedVertex.{u}} (a : RingedMap S X) ↦
      proEtaleRingModulePullback a.hom X.ring S.ring a.coefficient) (@moduleCompositor) a b d e h

private theorem ringedMap_ext {S X : RingedVertex.{u}} {a b : RingedMap S X}
    (h : a.hom = b.hom) (hc : HEq a.coefficient b.coefficient) : a = b := by
  cases a with
  | mk f c =>
    cases b with
    | mk g d =>
      dsimp only at h hc
      cases h
      cases hc
      rfl

private abbrev vertex (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) : RingedVertex := ⟨X, R⟩

private abbrev ringedMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    RingedMap (vertex X S) (vertex Y R) := ⟨f, c⟩

private theorem square_map_eq
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) :
    ringedMap g' r.RX r.RX' r.cg' ≫ᵣ ringedMap f r.RY r.RX r.cf =
      ringedMap f' r.RY' r.RX' r.cf' ≫ᵣ ringedMap g r.RY r.RY' r.cg :=
  ringedMap_ext sq.w r.coherent

private theorem square_eq
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq)
    (h : ringedMap f' r.RY' r.RX' r.cf' ≫ᵣ ringedMap g r.RY r.RY' r.cg =
      ringedMap g' r.RX r.RX' r.cg' ≫ᵣ ringedMap f r.RY r.RX r.cf) :
    cubeSquare (ringedMap f' r.RY' r.RX' r.cf') (ringedMap g r.RY r.RY' r.cg)
      (ringedMap g' r.RX r.RX' r.cg') (ringedMap f r.RY r.RX r.cf) h =
      r.exchangeModuleSquare.hom := by
  simp only [cubeSquare, abstractCubeSquare, abstractCubeComposition_refl]
  simp only [abstractCubeComposition, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
    StrictTowerRingedSquare.exchangeModuleSquare]
  unfold moduleCompositor RingedMap.pullComp
  rfl

private theorem abstractCubeSquare_cube_morphisms
    (D : RingedVertex.{u} → Type*) [∀ A, Category (D A)]
    (F : ∀ {A B : RingedVertex.{u}}, RingedMap A B → (D B ⥤ D A))
    (K : ∀ {A B C : RingedVertex.{u}} (a : RingedMap A B) (b : RingedMap B C),
      F (a ≫ᵣ b) ≅ F b ⋙ F a)
    (H : ∀ {A B C D' : RingedVertex.{u}}
      (a : RingedMap A B) (b : RingedMap B C) (c : RingedMap C D'),
      K a (b ≫ᵣ c) ≪≫ Functor.isoWhiskerRight (K b c) (F a) ≪≫
          Functor.associator (F c) (F b) (F a) =
        eqToIso (congrArg F (immersion_assoc c b a)) ≪≫ K (a ≫ᵣ b) c ≪≫
          Functor.isoWhiskerLeft (F c) (K a b))
    {X X' S S' U U' V V' : RingedVertex.{u}}
    (f : RingedMap X S) (f' : RingedMap X' S') (g : RingedMap S' S) (g' : RingedMap X' X)
    (h : g' ≫ᵣ f = f' ≫ᵣ g)
    (iU : RingedMap U X) (iU' : RingedMap U' X') (iV : RingedMap V S) (iV' : RingedMap V' S')
    (f₀ : RingedMap U V) (f₀' : RingedMap U' V') (g₀ : RingedMap V' V) (j : RingedMap U' U)
    (hd : f₀ ≫ᵣ iV = iU ≫ᵣ f) (hd' : f₀' ≫ᵣ iV' = iU' ≫ᵣ f')
    (he : g₀ ≫ᵣ iV = iV' ≫ᵣ g) (hj : j ≫ᵣ iU = iU' ≫ᵣ g')
    (h₀ : j ≫ᵣ f₀ = f₀' ≫ᵣ g₀)
    (s1 : (F iV) ⋙ (F g₀) ⟶ (F g) ⋙ (F iV'))
    (s2 : (F iV') ⋙ (F f₀') ⟶ (F f') ⋙ (F iU'))
    (s3 : (F g) ⋙ (F f') ⟶ (F f) ⋙ (F g'))
    (s4 : (F g₀) ⋙ (F f₀') ⟶ (F f₀) ⋙ (F j))
    (s5 : (F iV) ⋙ (F f₀) ⟶ (F f) ⋙ (F iU))
    (s6 : (F iU) ⋙ (F j) ⟶ (F g') ⋙ (F iU'))
    (e1 : abstractCubeSquare D F K g₀ iV iV' g he = s1)
    (e2 : abstractCubeSquare D F K f₀' iV' iU' f' hd' = s2)
    (e3 : abstractCubeSquare D F K f' g g' f h.symm = s3)
    (e4 : abstractCubeSquare D F K f₀' g₀ j f₀ h₀.symm = s4)
    (e5 : abstractCubeSquare D F K f₀ iV iU f hd = s5)
    (e6 : abstractCubeSquare D F K j iU iU' g' hj = s6)
    (M : D S) (Q : Cat) (eQ : Cat.of (D U') = Q)
    (QA QB QC QD QE QF : Q)
    (q1 : QA ⟶ QB) (q2 : QB ⟶ QC) (q3 : QC ⟶ QD)
    (q4 : QA ⟶ QE) (q5 : QE ⟶ QF) (q6 : QF ⟶ QD)
    (oA : HEq ((F f₀').obj ((F iV ⋙ F g₀).obj M)) QA)
    (oB : HEq ((F f₀').obj ((F g ⋙ F iV').obj M)) QB)
    (oC : HEq ((F iU').obj ((F g ⋙ F f').obj M)) QC)
    (oD : HEq ((F iU').obj ((F f ⋙ F g').obj M)) QD)
    (oE : HEq ((F j).obj ((F iV ⋙ F f₀).obj M)) QE)
    (oF : HEq ((F j).obj ((F f ⋙ F iU).obj M)) QF)
    (hq1 : HEq ((F f₀').map (s1.app M)) q1)
    (hq2 : HEq (s2.app ((F g).obj M)) q2)
    (hq3 : HEq ((F iU').map (s3.app M)) q3)
    (hq4 : HEq (s4.app ((F iV).obj M)) q4)
    (hq5 : HEq ((F j).map (s5.app M)) q5)
    (hq6 : HEq (s6.app ((F f).obj M)) q6) :
    q1 ≫ q2 ≫ q3 = q4 ≫ q5 ≫ q6 := by
  cases eQ
  cases eq_of_heq oA
  cases eq_of_heq oB
  cases eq_of_heq oC
  cases eq_of_heq oD
  cases eq_of_heq oE
  cases eq_of_heq oF
  cases eq_of_heq hq1
  cases eq_of_heq hq2
  cases eq_of_heq hq3
  cases eq_of_heq hq4
  cases eq_of_heq hq5
  cases eq_of_heq hq6
  exact abstractCubeSquare_cube_faces D F K H f f' g g' h iU iU' iV iV'
    f₀ f₀' g₀ j hd hd' he hj h₀ s1 s2 s3 s4 s5 s6 e1 e2 e3 e4 e5 e6 M

-- Congruence is proved before specializing, so checking a projection does not
-- require reducing the concrete module inverse-image construction.
universe v w
private theorem functor_obj_heq
    {A B A' B' : Type v}
    [c : Category.{w} A] [d : Category.{w} B]
    [c' : Category.{w} A'] [d' : Category.{w} B']
    (eA : A = A') (eB : B = B') (ec : HEq c c') (ed : HEq d d')
    {F : A ⥤ B} {G : A' ⥤ B'} (hF : HEq F G)
    {x : A} {y : A'} (hx : HEq x y) : HEq (F.obj x) (G.obj y) := by
  cases eA
  cases eB
  cases eq_of_heq ec
  cases eq_of_heq ed
  cases eq_of_heq hF
  cases eq_of_heq hx
  rfl

private theorem functor_map_heq
    {A B A' B' : Type v}
    [c : Category.{w} A] [d : Category.{w} B]
    [c' : Category.{w} A'] [d' : Category.{w} B']
    (eA : A = A') (eB : B = B') (ec : HEq c c') (ed : HEq d d')
    {F : A ⥤ B} {G : A' ⥤ B'} (hF : HEq F G)
    {x y : A} {x' y' : A'} (hx : HEq x x') (hy : HEq y y')
    {f : x ⟶ y} {g : x' ⟶ y'} (hf : HEq f g) : HEq (F.map f) (G.map g) := by
  cases eA
  cases eB
  cases eq_of_heq ec
  cases eq_of_heq ed
  cases eq_of_heq hF
  cases eq_of_heq hx
  cases eq_of_heq hy
  cases eq_of_heq hf
  rfl

private theorem natTrans_app_heq
    {A B A' B' : Type v}
    [c : Category.{w} A] [d : Category.{w} B]
    [c' : Category.{w} A'] [d' : Category.{w} B']
    (eA : A = A') (eB : B = B') (ec : HEq c c') (ed : HEq d d')
    {F₁ F₂ : A ⥤ B} {G₁ G₂ : A' ⥤ B'}
    (hF₁ : HEq F₁ G₁) (hF₂ : HEq F₂ G₂)
    {n : F₁ ⟶ F₂} {m : G₁ ⟶ G₂} (hn : HEq n m)
    {x : A} {y : A'} (hx : HEq x y) : HEq (n.app x) (m.app y) := by
  cases eA
  cases eB
  cases eq_of_heq ec
  cases eq_of_heq ed
  cases eq_of_heq hF₁
  cases eq_of_heq hF₂
  cases eq_of_heq hn
  cases eq_of_heq hx
  rfl

local macro "cube_objects" : tactic =>
  `(tactic| (
    try dsimp only [Functor.comp_obj]
    repeat' apply functor_obj_heq rfl rfl HEq.rfl HEq.rfl HEq.rfl
    all_goals rfl))

local macro "cube_apps" : tactic =>
  `(tactic| (
    apply natTrans_app_heq rfl rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl HEq.rfl
    cube_objects))

-- These private proof definitions retain their inferred dependent types. Staging
-- specialization avoids repeatedly reducing the concrete module functor structures.
set_option linter.defProp false in
private def stageBase
    {X' X Y' Y U : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {j : U ⟶ Y} (C : OpenCube r j) :=
  abstractCubeSquare_cube_morphisms
    (U := vertex C.XU C.localRings.RX) (U' := vertex C.XU' C.localRings.RX')
    (V := vertex U C.localRings.RY) (V' := vertex C.YU' C.localRings.RY')
    (fun A : RingedVertex.{u} ↦ proEtaleRingModules A.scheme A.ring)
    (fun {S X : RingedVertex.{u}} (a : RingedMap S X) ↦
      proEtaleRingModulePullback a.hom X.ring S.ring a.coefficient) (@moduleCompositor)
    (fun a b c ↦ pull_assoc c b a (immersion_assoc c b a))
    (ringedMap f r.RY r.RX r.cf) (ringedMap f' r.RY' r.RX' r.cf')
    (ringedMap g r.RY r.RY' r.cg) (ringedMap g' r.RX r.RX' r.cg')

set_option linter.defProp false in
private def stageCoherence
    {X' X Y' Y U : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {j : U ⟶ Y} (C : OpenCube r j) :=
  stageBase r C
    (square_map_eq r)
    (ringedMap C.jX r.RX C.localRings.RX C.cjX)
    (ringedMap C.jX' r.RX' C.localRings.RX' C.cjX')
    (ringedMap j r.RY C.localRings.RY C.cj)
    (ringedMap C.jY' r.RY' C.localRings.RY' C.cjY')
    (ringedMap C.fU C.localRings.RY C.localRings.RX C.localRings.cf)
    (ringedMap C.fU' C.localRings.RY' C.localRings.RX' C.localRings.cf')
    (ringedMap C.gU C.localRings.RY C.localRings.RY' C.localRings.cg)
    (ringedMap C.gU' C.localRings.RX C.localRings.RX' C.localRings.cg')
    (square_map_eq C.sourceFace).symm (square_map_eq C.targetFace).symm
    (square_map_eq C.baseFace).symm (square_map_eq C.upperFace).symm
    (square_map_eq C.localRings)

set_option linter.defProp false in
private def stageFaces
    {X' X Y' Y U : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {j : U ⟶ Y} (C : OpenCube r j) :=
  stageCoherence r C
    C.baseFace.exchangeModuleSquare.hom C.targetFace.exchangeModuleSquare.hom
    r.exchangeModuleSquare.hom C.localRings.exchangeModuleSquare.hom
    C.sourceFace.exchangeModuleSquare.hom C.upperFace.exchangeModuleSquare.hom

set_option linter.defProp false in
private def stageProof
    {X' X Y' Y U : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {j : U ⟶ Y} (C : OpenCube r j) :=
  stageFaces r C
    (square_eq C.baseFace (square_map_eq C.baseFace).symm)
    (square_eq C.targetFace (square_map_eq C.targetFace).symm)
    (square_eq r (square_map_eq r).symm)
    (square_eq C.localRings (square_map_eq C.localRings).symm)
    (square_eq C.sourceFace (square_map_eq C.sourceFace).symm)
    (square_eq C.upperFace (square_map_eq C.upperFace).symm)

set_option linter.defProp false in
private def pointwiseBase
    {X' X Y' Y U : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {j : U ⟶ Y} (C : OpenCube r j)
    (M : proEtaleRingModules Y r.RY) :=
  stageProof r C M (Cat.of (proEtaleRingModules C.XU' C.localRings.RX')) rfl

set_option linter.defProp false in
private def pointwiseRight
    {X' X Y' Y U : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {j : U ⟶ Y} (C : OpenCube r j)
    (M : proEtaleRingModules Y r.RY) :=
  pointwiseBase r C M _ _ _ _ _ _
    ((targetPull C.localRings).map (C.baseFace.exchangeModuleSquare.hom.app M))
    (C.targetFace.exchangeModuleSquare.hom.app ((basePull r).obj M))
    ((upperPull C.targetFace).map (r.exchangeModuleSquare.hom.app M))
    (C.localRings.exchangeModuleSquare.hom.app ((basePull C.sourceFace).obj M))
    ((upperPull C.localRings).map (C.sourceFace.exchangeModuleSquare.hom.app M))
    (C.upperFace.exchangeModuleSquare.hom.app ((verticalPull r).obj M))

set_option linter.defProp false in
private def pointwiseObjects
    {X' X Y' Y U : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {j : U ⟶ Y} (C : OpenCube r j)
    (M : proEtaleRingModules Y r.RY) :=
  pointwiseRight r C M (by cube_objects) (by cube_objects) (by cube_objects)
    (by cube_objects) (by cube_objects) (by cube_objects)

set_option linter.defProp false in
private def pointwiseFace1
    {X' X Y' Y U : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {j : U ⟶ Y} (C : OpenCube r j)
    (M : proEtaleRingModules Y r.RY) :=
  pointwiseObjects r C M (by
    apply functor_map_heq rfl rfl HEq.rfl HEq.rfl HEq.rfl
    · cube_objects
    · cube_objects
    · cube_apps)

set_option linter.defProp false in
private def pointwiseFace2
    {X' X Y' Y U : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {j : U ⟶ Y} (C : OpenCube r j)
    (M : proEtaleRingModules Y r.RY) :=
  pointwiseFace1 r C M (by cube_apps)

set_option linter.defProp false in
private def pointwiseFace3
    {X' X Y' Y U : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {j : U ⟶ Y} (C : OpenCube r j)
    (M : proEtaleRingModules Y r.RY) :=
  pointwiseFace2 r C M (by
    apply functor_map_heq rfl rfl HEq.rfl HEq.rfl HEq.rfl
    · cube_objects
    · cube_objects
    · cube_apps)

set_option linter.defProp false in
private def pointwiseFace4
    {X' X Y' Y U : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {j : U ⟶ Y} (C : OpenCube r j)
    (M : proEtaleRingModules Y r.RY) :=
  pointwiseFace3 r C M (by cube_apps)

set_option linter.defProp false in
private def pointwiseFace5
    {X' X Y' Y U : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {j : U ⟶ Y} (C : OpenCube r j)
    (M : proEtaleRingModules Y r.RY) :=
  pointwiseFace4 r C M (by
    apply functor_map_heq rfl rfl HEq.rfl HEq.rfl HEq.rfl
    · cube_objects
    · cube_objects
    · cube_apps)

set_option linter.defProp false in
private def pointwiseFace6
    {X' X Y' Y U : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {j : U ⟶ Y} (C : OpenCube r j)
    (M : proEtaleRingModules Y r.RY) :=
  pointwiseFace5 r C M (by cube_apps)

/-- The six canonical module inverse-image squares commute around an open cube.
Source: Stacks Project, sites.tex Tag 03CB, composition of morphisms of sites,
and proetale.tex Tag 09A5, morphisms of pro-etale sites; step 7 of
lem-sf-ringed-restriction-exchange-open-descent.
(blueprint: lem-sf-ringed-restriction-pullback-cube).
Proof: expand each exchangeModuleSquare as the inverse compositor for its first
path followed by the compositor for its second path. All paths have the same
composite scheme map, by the Cartesian-square commutativity equations.
The coefficient coherence equations of the four side faces, r and C.localRings
identify the composite coefficient isomorphisms. Conjugate the ordinary compositors under
the composite module adjunctions. By exchangeModuleComposition_existsUnique,
their conjugates act on sections by the fibre-product pasting maps. The two
threefold pastings preserve all three projections, so the universal property
of the iterated fibre product identifies them. Faithfulness on module sections
and injectivity of adjunction conjugation give the compositor associativity
with these coefficient transports. Cancel the inverse pairs on the two routes
to obtain the displayed equation. The argument uses neither openness nor any
nonemptiness hypothesis, and applies to zero modules and empty schemes. -/
theorem restriction_pullback_cube
    {X' X Y' Y U : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {sq : ChosenCartesianSquare g' f' f g}
    (r : StrictTowerRingedSquare sq) {j : U ⟶ Y} (C : OpenCube r j)
    (M : proEtaleRingModules Y r.RY) :
    (targetPull C.localRings).map (C.baseFace.exchangeModuleSquare.hom.app M) ≫
        C.targetFace.exchangeModuleSquare.hom.app ((basePull r).obj M) ≫
        (upperPull C.targetFace).map (r.exchangeModuleSquare.hom.app M) =
      C.localRings.exchangeModuleSquare.hom.app ((basePull C.sourceFace).obj M) ≫
        (upperPull C.localRings).map (C.sourceFace.exchangeModuleSquare.hom.app M) ≫
        C.upperFace.exchangeModuleSquare.hom.app ((verticalPull r).obj M) := by
  exact pointwiseFace6 r C M

end AlgebraicGeometry.Scheme.RingedRestrictionExchange
