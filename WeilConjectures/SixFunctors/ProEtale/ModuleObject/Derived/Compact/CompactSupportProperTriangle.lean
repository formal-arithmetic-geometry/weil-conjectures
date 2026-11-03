/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageAssociativity

/-!
# Proper exchange along a commuting triangle

Source: blueprint det-sf-comp-composition-base-change, proof (3), proper mate pasting.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open scoped CategoryTheory.Functor CategoryTheory.Obj
namespace CategoryTheory
section FamilyCoherence

variable {I : Type*} [Category I] {C : I → Type*} [∀ i, Category (C i)]
    (D : ∀ {X Y : I}, (X ⟶ Y) → C Y ⥤ C X)
    (χ : ∀ {X Y Z : I} (f : X ⟶ Y) (g : Y ⟶ Z), D (f ≫ g) ≅ D g ⋙ D f)

variable (hc : ∀ {S T U V : I} (a : S ⟶ T) (b : T ⟶ U) (c : U ⟶ V)
    (M : C V), (χ (a ≫ b) c).hom.app M ≫ (χ a b).hom.app ((D c).obj M) =
      (eqToIso (congrArg D (Category.assoc a b c))).hom.app M ≫
        (χ a (b ≫ c)).hom.app M ≫ (D a).map ((χ b c).hom.app M))

include hc

end FamilyCoherence

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.CondensedRing

private theorem normalized_mate_pasting
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {P : A ⥤ B} {RP : B ⥤ A} {U : B ⥤ C} {RU : C ⥤ B}
    {P' : D ⥤ E} {RP' : E ⥤ D} {U' : E ⥤ F} {RU' : F ⥤ E}
    {Q : A ⥤ C} {RQ : C ⥤ A} {Q' : D ⥤ F} {RQ' : F ⥤ D}
    {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
    (a : P ⊣ RP) (b : U ⊣ RU) (a' : P' ⊣ RP') (b' : U' ⊣ RU')
    (c : Q ⊣ RQ) (c' : Q' ⊣ RQ') (u : Q ≅ P ⋙ U) (u' : Q' ≅ P' ⋙ U')
    (α : TwoSquare G P P' H) (β : TwoSquare H U U' K)
    (κ : RQ ≅ RU ⋙ RP) (κ' : RQ' ≅ RU' ⋙ RP')
    (αm : RP ⋙ G ⟶ H ⋙ RP') (βm : RU ⋙ H ⟶ K ⋙ RU')
    (γm : RQ ⋙ G ⟶ K ⋙ RQ')
    (hκ : κ = conjugateIsoEquiv c (a.comp b) u.symm)
    (hκ' : κ' = conjugateIsoEquiv c' (a'.comp b') u'.symm)
    (hα : αm = (mateEquiv a a' α).natTrans)
    (hβ : βm = (mateEquiv b b' β).natTrans)
    (hγ : γm = (mateEquiv c c' (TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft G u'.hom ≫ (TwoSquare.vComp α β).natTrans ≫
        Functor.whiskerRight u.inv K))).natTrans) (X : C) :
    γm.app X = G.map (κ.hom.app X) ≫ αm.app (RU.obj X) ≫
      RP'.map (βm.app X) ≫ κ'.inv.app (K.obj X) := by
  subst κ
  subst κ'
  subst αm
  subst βm
  subst γm
  have h := mateEquiv_conjugateEquiv_vcomp c (a'.comp b') c'
    ((TwoSquare.vComp α β).whiskerLeft u.inv) u'.hom
  rw [conjugateEquiv_mateEquiv_vcomp c (a.comp b) (a'.comp b'),
    mateEquiv_hcomp a a' b b'] at h
  have hh := congrArg (fun w ↦ w.natTrans.app X) h
  simpa only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hComp,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id, Category.assoc, conjugateIsoEquiv_apply_hom, conjugateIsoEquiv_apply_inv,
    TwoSquare.mk, TwoSquare.natTrans,
    Iso.symm_hom, Iso.symm_inv] using hh

private theorem mate_change_left
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L Le : A ⥤ B} {R : B ⥤ A} {K Ke : C ⥤ D} {S : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D} (a : L ⊣ R) (b : K ⊣ S)
    (eL : L ≅ Le) (eK : K ≅ Ke) (θ : G ⋙ K ⟶ L ⋙ H) :
    (mateEquiv (a.ofNatIsoLeft eL) (b.ofNatIsoLeft eK)
      (TwoSquare.mk _ _ _ _
        (Functor.whiskerLeft G eK.inv ≫ θ ≫ Functor.whiskerRight eL.hom H))).natTrans =
      (mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).natTrans := by
  ext X
  simp only [mateEquiv_apply, Adjunction.ofNatIsoLeft_unit,
    Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
    Functor.leftUnitor_hom_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.map_comp, Category.id_comp,
    Category.assoc, Functor.comp_obj, Functor.comp_map]
  rw [← S.map_comp_assoc, Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← S.map_comp_assoc (H.map (eL.hom.app (R.obj X)))
    (H.map (eL.inv.app (R.obj X))), ← H.map_comp, Iso.hom_inv_id_app]
  simp

private theorem mate_change_horizontal
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {K : C ⥤ D} {S : D ⥤ C}
    {G Ge : A ⥤ C} {H He : B ⥤ D} (a : L ⊣ R) (b : K ⊣ S)
    (eG : G ≅ Ge) (eH : H ≅ He) (θ : G ⋙ K ⟶ L ⋙ H) (X : B) :
    (mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).natTrans.app X ≫
        S.map (eH.hom.app X) =
      eG.hom.app (R.obj X) ≫
        (mateEquiv a b (TwoSquare.mk _ _ _ _
          (Functor.whiskerRight eG.inv K ≫ θ ≫ Functor.whiskerLeft L eH.hom))).natTrans.app X := by
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
    Functor.leftUnitor_hom_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.map_comp, Category.id_comp,
    Category.assoc, Functor.comp_obj, Functor.comp_map]
  have hu := b.unit.naturality (eG.hom.app (R.obj X))
  simp only [Functor.id_map, Functor.comp_map] at hu
  rw [reassoc_of% hu]
  rw [← S.map_comp_assoc (K.map (eG.hom.app (R.obj X)))
    (K.map (eG.inv.app (R.obj X))), ← K.map_comp, Iso.hom_inv_id_app]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp, Category.comp_id]
  simp only [← S.map_comp]
  simpa only [TwoSquare.mk, TwoSquare.natTrans, Category.assoc,
    Functor.id_obj, Functor.comp_obj] using
    congrArg (fun f ↦ b.unit.app (G.obj (R.obj X)) ≫ S.map (θ.app (R.obj X) ≫ f))
      (eH.hom.naturality (a.counit.app X))

private theorem normalized_mate_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L Le : A ⥤ B} {R : B ⥤ A} {K Ke : C ⥤ D} {S : D ⥤ C}
    {G Ge : A ⥤ C} {H He : B ⥤ D}
    (a : L ⊣ R) (b : K ⊣ S) (ae : Le ⊣ R) (be : Ke ⊣ S)
    (eL : L ≅ Le) (eK : K ≅ Ke) (eG : G ≅ Ge) (eH : H ≅ He)
    (hL : a.ofNatIsoLeft eL = ae) (hK : b.ofNatIsoLeft eK = be)
    (θ : G ⋙ K ⟶ L ⋙ H) (θe : Ge ⋙ Ke ⟶ Le ⋙ He)
    (hs : Functor.whiskerRight eG.inv Ke ≫ Functor.whiskerLeft G eK.inv ≫ θ ≫
      Functor.whiskerRight eL.hom H ≫ Functor.whiskerLeft Le eH.hom = θe)
    (τ : R ⋙ G ⟶ H ⋙ S) (τe : R ⋙ Ge ⟶ He ⋙ S)
    (hτ : τ = (mateEquiv a b (TwoSquare.mk _ _ _ _ θ)).natTrans)
    (hτe : τe = (mateEquiv ae be (TwoSquare.mk _ _ _ _ θe)).natTrans) (X : B) :
    τ.app X ≫ S.map (eH.hom.app X) = eG.hom.app (R.obj X) ≫ τe.app X := by
  subst τ
  subst τe
  let φ := Functor.whiskerLeft G eK.inv ≫ θ ≫ Functor.whiskerRight eL.hom H
  have hv := mate_change_left a b eL eK θ
  rw [hL, hK] at hv
  have hh := mate_change_horizontal ae be eG eH φ X
  simp only [φ, Category.assoc] at hh
  rw [hs, hv] at hh
  exact hh

private theorem conjugate_iso_eq_of_inv
    {A B : Type*} [Category A] [Category B]
    {L L' : A ⥤ B} {R R' : B ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (e : L' ≅ L) (κ : R' ≅ R)
    (h : κ.inv = conjugateEquiv a b e.hom) :
    conjugateIsoEquiv b a e.symm = κ := by
  apply Iso.ext_inv
  exact h.symm

private theorem remove_reflexive_triangle
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {H : A ⥤ B} {G : B ⥤ C} {F : C ⥤ D}
    {FG : B ⥤ D} {GH : A ⥤ C} {V : A ⥤ D}
    (e₁ : V ≅ H ⋙ FG) (eFG : FG ≅ G ⋙ F)
    (e₂ : V ≅ GH ⋙ F) (eGH : GH ≅ H ⋙ G)
    (h : (Iso.refl _ ≪≫ e₁) ≪≫
      Functor.isoWhiskerLeft H (Iso.refl _ ≪≫ eFG) =
        e₂ ≪≫ Functor.isoWhiskerRight eGH F ≪≫ Functor.associator H G F) :
    e₁ ≪≫ Functor.isoWhiskerLeft H eFG =
      e₂ ≪≫ Functor.isoWhiskerRight eGH F ≪≫ Functor.associator H G F := by
  simpa only [Iso.refl_trans] using h

private theorem derivedTriangle_named
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {H : A ⥤ B} {G : B ⥤ C} {F : C ⥤ D}
    {FG : B ⥤ D} {GH : A ⥤ C} {V V₂ : A ⥤ D}
    [H.Additive] [G.Additive] [F.Additive] [FG.Additive] [GH.Additive] [V.Additive]
    [V₂.Additive]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits V₂] [PreservesFiniteColimits V₂]
    (e₁ : V ≅ H ⋙ FG) (eFG : FG ≅ G ⋙ F)
    (e₂ : V ≅ GH ⋙ F) (eGH : GH ≅ H ⋙ G)
    (h : e₁ ≪≫ Functor.isoWhiskerLeft H eFG =
      e₂ ≪≫ Functor.isoWhiskerRight eGH F ≪≫ Functor.associator H G F)
    (hD : DerivedCategory A ⥤ DerivedCategory B)
    (gD : DerivedCategory B ⥤ DerivedCategory C)
    (fD : DerivedCategory C ⥤ DerivedCategory D)
    (fgD : DerivedCategory B ⥤ DerivedCategory D)
    (ghD : DerivedCategory A ⥤ DerivedCategory C)
    (vD v₂D : DerivedCategory A ⥤ DerivedCategory D)
    (hH : hD = H.mapDerivedCategory) (hG : gD = G.mapDerivedCategory)
    (hF : fD = F.mapDerivedCategory) (hFGf : fgD = FG.mapDerivedCategory)
    (hGHf : ghD = GH.mapDerivedCategory) (hV : vD = V.mapDerivedCategory)
    (hV₂ : v₂D = V₂.mapDerivedCategory)
    (d₁ : vD ≅ hD ⋙ fgD)
    (dFG : fgD ≅ gD ⋙ fD)
    (ε : vD ≅ v₂D)
    (d₂ : v₂D ≅ ghD ⋙ fD)
    (dGH : ghD ≅ hD ⋙ gD)
    (h₁ : HEq d₁ (Functor.mapDerivedCategoryTriangleIso e₁))
    (hFG : HEq dFG (Functor.mapDerivedCategoryTriangleIso eFG))
    (h₂ : HEq (ε ≪≫ d₂) (Functor.mapDerivedCategoryTriangleIso e₂))
    (hGH : HEq dGH (Functor.mapDerivedCategoryTriangleIso eGH))
    (M : DerivedCategory A) :
    d₁.hom.app M ≫ dFG.hom.app (hD.obj M) =
      ε.hom.app M ≫ d₂.hom.app M ≫ fD.map (dGH.hom.app M) := by
  subst hD
  subst gD
  subst fD
  subst fgD
  subst ghD
  subst vD
  subst v₂D
  have ht := derivedTriangle_pasting e₁ eFG e₂ eGH h
  rw [← eq_of_heq h₁, ← eq_of_heq hFG, ← eq_of_heq h₂, ← eq_of_heq hGH] at ht
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Iso.trans_hom, Category.assoc] using congr_app ht M

private def familySquare {X' X Y' Y : I}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : g' ≫ f = f' ≫ g) : D g ⋙ D f' ≅ D f ⋙ D g' :=
  (χ f' g).symm ≪≫ eqToIso (congrArg D h.symm) ≪≫ χ g' f

private theorem familySquare_transpose {X' X Y' Y : I}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : g' ≫ f = f' ≫ g) :
    familySquare D χ f' g' g f h.symm = (familySquare D χ g' f' f g h).symm := by
  simp only [familySquare, Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc]
  rfl

@[reassoc]
private theorem familyComp_assocInv {S T U V : I}
    (a : S ⟶ T) (b : T ⟶ U) (c : U ⟶ V)
    (M : C V) :
    (χ a (b ≫ c)).hom.app M ≫
        (D a).map ((χ b c).hom.app M) =
      (eqToIso (congrArg (D) (Category.assoc a b c).symm)).hom.app M ≫
        (χ (a ≫ b) c).hom.app M ≫
          (χ a b).hom.app ((D c).obj M) := by
  have h := hc a b c M
  have hh := congrArg (fun f ↦
    (eqToIso (congrArg (D) (Category.assoc a b c).symm)).hom.app M ≫ f) h
  simpa only [Category.assoc, eqToIso.hom, eqToHom_app, eqToHom_trans_assoc,
    eqToHom_refl, NatTrans.id_app, Category.id_comp] using hh.symm

private theorem familySquare_paste
    {X X' X'' Y Y' Y'' : I}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    {h : Y'' ⟶ Y'} {h' : X'' ⟶ X'} {f'' : X'' ⟶ Y''}
    (sq₁ : CommSq g' f' f g) (sq₂ : CommSq h' f'' f' h)
    (sq : CommSq (h' ≫ g') f'' f (h ≫ g))
    (s₁ : D g ⋙ D f' ≅ D f ⋙ D g')
    (s₂ : D h ⋙ D f'' ≅ D f' ⋙ D h')
    (s : D (h ≫ g) ⋙ D f'' ≅ D f ⋙ D (h' ≫ g'))
    (hs₁ : s₁ = familySquare D χ g' f' f g sq₁.w)
    (hs₂ : s₂ = familySquare D χ h' f'' f' h sq₂.w)
    (hs : s = familySquare D χ (h' ≫ g') f'' f (h ≫ g) sq.w)
    (M : C Y) :
    (D f'').map ((χ h g).hom.app M) ≫
        s₂.hom.app ((D g).obj M) ≫
          (D h').map (s₁.hom.app M) =
      s.hom.app M ≫
        (χ h' g').hom.app ((D f).obj M) := by
  subst s₁
  subst s₂
  subst s
  rw [← cancel_epi ((χ f'' (h ≫ g)).hom.app M)]
  simp only [familySquare, Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom]
  simp only [Category.assoc, Functor.map_comp, Iso.hom_inv_id_app_assoc]
  rw [familyComp_assocInv_assoc D χ hc f'' h g, Iso.hom_inv_id_app_assoc,
    familyComp_eq_left_assoc D χ sq₂.w.symm g,
    reassoc_of% (hc h' f' g M),
    ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    familyComp_eq_right_assoc D χ h' sq₁.w.symm,
    familyComp_assocInv D χ hc h' g' f]
  simp only [eqToIso.hom, eqToHom_app, eqToHom_trans_assoc]

private theorem familySquare_vpaste
    {A A' B B' C C' : I}
    (a : A ⟶ B) (p : B ⟶ C) (a' : A' ⟶ B') (p' : B' ⟶ C')
    (vA : A' ⟶ A) (vB : B' ⟶ B) (v : C' ⟶ C)
    (ha : vA ≫ a = a' ≫ vB) (hp : vB ≫ p = p' ≫ v)
    (hq : vA ≫ (a ≫ p) = (a' ≫ p') ≫ v)
    (sA : D vB ⋙ D a' ≅ D a ⋙ D vA)
    (sP : D v ⋙ D p' ≅ D p ⋙ D vB)
    (sQ : D v ⋙ D (a' ≫ p') ≅ D (a ≫ p) ⋙ D vA)
    (hsA : sA = familySquare D χ vA a' a vB ha)
    (hsP : sP = familySquare D χ vB p' p v hp)
    (hsQ : sQ = familySquare D χ vA (a' ≫ p') (a ≫ p) v hq) :
    sQ.hom =
      Functor.whiskerLeft (D v) (χ a' p').hom ≫
        (TwoSquare.vComp
          (TwoSquare.mk _ _ _ _ sP.hom)
          (TwoSquare.mk _ _ _ _ sA.hom)).natTrans ≫
        Functor.whiskerRight (χ a p).inv (D vA) := by
  subst sA
  subst sP
  subst sQ
  have he :
      Functor.isoWhiskerRight (χ a p) (D vA) ≪≫
          Functor.isoWhiskerLeft (D p) (familySquare D χ vA a' a vB ha).symm ≪≫
          Functor.isoWhiskerRight (familySquare D χ vB p' p v hp).symm (D a') =
        (familySquare D χ vA (a' ≫ p') (a ≫ p) v hq).symm ≪≫
          Functor.isoWhiskerLeft (D v) (χ a' p') := by
    apply Iso.ext
    ext M
    have h := familySquare_paste D χ hc (CommSq.mk hp.symm) (CommSq.mk ha.symm)
      (CommSq.mk hq.symm)
      (familySquare D χ p' vB v p hp.symm)
      (familySquare D χ a' vA vB a ha.symm)
      (familySquare D χ (a' ≫ p') vA v (a ≫ p) hq.symm) rfl rfl rfl M
    rw [familySquare_transpose D χ vB p' p v hp,
      familySquare_transpose D χ vA a' a vB ha,
      familySquare_transpose D χ vA (a' ≫ p') (a ≫ p) v hq] at h
    exact h
  ext M
  have hi := congrArg (fun i ↦ i.inv.app M) he
  simp only [Iso.trans_inv, Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hi
  have hh := congrArg (fun f ↦ (χ a' p').hom.app
    ((D v).obj M) ≫ f) hi
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc] at hh
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    TwoSquare.vComp, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]
  exact hh.symm

/-- Direct-image composition followed by the specified equality of scheme maps.
Source: blueprint det-sf-comp-composition-base-change, proof (3).
(blueprint: lem-sfb-compact-support-proper-triangle). -/
def compactSupportPushforwardTriangle
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B C : Scheme.{u}} (a : A ⟶ B) (p : B ⟶ C) (q : A ⟶ C)
    (e : a ≫ p = q) :
    R((a)_*⟦Λ⟧) ⋙ R((p)_*⟦Λ⟧) ≅ R((q)_*⟦Λ⟧) :=
  (refinementDerivedLowerStarComp Λ a p).symm ≪≫
    Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ e)

/-- Pull back a morphism of triangles to the two literal fibre products.
Source: blueprint det-sf-comp-composition-base-change, proof (3).
(blueprint: lem-sfb-compact-support-proper-triangle). -/
def compactSupportTrianglePullback
    {A B Y Y' : Scheme.{u}} (a : A ⟶ B) (p : B ⟶ Y) (q : A ⟶ Y)
    (e : a ≫ p = q) (v : Y' ⟶ Y) : pullback q v ⟶ pullback p v :=
  pullback.map q v p v a (𝟙 Y') (𝟙 Y) (by simpa using e.symm) (by simp)

/-- The Cartesian square of a pulled-back morphism of triangles.
Source: base change of a refinement, as in Compactification.Refinement.ofIsPullback.
(blueprint: lem-sfb-compact-support-proper-triangle). -/
def compactSupportTrianglePullbackSquare
    {A B Y Y' : Scheme.{u}} (a : A ⟶ B) (p : B ⟶ Y) (q : A ⟶ Y)
    (e : a ≫ p = q) (v : Y' ⟶ Y) :
    ChosenCartesianSquare (pullback.fst q v) (compactSupportTrianglePullback a p q e v)
      a (pullback.fst p v) := by
  have hfst : compactSupportTrianglePullback a p q e v ≫ pullback.fst p v =
      pullback.fst q v ≫ a := by simp [compactSupportTrianglePullback]
  have hp : IsPullback (compactSupportTrianglePullback a p q e v) (pullback.fst q v)
      (pullback.fst p v) a := by
    refine IsPullback.of_right ?_ hfst (IsPullback.of_hasPullback p v).flip
    have hsnd : compactSupportTrianglePullback a p q e v ≫ pullback.snd p v =
        pullback.snd q v := by simp [compactSupportTrianglePullback]
    rw [hsnd, e]
    exact (IsPullback.of_hasPullback q v).flip
  exact
    { toCommSq := hp.flip.toCommSq
      isoPullback := hp.flip.isoPullback
      hom_fst := hp.flip.isoPullback_hom_fst
      hom_snd := hp.flip.isoPullback_hom_snd }

attribute [local irreducible] CategoryTheory.Mod.monoidalCategory
  CategoryTheory.Mod.monoidalCategoryStruct upperStar lowerStar upperStarComp
  upperStarLowerStarAdjunction derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarIsoMapDerivedCategory DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed upperStarFromPoint
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private abbrev exactUpper {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar Λ f).mapDerivedCategory

private def exactComp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    exactUpper Λ (f ≫ g) ≅ exactUpper Λ g ⋙ exactUpper Λ f :=
  Functor.mapDerivedCategoryTriangleIso (upperStarComp Λ f g)

private def exactSquare {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : g' ≫ f = f' ≫ g) :
    exactUpper Λ g ⋙ exactUpper Λ f' ≅ exactUpper Λ f ⋙ exactUpper Λ g' :=
  (exactComp Λ f' g).symm ≪≫
    eqToIso (congrArg (exactUpper Λ) h.symm) ≪≫ exactComp Λ g' f

private def exactExchange {X' X Y' Y : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : g' ≫ f = f' ≫ g) :
    (lowerStar Λ f).rightDerivedFunctor ⋙ exactUpper Λ g ⟶
      exactUpper Λ g' ⋙ (lowerStar Λ f').rightDerivedFunctor :=
  (mateEquiv
    (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ f').mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (exactSquare Λ g' f' f g h).hom)).natTrans

omit [IsCommMonObj Λ] in
private theorem derive_transport {A B : Scheme.{u}} {f g : A ⟶ B} (e : f = g) :
    Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ e) =
      eqToIso (congrArg (fun f ↦ (lowerStar Λ f).rightDerivedFunctor) e) := by
  cases e
  apply Iso.ext
  simp [lowerStarCongr, Functor.rightDerivedFunctorNatIso,
    Functor.rightDerivedFunctorNatTrans]
private theorem pull_comp_exact {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    leftDerivedUpperStarComp Λ f g =
      leftDerivedUpperStarIsoMapDerivedCategory Λ (f ≫ g) ≪≫
      exactComp Λ f g ≪≫
      Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm
        (upperStar Λ f).mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (upperStar Λ g).leftDerivedFunctor
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm := by
  simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, leftDerivedUpperStarIsoMapDerivedCategory,
    exactComp, Iso.trans_assoc]
private theorem pull_eq_exact {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    eqToIso (congrArg (fun f ↦ (upperStar Λ f).leftDerivedFunctor) h) ≪≫
        leftDerivedUpperStarIsoMapDerivedCategory Λ g =
      leftDerivedUpperStarIsoMapDerivedCategory Λ f ≪≫
        eqToIso (congrArg (exactUpper Λ) h) := by
  cases h
  simp
set_option maxHeartbeats 1000000 in
-- Derived-functor instance synthesis and kernel conversion need a higher limit.
private theorem square_exact {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g) :
    Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ g).symm
        (upperStar Λ f').mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (upperStar Λ g).leftDerivedFunctor
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f').symm ≪≫
      condensedAmbientPullbackComparison Λ sq ≪≫
      Functor.isoWhiskerRight (leftDerivedUpperStarIsoMapDerivedCategory Λ f)
        (upperStar Λ g').leftDerivedFunctor ≪≫
      Functor.isoWhiskerLeft (upperStar Λ f).mapDerivedCategory
        (leftDerivedUpperStarIsoMapDerivedCategory Λ g') =
      exactSquare Λ g' f' f g sq.toCommSq.w := by
  simp only [condensedAmbientPullbackComparison, pull_comp_exact, Iso.trans_symm,
    Iso.symm_symm_eq, ← Functor.isoWhiskerLeft_symm, ← Functor.isoWhiskerRight_symm,
    Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [Functor.isoWhiskerLeft_symm,
    Functor.isoWhiskerLeft_trans_isoWhiskerRight_assoc]
  simp only [← Functor.isoWhiskerLeft_symm, Iso.symm_self_id, Iso.trans_refl]
  rw [← Iso.trans_assoc (eqToIso (congrArg
    (fun f ↦ (upperStar Λ f).leftDerivedFunctor) sq.toCommSq.w.symm))
    (leftDerivedUpperStarIsoMapDerivedCategory Λ (g' ≫ f))]
  rw [pull_eq_exact Λ sq.toCommSq.w.symm]
  simp only [exactSquare, Iso.trans_assoc,
    Iso.symm_self_id_assoc]

private theorem exchange_exact {X' X Y' Y : Scheme.{u}}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (condensedAmbientExchange Λ sq).app M ≫
      (lowerStar Λ f').rightDerivedFunctor.map
        ((leftDerivedUpperStarIsoMapDerivedCategory Λ g').hom.app M) =
      (leftDerivedUpperStarIsoMapDerivedCategory Λ g).hom.app
          ((lowerStar Λ f).rightDerivedFunctor.obj M) ≫
        (exactExchange Λ g' f' f g sq.toCommSq.w).app M := by
  have hs := congrArg Iso.hom (square_exact Λ sq)
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom] at hs
  exact CategoryTheory.normalized_mate_transport
      (derivedUpperStarLowerStarAdjunction Λ f)
      (derivedUpperStarLowerStarAdjunction Λ f')
      (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction
      (upperStarLowerStarAdjunction Λ f').mapDerivedCategoryRightDerivedAdjunction
      (leftDerivedUpperStarIsoMapDerivedCategory Λ f)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ f')
      (leftDerivedUpperStarIsoMapDerivedCategory Λ g)
      (leftDerivedUpperStarIsoMapDerivedCategory Λ g')
      (refinementAdjunction_eq Λ f) (refinementAdjunction_eq Λ f')
      (condensedAmbientPullbackComparison Λ sq).hom
      (exactSquare Λ g' f' f g sq.toCommSq.w).hom hs
      (condensedAmbientExchange Λ sq) (exactExchange Λ g' f' f g sq.toCommSq.w)
      rfl rfl M

private theorem derive_upper_triangle {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) {j : X ⟶ Z} (h : j = f ≫ g) :
    Functor.mapDerivedCategoryTriangleIso
        (eqToIso (congrArg (upperStar Λ) h) ≪≫ upperStarComp Λ f g) =
      eqToIso (congrArg (exactUpper Λ) h) ≪≫ exactComp Λ f g := by
  subst j
  simp only [eqToIso_refl, Iso.refl_trans, exactComp]

private theorem exactComp_assoc {S T U V : Scheme.{u}}
    (a : S ⟶ T) (b : T ⟶ U) (c : U ⟶ V)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology V) Ab.{u + 1}) (condensedRingObj Λ V))) :
    (exactComp Λ (a ≫ b) c).hom.app M ≫
        (exactComp Λ a b).hom.app ((exactUpper Λ c).obj M) =
      (eqToIso (congrArg (exactUpper Λ) (Category.assoc a b c))).hom.app M ≫
        (exactComp Λ a (b ≫ c)).hom.app M ≫
          (exactUpper Λ a).map ((exactComp Λ b c).hom.app M) := by
  exact CategoryTheory.derivedTriangle_named
    (upperStarComp Λ (a ≫ b) c) (upperStarComp Λ a b)
    (eqToIso (congrArg (upperStar Λ) (Category.assoc a b c)) ≪≫
      upperStarComp Λ a (b ≫ c)) (upperStarComp Λ b c)
    (CategoryTheory.remove_reflexive_triangle
      (upperStarComp Λ (a ≫ b) c) (upperStarComp Λ a b)
      (eqToIso (congrArg (upperStar Λ) (Category.assoc a b c)) ≪≫
        upperStarComp Λ a (b ≫ c)) (upperStarComp Λ b c)
      (refinementPullback_triangle Λ ((a ≫ b) ≫ c) (a ≫ b) a b c rfl rfl
        (Category.assoc a b c).symm))
    (exactUpper Λ c) (exactUpper Λ b) (exactUpper Λ a)
    (exactUpper Λ (a ≫ b)) (exactUpper Λ (b ≫ c))
    (exactUpper Λ ((a ≫ b) ≫ c)) (exactUpper Λ (a ≫ b ≫ c))
    rfl rfl rfl rfl rfl rfl rfl
    (exactComp Λ (a ≫ b) c) (exactComp Λ a b)
    (eqToIso (congrArg (exactUpper Λ) (Category.assoc a b c))) (exactComp Λ a (b ≫ c))
    (exactComp Λ b c) HEq.rfl HEq.rfl
    (heq_of_eq (derive_upper_triangle Λ a (b ≫ c) (Category.assoc a b c)).symm) HEq.rfl M

private theorem exactSquare_vpaste
    {A A' B B' C C' : Scheme.{u}}
    (a : A ⟶ B) (p : B ⟶ C) (a' : A' ⟶ B') (p' : B' ⟶ C')
    (vA : A' ⟶ A) (vB : B' ⟶ B) (v : C' ⟶ C)
    (ha : vA ≫ a = a' ≫ vB) (hp : vB ≫ p = p' ≫ v)
    (hq : vA ≫ (a ≫ p) = (a' ≫ p') ≫ v) :
    (exactSquare Λ vA (a' ≫ p') (a ≫ p) v hq).hom =
      Functor.whiskerLeft (exactUpper Λ v) (exactComp Λ a' p').hom ≫
        (TwoSquare.vComp
          (TwoSquare.mk _ _ _ _ (exactSquare Λ vB p' p v hp).hom)
          (TwoSquare.mk _ _ _ _ (exactSquare Λ vA a' a vB ha).hom)).natTrans ≫
        Functor.whiskerRight (exactComp Λ a p).inv (exactUpper Λ vA) := by
  exact CategoryTheory.familySquare_vpaste (exactUpper Λ) (exactComp Λ)
    (fun {_ _ _ _} a b c M ↦ exactComp_assoc Λ a b c M)
    a p a' p' vA vB v ha hp hq
    (exactSquare Λ vA a' a vB ha) (exactSquare Λ vB p' p v hp)
    (exactSquare Λ vA (a' ≫ p') (a ≫ p) v hq) rfl rfl rfl

private theorem exact_comp_conjugate {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateIsoEquiv
        (upperStarLowerStarAdjunction Λ (f ≫ g)).mapDerivedCategoryRightDerivedAdjunction
        ((upperStarLowerStarAdjunction Λ g).mapDerivedCategoryRightDerivedAdjunction.comp
          (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction)
        (exactComp Λ f g).symm = refinementDerivedLowerStarComp Λ f g := by
  exact CategoryTheory.conjugate_iso_eq_of_inv
      ((upperStarLowerStarAdjunction Λ g).mapDerivedCategoryRightDerivedAdjunction.comp
        (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction)
      (upperStarLowerStarAdjunction Λ (f ≫ g)).mapDerivedCategoryRightDerivedAdjunction
      (Functor.mapDerivedCategoryTriangleIso (upperStarComp Λ f g))
      (refinementDerivedLowerStarComp Λ f g) (refinementComp_conjugate Λ f g)

private theorem exactExchange_paste
    {A A' B B' C C' : Scheme.{u}}
    (a : A ⟶ B) (p : B ⟶ C) (a' : A' ⟶ B') (p' : B' ⟶ C')
    (vA : A' ⟶ A) (vB : B' ⟶ B) (v : C' ⟶ C)
    (ha : vA ≫ a = a' ≫ vB) (hp : vB ≫ p = p' ≫ v)
    (hq : vA ≫ (a ≫ p) = (a' ≫ p') ≫ v)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A))) :
    (exactExchange Λ vA (a' ≫ p') (a ≫ p) v hq).app M =
      (exactUpper Λ v).map ((refinementDerivedLowerStarComp Λ a p).hom.app M) ≫
        (exactExchange Λ vB p' p v hp).app ((lowerStar Λ a).rightDerivedFunctor.obj M) ≫
        (lowerStar Λ p').rightDerivedFunctor.map
          ((exactExchange Λ vA a' a vB ha).app M) ≫
        (refinementDerivedLowerStarComp Λ a' p').inv.app ((exactUpper Λ vA).obj M) := by
  exact CategoryTheory.normalized_mate_pasting
    (upperStarLowerStarAdjunction Λ p).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ a).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ p').mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ a').mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ (a ≫ p)).mapDerivedCategoryRightDerivedAdjunction
    (upperStarLowerStarAdjunction Λ (a' ≫ p')).mapDerivedCategoryRightDerivedAdjunction
    (exactComp Λ a p) (exactComp Λ a' p')
    (TwoSquare.mk _ _ _ _ (exactSquare Λ vB p' p v hp).hom)
    (TwoSquare.mk _ _ _ _ (exactSquare Λ vA a' a vB ha).hom)
    (refinementDerivedLowerStarComp Λ a p) (refinementDerivedLowerStarComp Λ a' p')
    (exactExchange Λ vB p' p v hp) (exactExchange Λ vA a' a vB ha)
    (exactExchange Λ vA (a' ≫ p') (a ≫ p) v hq)
    (exact_comp_conjugate Λ a p).symm (exact_comp_conjugate Λ a' p').symm
    rfl rfl (by rw [← exactSquare_vpaste Λ a p a' p' vA vB v ha hp hq]; rfl) M

private theorem exact_triangle
    {A A' B B' C C' : Scheme.{u}}
    (a : A ⟶ B) (p : B ⟶ C) (q : A ⟶ C) (e : a ≫ p = q)
    (a' : A' ⟶ B') (p' : B' ⟶ C') (q' : A' ⟶ C') (e' : a' ≫ p' = q')
    (vA : A' ⟶ A) (vB : B' ⟶ B) (v : C' ⟶ C)
    (ha : vA ≫ a = a' ≫ vB) (hp : vB ≫ p = p' ≫ v)
    (hq : vA ≫ q = q' ≫ v)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A))) :
    (upperStar Λ v).mapDerivedCategory.map
        ((compactSupportPushforwardTriangle Λ a p q e).hom.app M) ≫
      (exactExchange Λ vA q' q v hq).app M =
    (exactExchange Λ vB p' p v hp).app
        ((lowerStar Λ a).rightDerivedFunctor.obj M) ≫
      (lowerStar Λ p').rightDerivedFunctor.map
        ((exactExchange Λ vA a' a vB ha).app M) ≫
      (compactSupportPushforwardTriangle Λ a' p' q' e').hom.app
        ((upperStar Λ vA).mapDerivedCategory.obj M) := by
  subst q
  subst q'
  have hpaste :
      (exactExchange Λ vA (a' ≫ p') (a ≫ p) v hq).app M =
        (upperStar Λ v).mapDerivedCategory.map
            ((refinementDerivedLowerStarComp Λ a p).hom.app M) ≫
          (exactExchange Λ vB p' p v hp).app ((lowerStar Λ a).rightDerivedFunctor.obj M) ≫
          (lowerStar Λ p').rightDerivedFunctor.map
            ((exactExchange Λ vA a' a vB ha).app M) ≫
          (refinementDerivedLowerStarComp Λ a' p').inv.app
            ((upperStar Λ vA).mapDerivedCategory.obj M) := by
    exact exactExchange_paste Λ a p a' p' vA vB v ha hp hq M
  rw [hpaste]
  simp only [compactSupportPushforwardTriangle, Iso.trans_hom, Iso.symm_hom,
    derive_transport, eqToIso_refl, Iso.refl_hom, Category.comp_id,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]

private theorem ambient_triangle
    {A A' B B' C C' : Scheme.{u}}
    {a : A ⟶ B} {p : B ⟶ C} {q : A ⟶ C} (e : a ≫ p = q)
    {a' : A' ⟶ B'} {p' : B' ⟶ C'} {q' : A' ⟶ C'} (e' : a' ≫ p' = q')
    {vA : A' ⟶ A} {vB : B' ⟶ B} {v : C' ⟶ C}
    (sqA : ChosenCartesianSquare vA a' a vB)
    (sqP : ChosenCartesianSquare vB p' p v)
    (sqQ : ChosenCartesianSquare vA q' q v)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A))) :
    (upperStar Λ v).leftDerivedFunctor.map
        ((compactSupportPushforwardTriangle Λ a p q e).hom.app M) ≫
      (condensedAmbientExchange Λ sqQ).app M =
    (condensedAmbientExchange Λ sqP).app ((lowerStar Λ a).rightDerivedFunctor.obj M) ≫
      (lowerStar Λ p').rightDerivedFunctor.map ((condensedAmbientExchange Λ sqA).app M) ≫
      (compactSupportPushforwardTriangle Λ a' p' q' e').hom.app
        ((upperStar Λ vA).leftDerivedFunctor.obj M) := by
  apply (cancel_mono ((lowerStar Λ q').rightDerivedFunctor.map
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ vA).hom.app M))).1
  have hn := (compactSupportPushforwardTriangle Λ a' p' q' e').hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ vA).hom.app M)
  simp only [Functor.comp_map] at hn
  have he := exact_triangle Λ a p q e a' p' q' e' vA vB v
    sqA.toCommSq.w sqP.toCommSq.w sqQ.toCommSq.w M
  simp only [Category.assoc]
  rw [exchange_exact, (leftDerivedUpperStarIsoMapDerivedCategory Λ v).hom.naturality_assoc]
  rw [he]
  rw [← hn]
  rw [← (lowerStar Λ p').rightDerivedFunctor.map_comp_assoc
    ((condensedAmbientExchange Λ sqA).app M)
    ((lowerStar Λ a').rightDerivedFunctor.map
      ((leftDerivedUpperStarIsoMapDerivedCategory Λ vA).hom.app M)), exchange_exact]
  simp only [Functor.map_comp, Category.assoc]
  simpa only [Functor.comp_obj, Category.assoc] using congrArg (fun f ↦ f ≫
    (lowerStar Λ p').rightDerivedFunctor.map
      ((exactExchange Λ vA a' a vB sqA.toCommSq.w).app M) ≫
    (compactSupportPushforwardTriangle Λ a' p' q' e').hom.app
      ((exactUpper Λ vA).obj M))
    (exchange_exact Λ sqP ((lowerStar Λ a).rightDerivedFunctor.obj M)).symm

set_option maxHeartbeats 1000000 in
-- Derived-functor instance synthesis and kernel conversion need a higher limit.
set_option maxHeartbeats 1000000 in
-- Derived-functor instance synthesis and kernel conversion need a higher limit.
set_option maxHeartbeats 1000000 in
-- Derived-functor instance synthesis and kernel conversion need a higher limit.
set_option maxHeartbeats 1000000 in
-- Derived-functor instance synthesis and kernel conversion need a higher limit.
set_option maxHeartbeats 1000000 in
-- Derived-functor instance synthesis and kernel conversion need a higher limit.
set_option maxHeartbeats 1000000 in
-- Derived-functor instance synthesis and kernel conversion need a higher limit.
private theorem triangle_assoc {A B C D : Scheme.{u}}
    (s : A ⟶ B) (a : B ⟶ C) (p : C ⟶ D) (q : B ⟶ D)
    (r : A ⟶ C) (z : A ⟶ D) (e : a ≫ p = q)
    (es : s ≫ q = z) (er : r ≫ p = z) (esr : s ≫ a = r)
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A))) :
    (compactSupportPushforwardTriangle Λ a p q e).hom.app
        ((lowerStar Λ s).rightDerivedFunctor.obj N) ≫
      (compactSupportPushforwardTriangle Λ s q z es).hom.app N =
    (lowerStar Λ p).rightDerivedFunctor.map
        ((compactSupportPushforwardTriangle Λ s a r esr).hom.app N) ≫
      (compactSupportPushforwardTriangle Λ r p z er).hom.app N := by
  subst q
  subst r
  subst z
  simp only [compactSupportPushforwardTriangle, Iso.trans_hom, Iso.symm_hom,
    derive_transport, eqToIso_refl, Iso.refl_hom, Category.comp_id]
  have hc := congr_app (derivedDirectImageAssociativity Λ s a p) N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hc
  let T := Functor.rightDerivedFunctorNatIso
    (lowerStarCongr Λ (Category.assoc s a p))
  have hi :
      (directImageComposition Λ (s ≫ a) p).app N ≪≫
        (lowerStar Λ p).rightDerivedFunctor.mapIso ((directImageComposition Λ s a).app N) =
      T.app N ≪≫ (directImageComposition Λ s (a ≫ p)).app N ≪≫
        (directImageComposition Λ a p).app ((lowerStar Λ s).rightDerivedFunctor.obj N) := by
    apply Iso.ext
    exact hc
  have hh := congrArg (fun i ↦ i.inv ≫ T.hom.app N) hi
  simp only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, Category.assoc,
    Category.comp_id, T, derive_transport, eqToIso_refl,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app,
    directImageComposition] at hh
  erw [Category.comp_id] at hh
  exact hh.symm

/-- Pasting proper exchange with an arbitrary arrow and a further direct image.

Source: blueprint det-sf-comp-composition-base-change, proof (3), applying the final
proper pushforward; Mathlib's mateEquiv_hcomp and naturality of the right compositor.
(blueprint: lem-sfb-compact-support-proper-triangle).

Proof: first substitute the specified normalization hb of b. Normalize the direct-image
compositor by the K-injective derived units, so it
is the conjugate of the exact pullback compositor. The square for a followed by p
is the horizontal paste of their pullback squares; the pullback compositors identify
its comparison with that paste. Apply mateEquiv_hcomp and conjugate-mate pasting.
This gives the exchange for q as the exchange for p followed by the image of the
exchange for a, with the two displayed triangle compositors. Naturality moves t
across the pulled-back triangle compositor. Associativity of the direct-image
compositor identifies the resulting two maps into the direct image along z: on a
K-injective resolution both are the underived triple compositor, whose associativity
is the ordinary sectionwise associativity. The equality s followed by a' equals r
and the two equations to z identify the structural equality transports. This yields
the formula below. The argument uses no open immersion, compactification, density,
properness, coefficient admissibility or invertibility of an exchange or of t.
It therefore also applies to zero objects and empty schemes. -/
theorem compactSupportProperTriangle_pasting
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    {A B Y Y' W : Scheme.{u}} (a : A ⟶ B) (p : B ⟶ Y) (q : A ⟶ Y)
    (e : a ≫ p = q) (v : Y' ⟶ Y)
    (s : W ⟶ pullback q v) (r : W ⟶ pullback p v) (z : W ⟶ Y')
    (es : s ≫ pullback.snd q v = z) (er : r ≫ pullback.snd p v = z)
    (esr : s ≫ compactSupportTrianglePullback a p q e v = r)
    (M : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1}) (condensedRingObj Λ A)))
    (N : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) (condensedRingObj Λ W)))
    (t : (detSfDerivedPullback Λ (pullback.fst q v)).obj M ⟶ R((s)_*⟦Λ⟧).obj N)
    (b : R((p)_*⟦Λ⟧) ⋙ detSfDerivedPullback Λ v ⟶
      detSfDerivedPullback Λ (pullback.fst p v) ⋙ R((pullback.snd p v)_*⟦Λ⟧))
    (hb : b = detSfProperBaseChangeMap Λ p v) :
    (detSfDerivedPullback Λ v).map
        ((compactSupportPushforwardTriangle Λ a p q e).hom.app M) ≫
      (detSfProperBaseChangeMap Λ q v).app M ≫
      R((pullback.snd q v)_*⟦Λ⟧).map t ≫
      (compactSupportPushforwardTriangle Λ s (pullback.snd q v) z es).hom.app N =
    b.app (R((a)_*⟦Λ⟧).obj M) ≫
      R((pullback.snd p v)_*⟦Λ⟧).map
        ((condensedAmbientExchange Λ (compactSupportTrianglePullbackSquare a p q e v)).app M ≫
          R((compactSupportTrianglePullback a p q e v)_*⟦Λ⟧).map t ≫
          (compactSupportPushforwardTriangle Λ s
            (compactSupportTrianglePullback a p q e v) r esr).hom.app N) ≫
      (compactSupportPushforwardTriangle Λ r (pullback.snd p v) z er).hom.app N := by
  subst b
  have ep : compactSupportTrianglePullback a p q e v ≫ pullback.snd p v =
      pullback.snd q v := by simp [compactSupportTrianglePullback]
  have hbase := ambient_triangle Λ e ep
    (compactSupportTrianglePullbackSquare a p q e v)
    (detSfProperBaseChangeSquare p v) (detSfProperBaseChangeSquare q v) M
  have hn := (compactSupportPushforwardTriangle Λ
    (compactSupportTrianglePullback a p q e v) (pullback.snd p v)
    (pullback.snd q v) ep).hom.naturality t
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hbase, ← reassoc_of% hn]
  rw [triangle_assoc Λ s (compactSupportTrianglePullback a p q e v)
    (pullback.snd p v) (pullback.snd q v) r z ep es er esr N]

set_option maxHeartbeats 1000000 in
-- Derived-functor instance synthesis and kernel conversion need a higher limit.
end AlgebraicGeometry.ProEtale.CondensedRing
