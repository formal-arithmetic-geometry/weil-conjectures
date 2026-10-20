/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.Paper.RingedEtaleOriginWitness
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate

/-!
# Open-adjunction normalization of proper/open comparison on strict towers

Source: Stacks Project, Tags 0F7B, 0F7F and 0941; the strict diagram enhancement and
normalization are the explicit agent assertion in the blueprint
(blueprint: lem-sp-proper-open-tower-comparison).

All operations are the published constant-coefficient strict-tower operations. Positive
level `n+1` is indexed by `n : ℕ`. The restriction arrow is constructed using the
cartesian square mate, the clopen lift, and the normalized direct-image compositor.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale.StrictTower

set_option backward.defeqAttrib.useBackward true

private theorem mate_factor
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    {Ls : C₁ ⥤ C₀} {Rs : C₀ ⥤ C₁} {Lq : C₃ ⥤ C₁} {Rq : C₁ ⥤ C₃}
    {Lp : C₄ ⥤ C₂} {Rp : C₂ ⥤ C₄} {Lr : C₃ ⥤ C₀} {Rr : C₀ ⥤ C₃}
    {Ji : C₃ ⥤ C₄} {Jb : C₁ ⥤ C₂} {Js : C₀ ⥤ C₁} {Jk : C₀ ⥤ C₂}
    (aq : Lq ⊣ Rq) (as : Ls ⊣ Rs) (ap : Lp ⊣ Rp) (ar : Lr ⊣ Rr)
    (eL : Lq ⋙ Ls ≅ Lr) (eJ : Js ⋙ Jb ≅ Jk)
    (β : TwoSquare Ji Lq Lp Jb)
    (δ : TwoSquare Jb Ls (𝟭 C₂) (Js ⋙ Jb)) (M : C₀) :
    (mateEquiv ar ap
      ((((TwoSquare.vComp β δ).whiskerRight (Functor.rightUnitor Lp).inv).whiskerLeft
        eL.hom).whiskerBottom eJ.hom)).natTrans.app M =
      Ji.map ((conjugateIsoEquiv ar (aq.comp as) eL).hom.app M) ≫
        (mateEquiv aq ap β).natTrans.app (Rs.obj M) ≫
        Rp.map ((mateEquiv as Adjunction.id δ).natTrans.app M) ≫ Rp.map (eJ.hom.app M) := by
  rw [mateEquiv_whiskerBottom,
    conjugateEquiv_mateEquiv_vcomp _ (aq.comp as),
    mateEquiv_conjugateEquiv_vcomp _ (ap.comp Adjunction.id), mateEquiv_hcomp]
  have hu : conjugateEquiv (ap.comp Adjunction.id) ap (Functor.rightUnitor Lp).inv =
      (Functor.leftUnitor Rp).hom := by
    rw [← conjugateIsoEquiv_apply_inv, conjugateIsoEquiv_rightUnitor]
    rfl
  simp only [hu, TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
    TwoSquare.whiskerLeft_app, TwoSquare.hComp_app, Functor.leftUnitor_hom_app,
    Category.assoc, conjugateIsoEquiv_apply_hom, Functor.comp_obj]
  erw [Category.id_comp]

private theorem paste_alpha
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    {Ls : C₁ ⥤ C₀} {Lq : C₃ ⥤ C₁} {Lp : C₄ ⥤ C₂} {Lr : C₃ ⥤ C₀}
    {Ji : C₃ ⥤ C₄} {Jb : C₁ ⥤ C₂} {Js : C₀ ⥤ C₁} {Jk : C₀ ⥤ C₂}
    (eL : Lq ⋙ Ls ≅ Lr) (eJ : Js ⋙ Jb ≅ Jk)
    (β : Ji ⋙ Lp ⟶ Lq ⋙ Jb) (π : 𝟭 C₁ ⟶ Ls ⋙ Js) :
    β ≫ Functor.whiskerRight (Functor.whiskerLeft Lq π) Jb ≫
      Functor.whiskerRight (Functor.associator Lq Ls Js).inv Jb ≫
      (Functor.associator (Lq ⋙ Ls) Js Jb).hom ≫
      Functor.whiskerLeft (Lq ⋙ Ls) eJ.hom ≫ Functor.whiskerRight eL.hom Jk =
    ((((TwoSquare.vComp (TwoSquare.mk _ _ _ _ β)
      (TwoSquare.mk Jb Ls (𝟭 C₂) (Js ⋙ Jb)
        ((Functor.rightUnitor Jb).hom ≫ (Functor.leftUnitor Jb).inv ≫
          Functor.whiskerRight π Jb ≫ (Functor.associator Ls Js Jb).hom))).whiskerRight
      (Functor.rightUnitor Lp).inv).whiskerLeft eL.hom).whiskerBottom eJ.hom).natTrans := by
  ext N
  simp only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    TwoSquare.whiskerBottom, TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.leftUnitor_inv_app, Functor.id_map, Functor.comp_obj, Functor.comp_map,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [Jb.map_id, Category.id_comp, Category.id_comp]
  apply congrArg (β.app N ≫ ·)
  apply congrArg (Jb.map (π.app (Lq.obj N)) ≫ ·)
  exact (eJ.hom.naturality (eL.hom.app N)).symm

private theorem mate_unit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {G : D ⥤ C} {R J : C ⥤ D} (a : G ⊣ R) (F : D ⥤ E) (τ : R ⟶ J) :
    mateEquiv a Adjunction.id
      (TwoSquare.mk F G (𝟭 E) (J ⋙ F)
        ((Functor.rightUnitor F).hom ≫ (Functor.leftUnitor F).inv ≫
          Functor.whiskerRight (a.unit ≫ Functor.whiskerLeft G τ) F ≫
          (Functor.associator G J F).hom)) =
      Functor.whiskerRight τ F ≫ (Functor.rightUnitor (J ⋙ F)).inv := by
  ext M
  simp only [mateEquiv_apply, Adjunction.id, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_obj,
    Functor.comp_map, Functor.id_obj, Functor.id_map, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app,
    Category.id_comp, Category.comp_id, NatTrans.id_app]
  rw [← F.map_comp]
  congr 1
  have hn := τ.naturality (a.counit.app M)
  dsimp only [Functor.comp_obj, Functor.id_obj] at hn
  rw [Category.assoc, ← hn]
  exact a.right_triangle_components_assoc M _

private theorem mate_factor_unit
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    {Ls : C₁ ⥤ C₀} {Rs : C₀ ⥤ C₁} {Lq : C₃ ⥤ C₁} {Rq : C₁ ⥤ C₃}
    {Lp : C₄ ⥤ C₂} {Rp : C₂ ⥤ C₄} {Lr : C₃ ⥤ C₀} {Rr : C₀ ⥤ C₃}
    {Ji : C₃ ⥤ C₄} {Jb : C₁ ⥤ C₂} {Js : C₀ ⥤ C₁} {Jk : C₀ ⥤ C₂}
    (aq : Lq ⊣ Rq) (as : Ls ⊣ Rs) (ap : Lp ⊣ Rp) (ar : Lr ⊣ Rr)
    (eL : Lq ⋙ Ls ≅ Lr) (eR : Rs ⋙ Rq ≅ Rr) (eJ : Js ⋙ Jb ≅ Jk)
    (he : conjugateIsoEquiv ar (aq.comp as) eL = eR.symm)
    (β : TwoSquare Ji Lq Lp Jb) (τ : Rs ⟶ Js)
    (π : 𝟭 C₁ ⟶ Ls ⋙ Js) (hπ : π = as.unit ≫ Functor.whiskerLeft Ls τ)
    (α : TwoSquare Ji Lr Lp Jk)
    (hα : α =
      ((((TwoSquare.vComp β
        (TwoSquare.mk Jb Ls (𝟭 C₂) (Js ⋙ Jb)
          ((Functor.rightUnitor Jb).hom ≫ (Functor.leftUnitor Jb).inv ≫
            Functor.whiskerRight π Jb ≫
            (Functor.associator Ls Js Jb).hom))).whiskerRight
        (Functor.rightUnitor Lp).inv).whiskerLeft eL.hom).whiskerBottom eJ.hom))
    (γ : Rr ⋙ Ji ⟶ Jk ⋙ Rp) (hγ : γ = (mateEquiv ar ap α).natTrans) (M : C₀) :
    γ.app M =
      Ji.map (eR.inv.app M) ≫ (mateEquiv aq ap β).natTrans.app (Rs.obj M) ≫
        Rp.map (Jb.map (τ.app M)) ≫ Rp.map (eJ.hom.app M) := by
  rw [hγ, hα, hπ]
  have hf := mate_factor aq as ap ar eL eJ β
    (TwoSquare.mk Jb Ls (𝟭 C₂) (Js ⋙ Jb)
      ((Functor.rightUnitor Jb).hom ≫ (Functor.leftUnitor Jb).inv ≫
        Functor.whiskerRight (as.unit ≫ Functor.whiskerLeft Ls τ) Jb ≫
        (Functor.associator Ls Js Jb).hom)) M
  rw [he, mate_unit as Jb τ] at hf
  simpa only [Iso.symm_hom, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.rightUnitor_inv_app, Category.comp_id] using hf

private theorem cartesian_unit
    {C₁ C₂ C₃ C₄ : Type*}
    [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    {Gq : C₁ ⥤ C₃} {Rq : C₃ ⥤ C₁} {Gp : C₂ ⥤ C₄} {Rp : C₄ ⥤ C₂}
    {Ji : C₁ ⥤ C₂} {Gi : C₂ ⥤ C₁} {Jb : C₃ ⥤ C₄} {Gb : C₄ ⥤ C₃}
    (aq : Gq ⊣ Rq) (ap : Gp ⊣ Rp) (ai : Ji ⊣ Gi) (ab : Jb ⊣ Gb)
    (θ : Gi ⋙ Gq ⟶ Gp ⋙ Gb) (β : Ji ⋙ Gp ≅ Gq ⋙ Jb)
    (hβ : ∀ N, β.inv.app N = Jb.map (Gq.map (ai.unit.app N)) ≫
      Jb.map (θ.app (Ji.obj N)) ≫ ab.counit.app (Gp.obj (Ji.obj N))) (M : C₃) :
    ai.unit.app (Rq.obj M) ≫
        Gi.map ((mateEquiv aq ap (TwoSquare.mk _ _ _ _ β.hom)).natTrans.app M) ≫
        (mateEquiv ap aq (TwoSquare.mk _ _ _ _ θ)).natTrans.app (Jb.obj M) =
      Rq.map (ab.unit.app M) := by
  have hb := β.inv_hom_id_app (Rq.obj M)
  rw [hβ] at hb
  have hh := Adjunction.unit_app_comp_map_exchange_comp_baseChange aq ap ai ab θ M
    (β.hom.app (Rq.obj M)) hb
  simp only [mateEquiv_apply, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app, Functor.comp_obj,
    Functor.comp_map, Category.id_comp,
    TwoSquare.mk, TwoSquare.natTrans]
  erw [Category.comp_id, Category.comp_id]
  exact hh


-- Normalize the restriction recipe with abstract functors, retaining its defining equations.
private theorem restriction_app
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    {Rs Js : C₀ ⥤ C₁} {Rq : C₁ ⥤ C₃} {Rp : C₂ ⥤ C₄} {Rr : C₀ ⥤ C₃}
    {Gi : C₄ ⥤ C₃} {Jb : C₁ ⥤ C₂} {Gb : C₂ ⥤ C₁} {Jk : C₀ ⥤ C₂}
    (ab : Jb ⊣ Gb) [IsIso ab.unit] (τ : Js ⟶ Rs)
    (eJ : Js ⋙ Jb ≅ Jk) (eR : Rs ⋙ Rq ≅ Rr) (χ : Rp ⋙ Gi ⟶ Gb ⋙ Rq)
    (ext : Jk ⋙ Gb ≅ Js)
    (hext : ext = Functor.isoWhiskerRight eJ.symm Gb ≪≫
      Functor.associator Js Jb Gb ≪≫
      Functor.isoWhiskerLeft Js (asIso ab.unit).symm ≪≫ Functor.rightUnitor Js)
    (lam : (Jk ⋙ Rp) ⋙ Gi ⟶ Rr)
    (hlam : lam = (Functor.associator Jk Rp Gi).hom ≫ Functor.whiskerLeft Jk χ ≫
      (Functor.associator Jk Gb Rq).inv ≫ Functor.whiskerRight ext.hom Rq ≫
      Functor.whiskerRight τ Rq ≫ eR.hom) (M : C₀) :
    lam.app M = χ.app (Jk.obj M) ≫ Rq.map (Gb.map (eJ.inv.app M)) ≫
      Rq.map (inv (ab.unit.app (Js.obj M))) ≫ Rq.map (τ.app M) ≫ eR.hom.app M := by
  rw [hlam, hext]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_hom_app, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.map_comp, Functor.comp_obj, Category.id_comp,
    Category.assoc, asIso_inv, NatIso.isIso_inv_app]
  erw [Rq.map_id, Category.id_comp]

private theorem factor_unit
    {C₀ C₁ C₂ C₃ C₄ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    {Rs Js : C₀ ⥤ C₁} {Rq : C₁ ⥤ C₃} {Rp : C₂ ⥤ C₄} {Rr : C₀ ⥤ C₃}
    {Ji : C₃ ⥤ C₄} {Gi : C₄ ⥤ C₃} {Jb : C₁ ⥤ C₂} {Gb : C₂ ⥤ C₁}
    {Jk : C₀ ⥤ C₂} (ηi : 𝟭 C₃ ⟶ Ji ⋙ Gi) (ηb : 𝟭 C₁ ⟶ Jb ⋙ Gb) [IsIso ηb]
    (τh : Js ⟶ Rs) (τi : Rs ⟶ Js) (hτi : τi ≫ τh = 𝟙 Rs) (eJ : Js ⋙ Jb ≅ Jk) (eR : Rs ⋙ Rq ≅ Rr)
    (α : Rq ⋙ Ji ⟶ Jb ⋙ Rp) (χ : Rp ⋙ Gi ⟶ Gb ⋙ Rq)
    (hα : ∀ X, ηi.app (Rq.obj X) ≫ Gi.map (α.app X) ≫ χ.app (Jb.obj X) =
      Rq.map (ηb.app X))
    (γ : Rr ⋙ Ji ⟶ Jk ⋙ Rp) (lam : (Jk ⋙ Rp) ⋙ Gi ⟶ Rr)
    (hγ : ∀ M, γ.app M = Ji.map (eR.inv.app M) ≫ α.app (Rs.obj M) ≫
      Rp.map (Jb.map (τi.app M)) ≫ Rp.map (eJ.hom.app M))
    (hlam : ∀ M, lam.app M = χ.app (Jk.obj M) ≫ Rq.map (Gb.map (eJ.inv.app M)) ≫
      Rq.map (inv (ηb.app (Js.obj M))) ≫ Rq.map (τh.app M) ≫ eR.hom.app M)
    (M : C₀) :
    ηi.app (Rr.obj M) ≫ Gi.map (γ.app M) ≫ lam.app M = 𝟙 (Rr.obj M) := by
  have hi := congrArg (fun f ↦ f.app M) hτi
  dsimp only [NatTrans.comp_app, NatTrans.id_app] at hi
  rw [hγ, hlam]
  have hη := ηi.naturality (eR.inv.app M)
  have hχ := χ.naturality (eJ.hom.app M)
  have hτ := χ.naturality (Jb.map (τi.app M))
  have hb := ηb.naturality (τi.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at *
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hη, reassoc_of% hχ]
  simp only [← Rq.map_comp_assoc]
  rw [reassoc_of% hτ, reassoc_of% (hα (Rs.obj M))]
  rw [← Rq.map_comp_assoc, ← hb, Rq.map_comp]
  simp only [Category.assoc, ← Rq.map_comp_assoc]
  erw [← Gb.map_comp_assoc, eJ.hom_inv_id_app, Gb.map_id, Category.id_comp,
    IsIso.hom_inv_id_assoc, hi, Rq.map_id, Category.id_comp,
    eR.inv_hom_id_app]

private theorem adjunct_eq_of_unit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    {F : E ⥤ C} {H : E ⥤ D} (lam : H ⋙ R ≅ F) (γ : F ⋙ L ⟶ H)
    (h : ∀ M, a.unit.app (F.obj M) ≫ R.map (γ.app M) ≫ lam.hom.app M = 𝟙 _) :
    (((a.whiskerRight E).homEquiv _ _).symm lam.inv) = γ := by
  apply ((a.whiskerRight E).homEquiv _ _).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  ext M
  simp only [NatTrans.comp_app, Adjunction.whiskerRight_unit_app_app,
    Functor.whiskeringRight_obj_map, Functor.whiskerRight_app]
  apply (cancel_mono (lam.hom.app M)).1
  simpa only [Category.assoc] using (lam.inv_hom_id_app M).trans (h M).symm

variable (A : Type (u + 1)) [CommRing A]

/-- Restrict open extension along the open part of the fibre product. The inverse
open unit removes `G_b J_b`, after factoring `k = b s`.
Source: Stacks 09AE and the clopen factorization of 0F7B
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenRestrictedExtension {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    J A k ⋙ G A (pullback.fst p i) ≅ J A (squareLift k r p i h) :=
  Functor.isoWhiskerRight
    ((jComp A (squareLift k r p i h) (pullback.fst p i)) ≪≫
      jCongr A (pullback.lift_fst k r h)).symm (G A (pullback.fst p i)) ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft (J A (squareLift k r p i h))
    (@asIso _ _ _ _ (jAdj A (pullback.fst p i)).unit
      (jAdj_unit_isIso A (pullback.fst p i))).symm ≪≫
  Functor.rightUnitor _

/-- The actual open-restriction arrow: the cartesian inverse/direct-image mate,
restricted extension, the clopen open-to-direct-image map, and direct-image composition.
Source: Stacks 04J0, 07A7, 09AE and 0F7B, applied on the strict diagram site
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenRestrictionMap {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    (J A k ⋙ R A p) ⋙ G A i ⟶ R A r :=
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (J A k)
    (exchange A (pullback.fst p i) (pullback.snd p i) p i pullback.condition) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight (properOpenRestrictedExtension A k r p i h).hom
    (R A (pullback.snd p i)) ≫
  Functor.whiskerRight (openToR A (squareLift k r p i h)) (R A (pullback.snd p i)) ≫
  (rComp A (squareLift k r p i h) (pullback.snd p i)).hom ≫
  (eqToIso (congrArg (R A) (pullback.lift_snd k r h))).hom

/-- The open adjunct of the inverse restriction isomorphism, as a transformation on
the entire derived strict-tower category. No evaluation or arbitrary choice is used.
Source: Stacks 03DI and 07A7, blueprint open-adjunction normalization
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenOpenAdjunct {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i]
    (lam : (J A k ⋙ R A p) ⋙ G A i ≅ R A r) :
    R A r ⋙ J A i ⟶ J A k ⋙ R A p :=
  (((jAdj A i).whiskerRight (Derived A U)).homEquiv _ _).symm lam.inv

/-- In a cartesian square the restriction comparison is the square mate followed
by the inverse open unit, with the associators made explicit.
Source: Stacks 07A7 and the cartesian normalization in the blueprint
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenCartesianRestrictionMap {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] (h : k ≫ p = r ≫ i) :
    (J A k ⋙ R A p) ⋙ G A i ⟶ R A r :=
  (Functor.associator _ _ _).hom ≫
  Functor.whiskerLeft (J A k) (exchange A k r p i h) ≫
  (Functor.associator _ _ _).inv ≫
  Functor.whiskerRight
    (@asIso _ _ _ _ (jAdj A k).unit (jAdj_unit_isIso A k)).inv (R A r) ≫
  (Functor.leftUnitor _).hom

/-- Specialize the existing origin witness and scalar restriction to `A/I^(n+1)`.
This is just the dependent pair of the bounded-below finite-coefficient object, its
retained etale origin, and the specified scalar-restriction isomorphism.
Source: Stacks 099R and the displayed origin hypothesis in the blueprint
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenQuotientOrigin (I : Ideal A) [∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))]
    (U : Scheme.{u}) (N : Derived A U) (n : ℕ) : Type _ :=
  letI : TopologicalSpace (A ⧸ I ^ (n + 1)) := ⊥
  letI : DiscreteTopology (A ⧸ I ^ (n + 1)) := ⟨rfl⟩
  Σ F : FiniteCoefficientDerivedCategoryPlus U (A ⧸ I ^ (n + 1)),
    Σ _origin : EtaleOriginWitness U (A ⧸ I ^ (n + 1)) F,
      (finiteRestriction A U (A ⧸ I ^ (n + 1)) (Ideal.Quotient.mk _)).mapDerivedCategory.obj
        F.obj ≅ (ev A U n).obj N

/-- Use that very quotient origin in the existing finite evaluation comparisons.
Source: Stacks 099R and the blueprint's finite evaluation clause
(blueprint: lem-sp-proper-open-tower-comparison). -/
def properOpenScalarOrigin (I : Ideal A) [∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))]
    (U : Scheme.{u}) (N : Derived A U) (n : ℕ)
    (w : properOpenQuotientOrigin A I U N n) :
    ScalarEtaleOrigin A U ((ev A U n).obj N) :=
  letI : TopologicalSpace (A ⧸ I ^ (n + 1)) := ⊥
  letI : DiscreteTopology (A ⧸ I ^ (n + 1)) := ⟨rfl⟩
  { Λ := A ⧸ I ^ (n + 1)
    topology := inferInstance
    discrete := inferInstance
    φ := Ideal.Quotient.mk _
    F := w.1
    origin := w.2.1
    iso := w.2.2 }

attribute [local irreducible] G R J adj jAdj

-- With four adjunctions, the second mate is a conjugate and preserves invertibility.
private theorem exchange_isIso {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i]
    (h : k ≫ p = r ≫ i) (hsq : IsPullback k r p i) :
    IsIso (exchange A k r p i h) := by
  have hb := betaInv_isIso A r k i p h.symm hsq.flip
  have hs : mateEquiv (jAdj A i) (jAdj A k)
      (TwoSquare.mk _ _ _ _ (betaInv A r k i p h.symm)) =
        TwoSquare.mk _ _ _ _ (squareG A k r p i h).hom := by
    apply mateEquiv_eq_of_unit
    intro M
    change (G A r).map ((jAdj A i).unit.app M) ≫
        (squareG A k r p i h).hom.app ((J A i).obj M) =
      (jAdj A k).unit.app ((G A r).obj M) ≫
        (G A k).map (betaInvApp A r k i p h.symm M)
    have hh := ((jAdj A k).homEquiv _ _).apply_symm_apply
      ((G A r).map ((jAdj A i).unit.app M) ≫
        (squareG A r k i p h.symm).inv.app ((J A i).obj M))
    have hflip : (squareG A r k i p h.symm).inv = (squareG A k r p i h).hom := by
      simp only [squareG, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
        eqToIso.hom, eqToIso.inv, Category.assoc]
    rw [Adjunction.homEquiv_unit] at hh
    change (jAdj A k).unit.app ((G A r).obj M) ≫
        (G A k).map (betaInvApp A r k i p h.symm M) = _ at hh
    rw [hflip] at hh
    exact hh.symm
  have he : conjugateEquiv ((jAdj A i).comp (adj A p))
      ((adj A r).comp (jAdj A k)) (betaInv A r k i p h.symm) =
        exchange A k r p i h := by
    have hh := iterated_mateEquiv_conjugateEquiv (jAdj A i) (jAdj A k)
      (adj A r) (adj A p) (TwoSquare.mk _ _ _ _ (betaInv A r k i p h.symm))
    rw [hs] at hh
    exact hh.symm
  rw [← he]
  exact conjugateEquiv_iso _ _ _

-- The published direct-image compositor is conjugate to the inverse-image compositor.
private theorem rComp_transport {U V W : Scheme.{u}}
    (s : U ⟶ V) (q : V ⟶ W) (r : U ⟶ W) (h : s ≫ q = r) :
    conjugateIsoEquiv (adj A r) ((adj A q).comp (adj A s))
      ((gComp A s q).symm ≪≫ eqToIso (congrArg (G A) h)) =
        ((rComp A s q) ≪≫ eqToIso (congrArg (R A) h)).symm := by
  subst r
  simp only [eqToIso_refl, Iso.trans_refl]
  exact conjugateIsoEquiv_iso_symm _ _ _

-- Specialize pasting as an equality of squares before taking proper mates.
private theorem alpha_paste {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    let s := squareLift k r p i h
    let b := pullback.fst p i
    let q := pullback.snd p i
    let β := TwoSquare.mk (J A i) (G A q) (G A p) (J A b)
      (beta A q b i p pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom
    let δ := TwoSquare.mk (J A b) (G A s) (𝟭 (Derived A V)) (J A s ⋙ J A b)
      ((Functor.rightUnitor (J A b)).hom ≫ (Functor.leftUnitor (J A b)).inv ≫
        Functor.whiskerRight (pi A s) (J A b) ≫
        (Functor.associator (G A s) (J A s) (J A b)).hom)
    TwoSquare.mk (J A i) (G A r) (G A p) (J A k) (alpha A k r p i h) =
      (((TwoSquare.vComp β δ).whiskerRight (Functor.rightUnitor (G A p)).inv).whiskerLeft
        ((gComp A s q).symm ≪≫
          eqToIso (congrArg (G A) (pullback.lift_snd k r h))).hom).whiskerBottom
        ((jComp A s b) ≪≫ jCongr A (pullback.lift_fst k r h)).hom := by
  dsimp only
  exact paste_alpha
    ((gComp A (squareLift k r p i h) (pullback.snd p i)).symm ≪≫
      eqToIso (congrArg (G A) (pullback.lift_snd k r h)))
    ((jComp A (squareLift k r p i h) (pullback.fst p i)) ≪≫
      jCongr A (pullback.lift_fst k r h))
    (beta A (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm
      (IsPullback.of_hasPullback p i).flip).hom (pi A (squareLift k r p i h))

-- Normalize gamma at the natural-transformation level, before taking components.
private theorem gamma_def_eq {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    gamma A k r p i h = (mateEquiv (adj A r) (adj A p)
      (TwoSquare.mk _ _ _ _ (alpha A k r p i h))).natTrans := rfl

-- All substantive mate calculations occur in the abstract helper above.
private theorem gamma_factor {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived A U) :
    (gamma A k r p i h).app M =
      (J A i).map
          (((rComp A (squareLift k r p i h) (pullback.snd p i)) ≪≫
            eqToIso (congrArg (R A) (pullback.lift_snd k r h))).inv.app M) ≫
        (mateEquiv (adj A (pullback.snd p i)) (adj A p)
          (TwoSquare.mk _ _ _ _
            (beta A (pullback.snd p i) (pullback.fst p i) i p pullback.condition.symm
              (IsPullback.of_hasPullback p i).flip).hom)).natTrans.app
              ((R A (squareLift k r p i h)).obj M) ≫
        (R A p).map ((J A (pullback.fst p i)).map
          ((@inv _ _ _ _ (openToR A (squareLift k r p i h))
            (openToR_isIso A (squareLift k r p i h))).app M)) ≫
        (R A p).map (((jComp A (squareLift k r p i h) (pullback.fst p i)) ≪≫
          jCongr A (pullback.lift_fst k r h)).hom.app M) := by
  let s := squareLift k r p i h
  let b := pullback.fst p i
  let q := pullback.snd p i
  let β : TwoSquare (J A i) (G A q) (G A p) (J A b) :=
    TwoSquare.mk _ _ _ _ (beta A q b i p pullback.condition.symm
      (IsPullback.of_hasPullback p i).flip).hom
  exact mate_factor_unit (adj A q) (adj A s) (adj A p) (adj A r)
    ((gComp A s q).symm ≪≫ eqToIso (congrArg (G A) (pullback.lift_snd k r h)))
    ((rComp A s q) ≪≫ eqToIso (congrArg (R A) (pullback.lift_snd k r h)))
    ((jComp A s b) ≪≫ jCongr A (pullback.lift_fst k r h))
    (rComp_transport A s q r (pullback.lift_snd k r h)) β
    (@inv _ _ _ _ (openToR A s) (openToR_isIso A s))
    (pi A s) rfl
    (TwoSquare.mk _ _ _ _ (alpha A k r p i h)) (alpha_paste A k r p i h)
    (gamma A k r p i h) (gamma_def_eq A k r p i h) M

private theorem cartesian_gamma_unit {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i]
    (h : k ≫ p = r ≫ i) (hsq : IsPullback k r p i) (M : Derived A U) :
    (jAdj A i).unit.app ((R A r).obj M) ≫
        (G A i).map ((mateEquiv (adj A r) (adj A p)
          (TwoSquare.mk _ _ _ _ (beta A r k i p h.symm hsq.flip).hom)).natTrans.app M) ≫
        (exchange A k r p i h).app ((J A k).obj M) =
      (R A r).map ((jAdj A k).unit.app M) := by
  apply cartesian_unit
  intro N
  have hflip : (squareG A r k i p h.symm).inv = (squareG A k r p i h).hom := by
    simp only [squareG, Iso.trans_inv, Iso.trans_hom, Iso.symm_hom, Iso.symm_inv,
      eqToIso.hom, eqToIso.inv, Category.assoc]
  change betaInvApp A r k i p h.symm N = _
  rw [betaInvApp, Adjunction.homEquiv_counit, Functor.map_comp, hflip, Category.assoc]

-- Expand the specified restriction map once, independently of its unit normalization.
private theorem restriction_map_app {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived A U) :
    letI := jAdj_unit_isIso A (pullback.fst p i)
    (properOpenRestrictionMap A k r p i h).app M =
      (exchange A (pullback.fst p i) (pullback.snd p i) p i pullback.condition).app
          ((J A k).obj M) ≫
        (R A (pullback.snd p i)).map ((G A (pullback.fst p i)).map
          (((jComp A (squareLift k r p i h) (pullback.fst p i)) ≪≫
            jCongr A (pullback.lift_fst k r h)).inv.app M)) ≫
        (R A (pullback.snd p i)).map
          (inv ((jAdj A (pullback.fst p i)).unit.app ((J A (squareLift k r p i h)).obj M))) ≫
        (R A (pullback.snd p i)).map ((openToR A (squareLift k r p i h)).app M) ≫
        (((rComp A (squareLift k r p i h) (pullback.snd p i)) ≪≫
          eqToIso (congrArg (R A) (pullback.lift_snd k r h))).hom.app M) := by
  have := jAdj_unit_isIso A (pullback.fst p i)
  exact restriction_app (jAdj A (pullback.fst p i)) (openToR A (squareLift k r p i h))
    ((jComp A (squareLift k r p i h) (pullback.fst p i)) ≪≫
      jCongr A (pullback.lift_fst k r h))
    ((rComp A (squareLift k r p i h) (pullback.snd p i)) ≪≫
      eqToIso (congrArg (R A) (pullback.lift_snd k r h)))
    (exchange A (pullback.fst p i) (pullback.snd p i) p i pullback.condition)
    (properOpenRestrictedExtension A k r p i h) rfl
    (properOpenRestrictionMap A k r p i h) rfl M

-- Cancel the compositors and clopen comparison in the factorization of gamma.
-- Keep the scheme maps explicit here: aliases make kernel conversion unfold the pullback.
private theorem restriction_unit {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (M : Derived A U) :
    (jAdj A i).unit.app ((R A r).obj M) ≫
        (G A i).map ((gamma A k r p i h).app M) ≫
        (properOpenRestrictionMap A k r p i h).app M = 𝟙 ((R A r).obj M) := by
  have := openToR_isIso A (squareLift k r p i h)
  have := jAdj_unit_isIso A (pullback.fst p i)
  exact factor_unit
    (C₀ := Derived A U) (C₁ := Derived A (pullback p i)) (C₂ := Derived A V)
    (C₃ := Derived A W) (C₄ := Derived A Z)
    (Rs := R A (squareLift k r p i h)) (Js := J A (squareLift k r p i h))
    (Rq := R A (pullback.snd p i)) (Rp := R A p) (Rr := R A r)
    (Ji := J A i) (Gi := G A i) (Jb := J A (pullback.fst p i))
    (Gb := G A (pullback.fst p i)) (Jk := J A k)
    (jAdj A i).unit (jAdj A (pullback.fst p i)).unit
    (openToR A (squareLift k r p i h)) (inv (openToR A (squareLift k r p i h)))
    (IsIso.inv_hom_id (openToR A (squareLift k r p i h)))
    ((jComp A (squareLift k r p i h) (pullback.fst p i)) ≪≫
      jCongr A (pullback.lift_fst k r h))
    ((rComp A (squareLift k r p i h) (pullback.snd p i)) ≪≫
      eqToIso (congrArg (R A) (pullback.lift_snd k r h)))
    (mateEquiv (adj A (pullback.snd p i)) (adj A p)
      (TwoSquare.mk _ _ _ _ (beta A (pullback.snd p i) (pullback.fst p i) i p
        pullback.condition.symm (IsPullback.of_hasPullback p i).flip).hom)).natTrans
    (exchange A (pullback.fst p i) (pullback.snd p i) p i pullback.condition)
    (fun X ↦ cartesian_gamma_unit A (pullback.fst p i) (pullback.snd p i) p i
      pullback.condition (IsPullback.of_hasPullback p i) X)
    (gamma A k r p i h) (properOpenRestrictionMap A k r p i h)
    (fun X ↦ gamma_factor A k r p i h X)
    (fun X ↦ restriction_map_app A k r p i h X) M

private theorem restriction_isIso {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) :
    IsIso (properOpenRestrictionMap A k r p i h) := by
  have := exchange_isIso A (pullback.fst p i) (pullback.snd p i) p i
    pullback.condition (IsPullback.of_hasPullback p i)
  have := openToR_isIso A (squareLift k r p i h)
  unfold properOpenRestrictionMap
  infer_instance

-- Both restriction maps satisfy the same unit equation; cancel its invertible prefix.
private theorem restriction_cartesian {U V W Z : Scheme.{u}}
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [QuasiCompact k] [QuasiCompact i]
    [IsProper r] [IsProper p] (h : k ≫ p = r ≫ i) (hsq : IsPullback k r p i) :
    properOpenRestrictionMap A k r p i h = properOpenCartesianRestrictionMap A k r p i h := by
  have := restriction_isIso A k r p i h
  have := jAdj_unit_isIso A k
  let lam := asIso (properOpenRestrictionMap A k r p i h)
  ext M
  have hu := restriction_unit A k r p i h M
  have he : (jAdj A i).unit.app ((R A r).obj M) ≫
      (G A i).map ((gamma A k r p i h).app M) = lam.inv.app M := by
    apply (cancel_mono (lam.hom.app M)).1
    rw [lam.inv_hom_id_app]
    simpa only [Category.assoc, lam, asIso_hom] using hu
  have hv := cartesian_gamma_unit A k r p i h hsq M
  have hg : gamma A k r p i h =
      (mateEquiv (adj A r) (adj A p)
        (TwoSquare.mk _ _ _ _ (beta A r k i p h.symm hsq.flip).hom)).natTrans := by
    rw [gamma, alpha_cartesian A k r p i h hsq]
  rw [← hg] at hv
  have hv' : (jAdj A i).unit.app ((R A r).obj M) ≫
      (G A i).map ((gamma A k r p i h).app M) ≫
        (properOpenCartesianRestrictionMap A k r p i h).app M = 𝟙 ((R A r).obj M) := by
    simp only [properOpenCartesianRestrictionMap, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Category.id_comp]
    erw [Category.comp_id]
    rw [reassoc_of% hv]
    erw [← Functor.map_comp, NatIso.isIso_inv_app, IsIso.hom_inv_id]
    exact (R A r).map_id M
  apply (cancel_epi (lam.inv.app M)).1
  rw [← he]
  simpa only [Category.assoc, lam, asIso_hom] using hu.trans hv'.symm

/-- The unique canonical restriction isomorphism and its open adjunct, with the finite
evaluation normalization. The equation with the open unit is the typed form of
`λ G_i Γ = 1` under `G_i J_i ≅ 1`. The equality with `gamma` identifies actual natural
transformations before evaluation, including noncartesian squares.

Source: Stacks 0F7B and 0F7F with 0941; the strict-tower enhancement and its open
normalization are agent assertions, as explicitly recorded in the DAG source
(blueprint: lem-sp-proper-open-tower-comparison).

Proof, following the five DAG steps:
1. Use the published strict constant-coefficient operations with B=A and n indexing
   positive level n+1. Weakly-etale localization and localizedModuleExactIndependent
   identify moduleJ with the prescribed sheafified extension presheaf: maps to the
   open are unique when they exist, so its direct sum is the stated module or zero.
   This preserves the open units and gives the same exact tower and derived adjunctions.
   Noetherian schemes make the open immersions quasi-compact. The strict-tower calculus
   supplies the clopen lift s into V times_Z W, with b s=k and q s=r.
2. Split every test object over the clopen image of s and its complement. Sheaf gluing
   identifies modules, transitions and differentials with pairs. Both J_s and s_* are
   F mapped to (F,0); openToR is identity on the first factor and zero on the other.
   Thus it is invertible and the direct-image unit is the clopen projection pi.
   The unit-normalized open compositor gives properOpenRestrictedExtension.
3. On the ringed diagram site choose a K-injective resolution. Restriction G_b
   preserves K-injectives because it is right adjoint to exact J_b. Localization of
   the ringed-site morphism identifies both restricted direct images with q_*G_b
   of that same resolution, by identity on sections. This is precisely exchange.
   Compose with step 2 and the normalized direct-image compositor to obtain the
   displayed properOpenRestrictionMap, an isomorphism. For a cartesian square the
   clopen lift is an isomorphism and this is the square mate followed by the open unit.
4. Compute the open transpose of the existing proper mate gamma. The square-mate
   unit equation cancels the p adjunction unit; the restriction of beta is the open
   identity. Naturality moves the r counit past the restriction comparison. What
   remains is R_q J_s epsilon_r composed with R_q pi_s G_q R_r and eta_q R_r.
   Since pi_s=eta_s under J_s=R_s, the composite-unit formula and the r triangle
   identity make this the identity of R_r. The open Hom bijection therefore identifies
   gamma with properOpenOpenAdjunct, as transformations on derived strict towers.
5. Apply gamma_isIso and gamma_evaluation to the specified quotient origins, using
   finiteGamma from properOpenInterchangeCoherence and the canonical finiteSource
   and finiteTarget comparisons. Each origin has its own lower bound; the strict
   transitions belong to N and no transitions between etale origins are required.
   Substitute step 4 before evaluating; no faithfulness of evaluation is invoked.
   Uniqueness of lambda follows because its hom is the specified restriction map. -/
theorem properOpenTowerComparison [IsNoetherianRing A]
    (I : Ideal A) [∀ n : ℕ, Finite (A ⧸ I ^ (n + 1))]
    {U V W Z : Scheme.{u}} [IsNoetherian U] [IsNoetherian V]
    [IsNoetherian W] [IsNoetherian Z]
    (k : U ⟶ V) (r : U ⟶ W) (p : V ⟶ Z) (i : W ⟶ Z)
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (h : k ≫ p = r ≫ i) :
    ∃! lam : (J A k ⋙ R A p) ⋙ G A i ≅ R A r,
      lam.hom = properOpenRestrictionMap A k r p i h ∧
      (IsPullback k r p i → lam.hom = properOpenCartesianRestrictionMap A k r p i h) ∧
      properOpenOpenAdjunct A k r p i lam = gamma A k r p i h ∧
      (∀ M : Derived A U,
        (jAdj A i).unit.app ((R A r).obj M) ≫
            (G A i).map ((properOpenOpenAdjunct A k r p i lam).app M) ≫ lam.hom.app M =
          𝟙 ((R A r).obj M)) ∧
      ∀ (N : Derived A U) (w : ∀ n : ℕ, properOpenQuotientOrigin A I U N n),
        IsIso ((properOpenOpenAdjunct A k r p i lam).app N) ∧
        ∀ n : ℕ,
          (finiteSource A r i N n (properOpenScalarOrigin A I U N n (w n))).hom ≫
              (ev A Z n).map ((properOpenOpenAdjunct A k r p i lam).app N) =
            (HD A Z (properOpenScalarOrigin A I U N n (w n)).Λ
                (properOpenScalarOrigin A I U N n (w n)).φ).map
                ((finiteGamma (properOpenScalarOrigin A I U N n (w n)).Λ k r p i h).hom.app
                  (properOpenScalarOrigin A I U N n (w n)).origin.L) ≫
              (finiteTarget A k p N n (properOpenScalarOrigin A I U N n (w n))).hom := by
  have := restriction_isIso A k r p i h
  let lam := asIso (properOpenRestrictionMap A k r p i h)
  have heq : properOpenOpenAdjunct A k r p i lam = gamma A k r p i h :=
    adjunct_eq_of_unit (jAdj A i) lam (gamma A k r p i h)
      (restriction_unit A k r p i h)
  refine ⟨lam, ⟨rfl, ?_, heq, ?_, ?_⟩, ?_⟩
  · intro hsq
    exact restriction_cartesian A k r p i h hsq
  · intro M
    rw [heq]
    exact restriction_unit A k r p i h M
  · intro N w
    constructor
    · rw [heq]
      exact gamma_isIso A k r p i h N
        (fun n ↦ ⟨properOpenScalarOrigin A I U N n (w n)⟩)
    · intro n
      exact (congrArg (fun f ↦
        (finiteSource A r i N n (properOpenScalarOrigin A I U N n (w n))).hom ≫
          (ev A Z n).map (f.app N)) heq).trans
            (gamma_evaluation A k r p i h N n (properOpenScalarOrigin A I U N n (w n)))
  · intro μ hμ
    apply Iso.ext
    exact hμ.1


end AlgebraicGeometry.ProEtale.StrictTower
