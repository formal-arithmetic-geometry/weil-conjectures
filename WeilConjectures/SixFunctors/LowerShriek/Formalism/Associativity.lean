/-
Copyright (c) 2026 Weil conjectures project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weil conjectures project
-/
module

public import WeilConjectures.Compactification.Tower
public import WeilConjectures.SixFunctors.LowerShriek.Formalism.Canonical

/-!
# Associativity of the composition isomorphism in a compact support formalism

For a tower of compactifications `𝒯` of composable morphisms `f`, `g`, `h`
(`AlgebraicGeometry.Compactification.Tower`), the two composites
`Rf_! ⋙ Rg_! ⋙ Rh_! ≅ R(f ≫ g ≫ h)_!` built from the composition isomorphisms of the four
triangles of `𝒯` agree (`compIso_tower`): this is a pasting identity for the exchange maps of
the squares of the tower. Combined with the independence of the triangles, it gives the
associativity of the canonical composition isomorphism `F.lowerShriekCompIso`
(`lowerShriekCompIso_assoc`, blueprint `sk-thm-sf-comp-composition`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits TwoSquare

namespace AlgebraicGeometry.CompactSupportFormalism

variable (F : CompactSupportFormalism.{w, v, u}) [F.HasProperExchange]

variable {X Y S T : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S} {h : S ⟶ T}

/-- **The pasting identity of a tower of compactifications**: the two composites of the
composition isomorphisms of the four triangles of a tower agree. -/
theorem compIso_tower (𝒯 : Compactification.Tower f g h) :
    Functor.whiskerRight (F.compIso 𝒯.fg).hom (F.shriek 𝒯.ch) ≫ (F.compIso 𝒯.fg_h).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (F.shriek 𝒯.cf) (F.compIso 𝒯.gh).hom ≫ (F.compIso 𝒯.f_gh).hom := by
  have := HasBaseChange.isIso_baseChange (F := F) 𝒯.isPullback_fg
  have := HasBaseChange.isIso_baseChange (F := F) 𝒯.isPullback_gh
  have := HasBaseChange.isIso_baseChange (F := F) 𝒯.isPullback_mid
  have : IsIso (F.baseChange 𝒯.cf.g (𝒯.q ≫ 𝒯.q') 𝒯.cgh.i 𝒯.p₁ 𝒯.f_gh.isPullback.w).natTrans :=
    HasBaseChange.isIso_baseChange (F := F) 𝒯.f_gh.isPullback
  have : IsIso (F.baseChange 𝒯.cfg.g 𝒯.q' 𝒯.ch.i (𝒯.p₁ ≫ 𝒯.p₂) 𝒯.fg_h.isPullback.w).natTrans :=
    HasBaseChange.isIso_baseChange (F := F) 𝒯.fg_h.isPullback
  ext K
  have hV := congr_app (F.exchange_paste_vert 𝒯.cf.g 𝒯.p 𝒯.p₁ 𝒯.q 𝒯.cg.i 𝒯.q' 𝒯.q₂
    (𝒯.q ≫ 𝒯.q') 𝒯.cgh.i 𝒯.isPullback_fg.w 𝒯.isPullback_mid.w rfl 𝒯.i_q₂
    𝒯.f_gh.isPullback.w) ((F.sh 𝒯.cf.i).obj K)
  have hH := congr_app (F.exchange_paste_horiz 𝒯.p 𝒯.cg.g 𝒯.q' 𝒯.q₂ 𝒯.ch.i 𝒯.p₁ 𝒯.p₂
    𝒯.cfg.g (𝒯.p₁ ≫ 𝒯.p₂) 𝒯.isPullback_mid.w 𝒯.isPullback_gh.w 𝒯.p_g rfl
    𝒯.fg_h.isPullback.w) ((F.sh 𝒯.cfg.i).obj K)
  simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.hComp, TwoSquare.vComp, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id, Functor.comp_obj]
    at hV hH
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, compIso_hom_app]
  dsimp only [shriek, Functor.comp_obj, Functor.comp_map, Compactification.copy_i,
    Compactification.copy_g]
  have hPC := F.pfComp'_assoc_inv_app 𝒯.p₁ 𝒯.p₂ 𝒯.ch.g (𝒯.p₁ ≫ 𝒯.p₂) 𝒯.cgh.g 𝒯.cfgh.g rfl 𝒯.p₂_g
    𝒯.fg_h.p_g 𝒯.p₁_g ((F.sh 𝒯.cfgh.i).obj K)
  have hSC := F.shComp'_assoc_inv_app 𝒯.cf.i 𝒯.q 𝒯.q' 𝒯.cfg.i (𝒯.q ≫ 𝒯.q') 𝒯.cfgh.i 𝒯.i_q rfl
    𝒯.i_q' 𝒯.f_gh.i_q K
  -- naturality
  have hεgh := (F.exchange 𝒯.cg.g 𝒯.q₂ 𝒯.ch.i 𝒯.p₂ 𝒯.isPullback_gh.w).natTrans.naturality
    ((F.exchange 𝒯.cf.g 𝒯.q 𝒯.cg.i 𝒯.p 𝒯.isPullback_fg.w).natTrans.app ((F.sh 𝒯.cf.i).obj K) ≫
      (F.pf 𝒯.p).map ((F.shComp' 𝒯.cf.i 𝒯.q 𝒯.cfg.i 𝒯.i_q).inv.app K))
  have hεR := (F.exchange 𝒯.p 𝒯.q' 𝒯.q₂ 𝒯.p₁ 𝒯.isPullback_mid.w).natTrans.naturality
    ((F.shComp' 𝒯.cf.i 𝒯.q 𝒯.cfg.i 𝒯.i_q).inv.app K)
  have hP := (F.pfComp' 𝒯.p₁ 𝒯.p₂ (𝒯.p₁ ≫ 𝒯.p₂) rfl).inv.naturality
    ((F.shComp' 𝒯.cfg.i 𝒯.q' 𝒯.cfgh.i 𝒯.i_q').inv.app K)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.map_comp, Category.assoc] at hεgh hεR hP
  simp only [Category.assoc]
  rw [← NatTrans.naturality_assoc, hPC, ← Functor.map_comp_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp_assoc]
  refine congrArg (· ≫ _) (congrArg (F.pf 𝒯.ch.g).map ?_)
  rw [hH, hV]
  have hεR' := congrArg (F.pf 𝒯.p₂).map hεR
  have hSC' := congrArg (fun x ↦ (F.pf 𝒯.p₂).map ((F.pf 𝒯.p₁).map x)) hSC
  simp only [Functor.map_comp] at hεR' hSC'
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (F.sh 𝒯.ch.i) ((F.pfComp' 𝒯.p 𝒯.cg.g 𝒯.cfg.g 𝒯.p_g).inv.app _),
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% hεgh, reassoc_of% hεR']
  erw [← hP]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app_assoc, hSC]

end AlgebraicGeometry.CompactSupportFormalism
