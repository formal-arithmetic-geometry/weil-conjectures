/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.FrobeniusPowerCommutation
public import WeilConjectures.WeilSheaf.StalkFrobenius
import WeilConjectures.WeilSheaf.BaseChangeField.Coherence
import WeilConjectures.DeligneLaumon.FrobeniusPowerCompositionGeometry

/-! # The single-return square for a power translate

Source: the geometric orbit argument in `sk-i-dl-general-real`, step 2 of
`lem-zl-frobenius-power-stalk-transport`.
(blueprint: lem-zl-frobenius-power-translate-structure).
-/

@[expose] public section
set_option autoImplicit false
universe u v w

open CategoryTheory Limits Endofunctor

namespace AlgebraicGeometry.WeilSheaf
open ProEtale

private theorem forget_map {l : ℕ} [Fact l.Prime] {S : Scheme.{u}}
    {M N : AdicSheaf l S} (f : M ⟶ N) :
    (AdicSheaf.forget S).map f = f.hom := rfl

private theorem pairIso_hom_inv {S : Scheme.{u}} (a b : S ≅ S) :
    (a.hom ≫ b.hom) ≫ (b.inv ≫ a.inv) = 𝟙 S := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id]

private theorem pairIso_inv_hom {S : Scheme.{u}} (a b : S ≅ S) :
    (b.inv ≫ a.inv) ≫ (a.hom ≫ b.hom) = 𝟙 S := by
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

private abbrev pairIso {S : Scheme.{u}} (a b : S ≅ S) : S ≅ S where
  hom := a.hom ≫ b.hom
  inv := b.inv ≫ a.inv
  hom_inv_id := pairIso_hom_inv a b
  inv_hom_id := pairIso_inv_hom a b

private theorem intertwiner_square {D : Type v} [Category.{w} D]
    (F B L R : D ⥤ D) (ua : F ≅ L) (ub : B ≅ R) (M N : D)
    {Z K J : D} (x : Z ⟶ F.obj (B.obj M)) (y₁ : Z ⟶ J)
    (y₂ : J ⟶ B.obj (F.obj M)) (w₀ : Z ⟶ K)
    (c₁ : K ⟶ L.obj (R.obj M)) (c₂ : K ⟶ R.obj (L.obj M))
    (t : L.obj (R.obj M) ⟶ R.obj (L.obj M))
    (φ : L.obj M ⟶ M) (ψ : L.obj N ⟶ N) (c : R.obj M ⟶ N)
    (hL : x ≫ F.map (ub.hom.app M) ≫ ua.hom.app (R.obj M) = w₀ ≫ c₁)
    (hR : y₁ ≫ y₂ ≫ B.map (ua.hom.app M) ≫ ub.hom.app (L.obj M) = w₀ ≫ c₂)
    (hC : c₁ ≫ t = c₂) (h : L.map c ≫ ψ = t ≫ R.map φ ≫ c) :
    x ≫ F.map (ub.hom.app M ≫ c) ≫ ua.hom.app N ≫ ψ =
      y₁ ≫ y₂ ≫ B.map (ua.hom.app M ≫ φ) ≫ ub.hom.app M ≫ c := by
  simp only [Functor.map_comp, Category.assoc]
  rw [ua.hom.naturality_assoc, reassoc_of% hL, h, reassoc_of% hC,
    ub.hom.naturality_assoc, reassoc_of% hR]

private theorem lower_factor_hom_app
    (D : Type v) [Category.{u + 1} D] {S T U : Scheme.{u}}
    {a : S ⟶ U} {b : S ⟶ T} {c : T ⟶ U} (h : b ≫ c = a)
    (M : Sheaf (Scheme.ProEt.topology S) D) :
    (lowerStarFactor D h).hom.app M =
      (lowerStarComp D b c).hom.app M ≫ (lowerStarCongr D h).hom.app M := by
  rw [← lowerStarComp_trans_lowerStarCongr D h, Iso.trans_hom, NatTrans.comp_app]

private theorem upper_square_factor
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {S : Scheme.{u}}
    (a b E : S ≅ S)
    (hE : a.hom ≫ b.hom = E.hom) (hi : b.inv ≫ a.inv = E.inv)
    (hR : b.hom ≫ a.hom = E.hom) (hRi : a.inv ≫ b.inv = E.inv)
    (M N : Sheaf (Scheme.ProEt.topology S) D)
    (φ : (a.inv)_*[D].obj M ⟶ M) (ψ : (a.inv)_*[D].obj N ⟶ N)
    (c : (b.inv)_*[D].obj M ⟶ N)
    (h : (a.inv)_*[D].map c ≫ ψ =
      (lowerStarFactor D hi).hom.app M ≫ (lowerStarFactor D hRi).inv.app M ≫
        (b.inv)_*[D].map φ ≫ c) :
    (upperStarFactor D hE).hom.app M ≫
      (a.hom)^*[D].map ((upperStarIsoLowerStarInv D b).hom.app M ≫ c) ≫
      (upperStarIsoLowerStarInv D a).hom.app N ≫ ψ =
    (upperStarFactor D hR).hom.app M ≫
      (b.hom)^*[D].map ((upperStarIsoLowerStarInv D a).hom.app M ≫ φ) ≫
      (upperStarIsoLowerStarInv D b).hom.app M ≫ c := by
  have L := (upperStarIsoLowerStarInv_hom_app_trans D a b E hE hi M).symm
  have R := (upperStarIsoLowerStarInv_hom_app_trans D b a E hR hRi M).symm
  have H := intertwiner_square (a.hom)^*[D] (b.hom)^*[D]
    (a.inv)_*[D] (b.inv)_*[D]
    (upperStarIsoLowerStarInv D a) (upperStarIsoLowerStarInv D b) M N
    ((upperStarFactor D hE).hom.app M)
    (𝟙 _) ((upperStarFactor D hR).hom.app M)
    ((upperStarIsoLowerStarInv D E).hom.app M)
    ((lowerStarFactor D hi).inv.app M) ((lowerStarFactor D hRi).inv.app M)
    ((lowerStarFactor D hi).hom.app M ≫ (lowerStarFactor D hRi).inv.app M)
    φ ψ c L (by simpa only [Category.id_comp] using R)
    (by simp only [Iso.inv_hom_id_app_assoc]) (by simpa only [Category.assoc] using h)
  simpa only [Category.id_comp] using H

private theorem upper_factor_prefix_iso
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {S : Scheme.{u}}
    {a b c d e : S ⟶ S} (h : b ≫ c = a) (h' : d ≫ e = a)
    (hc : b ≫ c = d ≫ e) :
    upperStarCongr D h ≪≫ upperStarFactor D h' =
      upperStarCongr D hc ≪≫ upperStarComp D d e := by
  change upperStarCongr D h ≪≫
      (upperStarCongr D h'.symm ≪≫ upperStarComp D d e) = _
  rw [← Iso.trans_assoc, upperStarCongr_trans]

private theorem upper_factor_self_iso
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {S : Scheme.{u}}
    {a b c : S ⟶ S} (h : b ≫ c = a) :
    upperStarCongr D h ≪≫ upperStarFactor D h = upperStarComp D b c := by
  have H := upper_factor_prefix_iso D h h rfl
  simpa only [upperStarCongr, eqToIso_refl, Iso.refl_trans] using H

private theorem lower_factor_compare
    (D : Type v) [Category.{u + 1} D] {S : Scheme.{u}}
    {a b c d e : S ⟶ S} (h : b ≫ c = a) (h' : d ≫ e = a)
    (hc : b ≫ c = d ≫ e) (M : Sheaf (Scheme.ProEt.topology S) D) :
    (lowerStarFactor D h).hom.app M ≫ (lowerStarFactor D h').inv.app M =
      (lowerStarFactor D hc).hom.app M ≫ (lowerStarComp D d e).inv.app M := by
  subst a
  rw [lowerStarFactor_rfl,
    ← lowerStarCongr_hom_app_comp_lowerStarComp_inv_app D hc M,
    ← Category.assoc, ← lower_factor_hom_app D hc M]

private theorem change_prefix_pair {D : Type v} [Category.{w} D]
    {A B C E Z : D} (x : A ⟶ Z) (u : A ⟶ B) (v : B ⟶ E)
    (u' : A ⟶ C) (v' : C ⟶ E) (w : E ⟶ Z)
    (hp : u ≫ v = u' ≫ v') (h : x = u' ≫ v' ≫ w) : x = u ≫ v ≫ w := by
  rw [← Category.assoc, ← hp, Category.assoc] at h
  exact h

private theorem lower_equivariance_repackage
    (D : Type v) [Category.{u + 1} D] {S : Scheme.{u}}
    (a b E : S ≅ S) (hi : b.inv ≫ a.inv = E.inv)
    (hci : b.inv ≫ a.inv = a.inv ≫ b.inv)
    (M N : Sheaf (Scheme.ProEt.topology S) D)
    (φ : (a.inv)_*[D].obj M ⟶ M) (ψ : (a.inv)_*[D].obj N ⟶ N)
    (c : (b.inv)_*[D].obj M ⟶ N)
    (h : (a.inv)_*[D].map c ≫ ψ =
      (lowerStarFactor D hci).hom.app M ≫
        (lowerStarComp D a.inv b.inv).inv.app M ≫ (b.inv)_*[D].map φ ≫ c) :
    (a.inv)_*[D].map c ≫ ψ =
      (lowerStarFactor D hi).hom.app M ≫
        (lowerStarFactor D (hci.symm.trans hi)).inv.app M ≫
          (b.inv)_*[D].map φ ≫ c := by
  exact change_prefix_pair ((a.inv)_*[D].map c ≫ ψ)
    ((lowerStarFactor D hi).hom.app M)
    ((lowerStarFactor D (hci.symm.trans hi)).inv.app M)
    ((lowerStarFactor D hci).hom.app M) ((lowerStarComp D a.inv b.inv).inv.app M)
    ((b.inv)_*[D].map φ ≫ c)
    (lower_factor_compare D hi (hci.symm.trans hi) hci M) h

private theorem upper_path_square
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {S : Scheme.{u}}
    (a b E : S ≅ S) (hE : a.hom ≫ b.hom = E.hom)
    (hc : a.hom ≫ b.hom = b.hom ≫ a.hom)
    (M N : Sheaf (Scheme.ProEt.topology S) D)
    (p : ((b.hom)^*[D] ⋙ (a.hom)^*[D]).obj M ⟶ N)
    (q : ((a.hom)^*[D] ⋙ (b.hom)^*[D]).obj M ⟶ N)
    (HP : upperStarCongr D hE ≪≫ upperStarFactor D hE = upperStarComp D a.hom b.hom)
    (HQ : upperStarCongr D hE ≪≫ upperStarFactor D (hc.symm.trans hE) =
      upperStarCongr D hc ≪≫ upperStarComp D b.hom a.hom)
    (H : (upperStarFactor D hE).hom.app M ≫ p =
      (upperStarFactor D (hc.symm.trans hE)).hom.app M ≫ q) :
    (upperStarComp D a.hom b.hom).hom.app M ≫ p =
      (upperStarCongr D hc).hom.app M ≫ (upperStarComp D b.hom a.hom).hom.app M ≫ q := by
  have h := congrArg (fun t ↦ (upperStarCongr D hE).hom.app M ≫ t) H
  have HP' := congrArg (fun I ↦ I.hom.app M) HP
  have HQ' := congrArg (fun I ↦ I.hom.app M) HQ
  simp only [Iso.trans_hom, NatTrans.comp_app] at HP' HQ'
  rw [← Category.assoc, HP', ← Category.assoc, HQ', Category.assoc] at h
  exact h

private theorem upper_square_core
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {S : Scheme.{u}}
    (a b E : S ≅ S) (hE : a.hom ≫ b.hom = E.hom)
    (hc : a.hom ≫ b.hom = b.hom ≫ a.hom)
    (M N : Sheaf (Scheme.ProEt.topology S) D)
    (φ : (a.inv)_*[D].obj M ⟶ M) (ψ : (a.inv)_*[D].obj N ⟶ N)
    (c : (b.inv)_*[D].obj M ⟶ N)
    (HP : upperStarCongr D hE ≪≫ upperStarFactor D hE = upperStarComp D a.hom b.hom)
    (HQ : upperStarCongr D hE ≪≫ upperStarFactor D (hc.symm.trans hE) =
      upperStarCongr D hc ≪≫ upperStarComp D b.hom a.hom)
    (H : (upperStarFactor D hE).hom.app M ≫
      (a.hom)^*[D].map ((upperStarIsoLowerStarInv D b).hom.app M ≫ c) ≫
      (upperStarIsoLowerStarInv D a).hom.app N ≫ ψ =
    (upperStarFactor D (hc.symm.trans hE)).hom.app M ≫
      (b.hom)^*[D].map ((upperStarIsoLowerStarInv D a).hom.app M ≫ φ) ≫
      (upperStarIsoLowerStarInv D b).hom.app M ≫ c) :
    (upperStarComp D a.hom b.hom).hom.app M ≫
      (a.hom)^*[D].map
        ((upperStarIsoLowerStarInv D b).hom.app M ≫ c) ≫
      (upperStarIsoLowerStarInv D a).hom.app N ≫ ψ =
    (upperStarCongr D hc).hom.app M ≫
      (upperStarComp D b.hom a.hom).hom.app M ≫
      (b.hom)^*[D].map
        ((upperStarIsoLowerStarInv D a).hom.app M ≫ φ) ≫
      (upperStarIsoLowerStarInv D b).hom.app M ≫ c := by
  exact upper_path_square D a b E hE hc M N
    ((a.hom)^*[D].map ((upperStarIsoLowerStarInv D b).hom.app M ≫ c) ≫
      (upperStarIsoLowerStarInv D a).hom.app N ≫ ψ)
    ((b.hom)^*[D].map ((upperStarIsoLowerStarInv D a).hom.app M ≫ φ) ≫
      (upperStarIsoLowerStarInv D b).hom.app M ≫ c) HP HQ H

private theorem upper_square_with_composite
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {S : Scheme.{u}}
    (a b E : S ≅ S)
    (hE : a.hom ≫ b.hom = E.hom) (hi : b.inv ≫ a.inv = E.inv)
    (hc : a.hom ≫ b.hom = b.hom ≫ a.hom)
    (hci : b.inv ≫ a.inv = a.inv ≫ b.inv)
    (M N : Sheaf (Scheme.ProEt.topology S) D)
    (φ : (a.inv)_*[D].obj M ⟶ M)
    (ψ : (a.inv)_*[D].obj N ⟶ N)
    (c : (b.inv)_*[D].obj M ⟶ N)
    (h : (a.inv)_*[D].map c ≫ ψ =
      (lowerStarFactor D hci).hom.app M ≫
        (lowerStarComp D a.inv b.inv).inv.app M ≫
        (b.inv)_*[D].map φ ≫ c) :
    (upperStarComp D a.hom b.hom).hom.app M ≫
      (a.hom)^*[D].map
        ((upperStarIsoLowerStarInv D b).hom.app M ≫ c) ≫
      (upperStarIsoLowerStarInv D a).hom.app N ≫ ψ =
    (upperStarCongr D hc).hom.app M ≫
      (upperStarComp D b.hom a.hom).hom.app M ≫
      (b.hom)^*[D].map
        ((upperStarIsoLowerStarInv D a).hom.app M ≫ φ) ≫
      (upperStarIsoLowerStarInv D b).hom.app M ≫ c := by
  have h' := lower_equivariance_repackage D a b E hi hci M N φ ψ c h
  have H := upper_square_factor D a b E hE hi
    (hc.symm.trans hE) (hci.symm.trans hi) M N φ ψ c h'
  have HP := upper_factor_self_iso D hE
  have HQ := upper_factor_prefix_iso D hE (hc.symm.trans hE) hc
  exact upper_square_core D a b E hE hc M N φ ψ c HP HQ H

private theorem upper_square_of_lower_concrete
    (D : Type v) [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] {S : Scheme.{u}}
    (a b : S ≅ S)
    (hc : a.hom ≫ b.hom = b.hom ≫ a.hom)
    (hci : b.inv ≫ a.inv = a.inv ≫ b.inv)
    (M N : Sheaf (Scheme.ProEt.topology S) D)
    (φ : (a.inv)_*[D].obj M ⟶ M)
    (ψ : (a.inv)_*[D].obj N ⟶ N)
    (c : (b.inv)_*[D].obj M ⟶ N)
    (h : (a.inv)_*[D].map c ≫ ψ =
      (lowerStarFactor D hci).hom.app M ≫
        (lowerStarComp D a.inv b.inv).inv.app M ≫
        (b.inv)_*[D].map φ ≫ c) :
    (upperStarComp D a.hom b.hom).hom.app M ≫
      (a.hom)^*[D].map
        ((upperStarIsoLowerStarInv D b).hom.app M ≫ c) ≫
      (upperStarIsoLowerStarInv D a).hom.app N ≫ ψ =
    (upperStarCongr D hc).hom.app M ≫
      (upperStarComp D b.hom a.hom).hom.app M ≫
      (b.hom)^*[D].map
        ((upperStarIsoLowerStarInv D a).hom.app M ≫ φ) ≫
      (upperStarIsoLowerStarInv D b).hom.app M ≫ c := by
  exact upper_square_with_composite D a b (pairIso a b) rfl rfl hc hci M N φ ψ c h

private theorem upper_square_of_adic_lower
    {l : ℕ} [Fact l.Prime] {S : Scheme.{u}} (a b : S ≅ S)
    (hc : a.hom ≫ b.hom = b.hom ≫ a.hom)
    (hci : b.inv ≫ a.inv = a.inv ≫ b.inv)
    (M N : AdicSheaf l S) (φ : (a.inv)_*ᵃ[l].obj M ⟶ M)
    (ψ : (a.inv)_*ᵃ[l].obj N ⟶ N) (c : (b.inv)_*ᵃ[l].obj M ⟶ N)
    (h : (a.inv)_*ᵃ[l].map c ≫ ψ =
      (adicLowerStarSquareIso l hci).hom.app M ≫ (b.inv)_*ᵃ[l].map φ ≫ c) :
    (upperStarComp (WeilCoefficients.{u} l) a.hom b.hom).hom.app M.X ≫
      (a.hom)^*[WeilCoefficients.{u} l].map
        ((upperStarIsoLowerStarInv _ b).hom.app M.X ≫ c.hom) ≫
      (upperStarIsoLowerStarInv _ a).hom.app N.X ≫ ψ.hom =
    (upperStarCongr (WeilCoefficients.{u} l) hc).hom.app M.X ≫
      (upperStarComp (WeilCoefficients.{u} l) b.hom a.hom).hom.app M.X ≫
      (b.hom)^*[WeilCoefficients.{u} l].map
        ((upperStarIsoLowerStarInv _ a).hom.app M.X ≫ φ.hom) ≫
      (upperStarIsoLowerStarInv _ b).hom.app M.X ≫ c.hom := by
  apply upper_square_of_lower_concrete (WeilCoefficients.{u} l) a b hc hci M.X N.X φ.hom ψ.hom c.hom
  have H := congrArg (fun f ↦ f.hom) h
  simpa only [Mod.comp_hom', adicLowerStar_map_hom,
    adicLowerStarSquareIso_hom_app_hom, lowerStarFactor_rfl,
    adicLowerStar_obj_X, Category.assoc] using H

private theorem adic_congr_eqToIso
    {l : ℕ} [Fact l.Prime] {S T : Scheme.{u}} {f g : S ⟶ T} (h : f = g) :
    adicLowerStarCongr l h = eqToIso (congrArg (fun f : S ⟶ T ↦ (f)_*ᵃ[l]) h) := by
  subst g
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply Mod.hom_ext
  rfl

private theorem pushforward_square_intertwines
    {l : ℕ} [Fact l.Prime] {Z Z' : Scheme.{u}}
    (p : Z ⟶ Z') (a F : Z ⟶ Z) (a' F' : Z' ⟶ Z')
    (ha : p ≫ a' = a ≫ p) (hF : p ≫ F' = F ≫ p)
    (hc : a ≫ F = F ≫ a) (hc' : a' ≫ F' = F' ≫ a')
    (M N : AdicSheaf l Z) (φ : (F)_*ᵃ[l].obj M ⟶ M)
    (ψ : (F)_*ᵃ[l].obj N ⟶ N) (t : (a)_*ᵃ[l].obj M ⟶ N)
    (ht : (F)_*ᵃ[l].map t ≫ ψ =
      (adicLowerStarSquareIso l hc).hom.app M ≫ (a)_*ᵃ[l].map φ ≫ t) :
    (F')_*ᵃ[l].map ((adicLowerStarSquareIso l ha).hom.app M ≫ (p)_*ᵃ[l].map t) ≫
        (adicLowerStarSquareIso l hF).hom.app N ≫ (p)_*ᵃ[l].map ψ =
      (adicLowerStarSquareIso l hc').hom.app ((p)_*ᵃ[l].obj M) ≫
        (a')_*ᵃ[l].map ((adicLowerStarSquareIso l hF).hom.app M ≫ (p)_*ᵃ[l].map φ) ≫
        (adicLowerStarSquareIso l ha).hom.app M ≫ (p)_*ᵃ[l].map t := by
  have nF := (adicLowerStarSquareIso l hF).hom.naturality t
  have na := (adicLowerStarSquareIso l ha).hom.naturality φ
  simp only [Functor.comp_map] at nF na
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% nF,
    ← Functor.map_comp (p)_*ᵃ[l] ((F)_*ᵃ[l].map t) ψ, ht, Functor.map_comp,
    Functor.map_comp,
    reassoc_of% adicLowerStarSquareIso_cube p p a a' F F' F F' ha hF hF hc hc']
  rw [← reassoc_of% na]

variable {k₀ k₁ : Type u} [Field k₀] [Finite k₀] [Field k₁] [Finite k₁]
  {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] [Fact (ringChar k₁ ≠ l)]
  {X C : Scheme.{u}} [X.Over (Spec (.of k₀))] [C.Over (Spec (.of k₁))]

omit [Fact (ringChar k₀ ≠ l)] in
private theorem power_iterate_congr (m n : ℕ) (h : m = n)
    (M : AdicSheaf l (X ↘ Spec (.of k₀)).geometricFiber) :
    (ProEtaleWeilSheaf.frobeniusPowPullbackIterateIso m).hom.app M ≫
        eqToHom (Functor.congr_obj
          (congrArg (frobeniusPullback k₀ l X).iterate h) M) =
      eqToHom (Functor.congr_obj
        (congrArg (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X) h) M) ≫
        (ProEtaleWeilSheaf.frobeniusPowPullbackIterateIso n).hom.app M := by
  subst n
  simp

omit [Fact (ringChar k₀ ≠ l)] in
private theorem power_comm_geometric (j r : ℕ)
    (hc : ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ j).inv ≫
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).inv =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).inv ≫
        ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ j).inv) :
    ProEtaleWeilSheaf.frobeniusPowerCommIso (k₀ := k₀) (l := l) (X := X) j r =
      adicLowerStarSquareIso l hc := by
  have hjr : ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ j).inv ≫
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).inv =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (j + r)).inv := by
    rw [pow_add, Aut.Aut_mul_def, Iso.trans_inv]
  have hrj : ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).inv ≫
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ j).inv =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r + j)).inv := by
    rw [pow_add, Aut.Aut_mul_def, Iso.trans_inv]
  rw [ProEtaleWeilSheaf.frobeniusPowerCommIso,
    ProEtaleWeilSheaf.frobeniusPowerCompositionIso_geometric j r hjr,
    ProEtaleWeilSheaf.frobeniusPowerCompositionIso_geometric r j hrj]
  apply Iso.ext
  apply NatTrans.ext
  funext M
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc, eqToIso.hom, eqToHom_app]
  rw [reassoc_of% power_iterate_congr (j + r) (r + j) (Nat.add_comm j r) M]
  simp only [Iso.hom_inv_id_app_assoc, adicLowerStarSquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    adic_congr_eqToIso, eqToIso.hom, eqToIso.inv, eqToHom_app,
    eqToHom_trans_assoc]

/-- The conjugate of the old geometric Frobenius power on the new geometric fibre.
Source: geometric orbit argument in `sk-i-dl-general-real`.
(blueprint: lem-zl-frobenius-power-translate-structure). -/
noncomputable def frobeniusPowerTranslateAut
    (θ : (X ↘ Spec (.of k₀)).geometricFiber ≅ (C ↘ Spec (.of k₁)).geometricFiber)
    (j : ℕ) : Aut (C ↘ Spec (.of k₁)).geometricFiber :=
  θ.symm ≪≫ ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ j) ≪≫ θ

/-- The actual carrier comparison for a translated power-return sheaf. This is
constructed from pullback composition and the supplied isomorphism, without choosing data
from any existence theorem.
Source: geometric orbit argument in `sk-i-dl-general-real`.
(blueprint: lem-zl-frobenius-power-translate-structure). -/
noncomputable def frobeniusPowerTranslateSheafIso
    (θ : (X ↘ Spec (.of k₀)).geometricFiber ≅ (C ↘ Spec (.of k₁)).geometricFiber)
    (r : ℕ)
    (hθ : θ.hom ≫ (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)
    (P Q : IsoAlgebra (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r))
    (j : ℕ)
    (e : (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j).obj P.carrier ≅ Q.carrier)
    (A B : WeilSheaf k₁ l C)
    (hA : A.obj = (IsoAlgebra.mapOfNatIso
      (ProEtaleWeilSheaf.transportCommIso θ r hθ)).obj P)
    (hB : B.obj = (IsoAlgebra.mapOfNatIso
      (ProEtaleWeilSheaf.transportCommIso θ r hθ)).obj Q) :
    ((frobeniusPowerTranslateAut θ j).hom)^*[WeilCoefficients.{u} l].obj A.obj.carrier.X ≅
      B.obj.carrier.X :=
  (upperStarIsoLowerStarInv _ (frobeniusPowerTranslateAut θ j)).app A.obj.carrier.X ≪≫
    (AdicSheaf.forget _).mapIso
      ((((frobeniusPowerTranslateAut θ j).inv)_*ᵃ[l]).mapIso
          (eqToIso (congrArg (fun K : ProEtaleWeilSheaf k₁ l C ↦ K.carrier) hA)) ≪≫
        (adicLowerStarComp l θ.hom (frobeniusPowerTranslateAut θ j).inv).app P.carrier ≪≫
        (adicLowerStarCongr l (by
          simp [frobeniusPowerTranslateAut])).app P.carrier ≪≫
        (adicLowerStarComp l
          ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ j).inv θ.hom).symm.app P.carrier ≪≫
        ((θ.hom)_*ᵃ[l]).mapIso e ≪≫
        (eqToIso (congrArg (fun K : ProEtaleWeilSheaf k₁ l C ↦ K.carrier) hB)).symm)

@[irreducible] private noncomputable def powerTranslateAdicIso
    (θ : (X ↘ Spec (.of k₀)).geometricFiber ≅ (C ↘ Spec (.of k₁)).geometricFiber)
    (r : ℕ)
    (hθ : θ.hom ≫ (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)
    (P Q : IsoAlgebra (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r))
    (j : ℕ)
    (e : (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j).obj P.carrier ≅ Q.carrier)
    (A B : WeilSheaf k₁ l C)
    (hA : A.obj = (IsoAlgebra.mapOfNatIso
      (ProEtaleWeilSheaf.transportCommIso θ r hθ)).obj P)
    (hB : B.obj = (IsoAlgebra.mapOfNatIso
      (ProEtaleWeilSheaf.transportCommIso θ r hθ)).obj Q) :
    ((frobeniusPowerTranslateAut θ j).inv)_*ᵃ[l].obj A.obj.carrier ≅ B.obj.carrier :=
      ((((frobeniusPowerTranslateAut θ j).inv)_*ᵃ[l]).mapIso
          (eqToIso (congrArg (fun K : ProEtaleWeilSheaf k₁ l C ↦ K.carrier) hA)) ≪≫
        (adicLowerStarComp l θ.hom (frobeniusPowerTranslateAut θ j).inv).app P.carrier ≪≫
        (adicLowerStarCongr l (by
          simp [frobeniusPowerTranslateAut])).app P.carrier ≪≫
        (adicLowerStarComp l
          ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ j).inv θ.hom).symm.app P.carrier ≪≫
        ((θ.hom)_*ᵃ[l]).mapIso e ≪≫
        (eqToIso (congrArg (fun K : ProEtaleWeilSheaf k₁ l C ↦ K.carrier) hB)).symm)

omit [Fact (ringChar k₀ ≠ l)] in
private theorem translate_iso_formula
    (θ : (X ↘ Spec (.of k₀)).geometricFiber ≅ (C ↘ Spec (.of k₁)).geometricFiber)
    (r : ℕ)
    (hθ : θ.hom ≫ (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)
    (P Q : IsoAlgebra (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r))
    (j : ℕ)
    (e : (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j).obj P.carrier ≅ Q.carrier)
    (A B : WeilSheaf k₁ l C)
    (hA : A.obj = (IsoAlgebra.mapOfNatIso
      (ProEtaleWeilSheaf.transportCommIso θ r hθ)).obj P)
    (hB : B.obj = (IsoAlgebra.mapOfNatIso
      (ProEtaleWeilSheaf.transportCommIso θ r hθ)).obj Q) :
    frobeniusPowerTranslateSheafIso θ r hθ P Q j e A B hA hB =
      (upperStarIsoLowerStarInv _ (frobeniusPowerTranslateAut θ j)).app A.obj.carrier.X ≪≫
        (AdicSheaf.forget _).mapIso (powerTranslateAdicIso θ r hθ P Q j e A B hA hB) := by
  unfold frobeniusPowerTranslateSheafIso powerTranslateAdicIso
  rfl

omit [Fact (ringChar k₀ ≠ l)] in
private theorem translate_hom_normalized
    (θ : (X ↘ Spec (.of k₀)).geometricFiber ≅ (C ↘ Spec (.of k₁)).geometricFiber)
    (r : ℕ)
    (hθ : θ.hom ≫ (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)
    (P Q : IsoAlgebra (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r))
    (j : ℕ)
    (e : (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j).obj P.carrier ≅ Q.carrier)
    (A B : WeilSheaf k₁ l C)
    (hA : A.obj = (IsoAlgebra.mapOfNatIso
      (ProEtaleWeilSheaf.transportCommIso θ r hθ)).obj P)
    (hB : B.obj = (IsoAlgebra.mapOfNatIso
      (ProEtaleWeilSheaf.transportCommIso θ r hθ)).obj Q) :
    (frobeniusPowerTranslateSheafIso θ r hθ P Q j e A B hA hB).hom =
      (upperStarIsoLowerStarInv _ (frobeniusPowerTranslateAut θ j)).hom.app
          A.obj.carrier.X ≫ (powerTranslateAdicIso θ r hθ P Q j e A B hA hB).hom.hom := by
  have H := congrArg Iso.hom (translate_iso_formula θ r hθ P Q j e A B hA hB)
  simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, forget_map] using H

omit [Fact (ringChar k₀ ≠ l)] in
private theorem lower_equivariance_from_carrier_eq
    (θ : (X ↘ Spec (.of k₀)).geometricFiber ≅ (C ↘ Spec (.of k₁)).geometricFiber)
    (r : ℕ)
    (hθ : θ.hom ≫ (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)
    (P Q : IsoAlgebra (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r))
    (j : ℕ)
    (e : (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j).obj P.carrier ≅ Q.carrier)
    (A B : WeilSheaf k₁ l C)
    (hA : A.obj = (IsoAlgebra.mapOfNatIso
      (ProEtaleWeilSheaf.transportCommIso θ r hθ)).obj P)
    (hB : B.obj = (IsoAlgebra.mapOfNatIso
      (ProEtaleWeilSheaf.transportCommIso θ r hθ)).obj Q)
    (hβ : θ.hom ≫ (frobeniusPowerTranslateAut θ j).inv =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ j).inv ≫ θ.hom)
    (hci : (frobeniusPowerTranslateAut θ j).inv ≫
        (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.inv =
      (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.inv ≫
        (frobeniusPowerTranslateAut θ j).inv)
    (h : ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius.inv)_*ᵃ[l].map
        ((adicLowerStarSquareIso l hβ).hom.app P.carrier ≫ (θ.hom)_*ᵃ[l].map e.hom) ≫
          (ProEtaleWeilSheaf.transportCommIso θ r hθ).hom.app Q.carrier ≫
            (θ.hom)_*ᵃ[l].map Q.str.hom =
      (adicLowerStarSquareIso l hci).hom.app ((θ.hom)_*ᵃ[l].obj P.carrier) ≫
        ((frobeniusPowerTranslateAut θ j).inv)_*ᵃ[l].map
          ((ProEtaleWeilSheaf.transportCommIso θ r hθ).hom.app P.carrier ≫
            (θ.hom)_*ᵃ[l].map P.str.hom) ≫
        (adicLowerStarSquareIso l hβ).hom.app P.carrier ≫ (θ.hom)_*ᵃ[l].map e.hom) :
    ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius.inv)_*ᵃ[l].map
        (powerTranslateAdicIso θ r hθ P Q j e A B hA hB).hom ≫ B.obj.str.hom =
      (adicLowerStarSquareIso l hci).hom.app A.obj.carrier ≫
        ((frobeniusPowerTranslateAut θ j).inv)_*ᵃ[l].map A.obj.str.hom ≫
          (powerTranslateAdicIso θ r hθ P Q j e A B hA hB).hom := by
  rcases A with ⟨A, hAc⟩
  rcases B with ⟨B, hBc⟩
  dsimp only at hA hB
  subst A
  subst B
  simpa only [powerTranslateAdicIso, IsoAlgebra.mapOfNatIso_obj_str,
    IsoAlgebra.mapOfNatIso_obj_carrier, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom, NatTrans.comp_app, Functor.mapIso_hom,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id, Category.assoc,
    adicLowerStarSquareIso] using h

-- Preserve the existing characteristic-instance binder of the public theorem.
set_option linter.unusedSectionVars false in
/-- Equivariance for the r-return becomes the single-return square after geometric
transport. There are no points, scalar Frobenii, stalks, or iterated new returns in this lemma.

Source: step 2 of `lem-zl-frobenius-power-stalk-transport`, geometric orbit argument in
`sk-i-dl-general-real`.
(blueprint: lem-zl-frobenius-power-translate-structure).

Proof: Put g = Fr_X, f = Fr_C, beta = theta^-1 g^j theta. The carrier comparison is
beta^* theta_* P = (beta^-1)_* theta_* P = theta_* (g^-j)_* P, followed by theta_* e.
Expand the transported structures of A and B from mapOfNatIso. In the two composites,
combine consecutive pushforwards using lowerStarComp. Their common scheme map is the
inverse of f ; beta = beta ; f, which follows from theta ; f = g^r ; theta and the
commutation of powers of g. The comparison between the two orders of g-pullbacks is
frobeniusPowerCommIso: its recursive identification with ordinary functor iterates
agrees with lowerStarComp by induction, with lowerStarId at zero and associativity at
successors. Thus the remaining equality is theta_* applied to he. Forgetting the adic
module structure and using upperStarIsoLowerStarInv_hom_app_trans gives precisely the
displayed square. Naturality moves e through the comparisons. This works also for
j = 0 or r = 0, using the identity compositors. -/
theorem frobeniusStr_powerTranslate
    (θ : (X ↘ Spec (.of k₀)).geometricFiber ≅ (C ↘ Spec (.of k₁)).geometricFiber)
    (r : ℕ)
    (hθ : θ.hom ≫ (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).hom ≫ θ.hom)
    (P Q : IsoAlgebra (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r))
    (j : ℕ)
    (e : (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j).obj P.carrier ≅ Q.carrier)
    (he : (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X r).map e.hom ≫ Q.str.hom =
      (ProEtaleWeilSheaf.frobeniusPowerCommIso j r).hom.app P.carrier ≫
        (ProEtaleWeilSheaf.frobeniusPowPullback k₀ l X j).map P.str.hom ≫ e.hom)
    (A B : WeilSheaf k₁ l C)
    (hA : A.obj = (IsoAlgebra.mapOfNatIso
      (ProEtaleWeilSheaf.transportCommIso θ r hθ)).obj P)
    (hB : B.obj = (IsoAlgebra.mapOfNatIso
      (ProEtaleWeilSheaf.transportCommIso θ r hθ)).obj Q)
    (hc : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom ≫
        (frobeniusPowerTranslateAut θ j).hom =
      (frobeniusPowerTranslateAut θ j).hom ≫
        (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom) :
    (upperStarComp (WeilCoefficients.{u} l)
      (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom
      (frobeniusPowerTranslateAut θ j).hom).hom.app A.obj.carrier.X ≫
        ((C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom)^*[WeilCoefficients.{u} l].map
          (frobeniusPowerTranslateSheafIso θ r hθ P Q j e A B hA hB).hom ≫
        WeilSheaf.frobeniusStr B =
      (upperStarCongr (WeilCoefficients.{u} l) hc).hom.app A.obj.carrier.X ≫
        (upperStarComp (WeilCoefficients.{u} l) (frobeniusPowerTranslateAut θ j).hom
          (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.hom).hom.app A.obj.carrier.X ≫
          ((frobeniusPowerTranslateAut θ j).hom)^*[WeilCoefficients.{u} l].map
            (WeilSheaf.frobeniusStr A) ≫
          (frobeniusPowerTranslateSheafIso θ r hθ P Q j e A B hA hB).hom := by
  have hβ : θ.hom ≫ (frobeniusPowerTranslateAut θ j).inv =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ j).inv ≫ θ.hom := by
    simp [frobeniusPowerTranslateAut]
  have hF := ProEtaleWeilSheaf.hom_comp_geometricGaloisFrobenius_inv θ r hθ
  have hci : (frobeniusPowerTranslateAut θ j).inv ≫
      (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.inv =
      (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.inv ≫
        (frobeniusPowerTranslateAut θ j).inv := by
    have H : (C ↘ Spec (.of k₁)).geometricGaloisFrobenius ≪≫
          frobeniusPowerTranslateAut θ j =
        frobeniusPowerTranslateAut θ j ≪≫
          (C ↘ Spec (.of k₁)).geometricGaloisFrobenius := Iso.ext hc
    exact congrArg Iso.inv H
  have hcold : ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ j).inv ≫
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).inv =
      ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).inv ≫
        ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ j).inv := by
    calc
      _ = ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (j + r)).inv := by
        rw [pow_add, Aut.Aut_mul_def, Iso.trans_inv]
      _ = ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ (r + j)).inv := by
        rw [Nat.add_comm]
      _ = _ := by rw [pow_add, Aut.Aut_mul_def, Iso.trans_inv]
  rw [power_comm_geometric j r hcold] at he
  have H := pushforward_square_intertwines θ.hom
    ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ j).inv
    ((X ↘ Spec (.of k₀)).geometricGaloisFrobenius ^ r).inv
    (frobeniusPowerTranslateAut θ j).inv
    (C ↘ Spec (.of k₁)).geometricGaloisFrobenius.inv
    hβ hF hcold hci P.carrier Q.carrier P.str.hom Q.str.hom e.hom he
  have Hc := lower_equivariance_from_carrier_eq θ r hθ P Q j e A B hA hB hβ hci H
  have U := upper_square_of_adic_lower
    (C ↘ Spec (.of k₁)).geometricGaloisFrobenius (frobeniusPowerTranslateAut θ j) hc hci
    A.obj.carrier B.obj.carrier A.obj.str.hom B.obj.str.hom
    (powerTranslateAdicIso θ r hθ P Q j e A B hA hB).hom Hc
  simpa only [translate_hom_normalized, frobeniusStr, forget_map, Category.assoc] using U

end AlgebraicGeometry.WeilSheaf
