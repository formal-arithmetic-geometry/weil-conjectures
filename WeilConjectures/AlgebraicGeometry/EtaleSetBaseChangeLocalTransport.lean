/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.BaseChangeMapAbelianAndSets

import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.SixFunctors.BaseChange.Pasting

/-!
# Transport of set-valued exchange invertibility to a single etale chart

Source: Stacks Project, Tag 0EZR, the two restriction identities in the proof of
`lemma-base-change-local` (blueprint: lem-sbc-sets-local-exchange-isIso-transport).
-/

@[expose] public section

set_option autoImplicit false

universe u v
open CategoryTheory CategoryTheory.Limits Category
namespace AlgebraicGeometry.Etale.SetExchangePasting

variable {C : Scheme.{u} → Type v} [∀ X, Category.{u + 1} (C X)]

private structure System (C : Scheme.{u} → Type v) [∀ X, Category.{u + 1} (C X)] where
  L : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → (C Y ⥤ C X)
  R : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → (C X ⥤ C Y)
  adj : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), L f ⊣ R f
  dcomp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (_hfg : fg = f ≫ g), R f ⋙ R g ≅ R fg
  assoc : ∀ {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ V)
    (fgh : X ⟶ V) (hfgh : fgh = f ≫ g ≫ h),
    (R f).associator (R g) (R h) ≪≫
      Functor.isoWhiskerLeft (R f) (dcomp g h (g ≫ h) rfl) ≪≫
        dcomp f (g ≫ h) fgh hfgh =
      Functor.isoWhiskerRight (dcomp f g (f ≫ g) rfl) (R h) ≪≫
        dcomp (f ≫ g) h fgh (by rw [hfgh, Category.assoc])

private noncomputable def lowerComp (sys : System C) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (sys.R f ⋙ sys.R g : C X ⥤ C Z) ≅ sys.R fg := sys.dcomp f g fg hfg

@[irreducible]
private noncomputable def upperComp (sys : System C) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (sys.L fg : C Z ⥤ C X) ≅ sys.L g ⋙ sys.L f :=
  ((conjugateIsoEquiv (sys.adj fg) ((sys.adj g).comp (sys.adj f))).symm
    (lowerComp sys f g fg hfg).symm).symm

private theorem conjugate_comp (sys : System C) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    conjugateIsoEquiv ((sys.adj g).comp (sys.adj f)) (sys.adj fg) (upperComp sys f g fg hfg) =
      lowerComp sys f g fg hfg := by
  ext : 1
  simp only [upperComp, conjugateIsoEquiv_apply_hom, Iso.symm_hom,
    conjugateIsoEquiv_symm_apply_inv, Iso.symm_inv]
  exact Equiv.apply_symm_apply _ _

private theorem comp_assoc (sys : System C) {X Y Z V : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Z ⟶ V)
    (fgh : X ⟶ V) (hfgh : fgh = f ≫ g ≫ h) :
    upperComp sys f (g ≫ h) fgh hfgh ≪≫
        Functor.isoWhiskerRight (upperComp sys g h (g ≫ h) rfl) (sys.L f) ≪≫
          (sys.L h).associator (sys.L g) (sys.L f) =
      upperComp sys (f ≫ g) h fgh (by rw [hfgh, assoc]) ≪≫
        Functor.isoWhiskerLeft (sys.L h) (upperComp sys f g (f ≫ g) rfl) := by
  refine (conjugateIsoEquiv ((sys.adj h).comp ((sys.adj g).comp (sys.adj f)))
    (sys.adj fgh)).injective ?_
  rw [conjugateIsoEquiv_trans _ ((sys.adj (g ≫ h)).comp (sys.adj f)) _,
    conjugateIsoEquiv_trans _ (((sys.adj h).comp (sys.adj g)).comp (sys.adj f)) _,
    conjugateIsoEquiv_trans _ ((sys.adj h).comp (sys.adj (f ≫ g))) _]
  simp only [conjugateIsoEquiv_isoWhiskerRight,
    conjugateIsoEquiv_isoWhiskerLeft, conjugateIsoEquiv_associator, Iso.trans_assoc]
  rw [conjugate_comp sys f (g ≫ h) fgh hfgh,
    conjugate_comp sys g h (g ≫ h) rfl,
    conjugate_comp sys (f ≫ g) h fgh (by rw [hfgh, assoc]),
    conjugate_comp sys f g]
  exact sys.assoc f g h fgh hfgh

private theorem comp_assoc' (sys : System C) {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z) (hfg : fg = f ≫ g) (hgh : gh = g ≫ h)
    (hfgh : fgh = fg ≫ h) :
    (upperComp sys f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
        Functor.whiskerRight (upperComp sys g h gh hgh).hom (sys.L f) =
      (upperComp sys fg h fgh hfgh).hom ≫
        Functor.whiskerLeft (sys.L h) (upperComp sys f g fg hfg).hom := by
  subst hfg
  subst hgh
  subst hfgh
  have key := congrArg Iso.hom
    (comp_assoc sys f g h ((f ≫ g) ≫ h) (Category.assoc f g h))
  refine NatTrans.ext (funext fun G => ?_)
  simpa using NatTrans.congr_app key G

@[reassoc]
private theorem map_comp_hom_app_upperStarComp_inv_app (sys : System C) {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (G : C Z) :
    (sys.L f).map ((upperComp sys g h gh hgh).hom.app G) ≫
        (upperComp sys f g fg hfg).inv.app ((sys.L h).obj G) =
      (upperComp sys f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).inv.app G ≫
        (upperComp sys fg h fgh hfgh).hom.app G := by
  have key := NatTrans.congr_app (comp_assoc' sys f g h fg gh fgh hfg hgh hfgh) G
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at key
  simpa using CategoryTheory.comp_inv_eq_inv_comp_of_eq _ _ _ _ key

@[reassoc]
private theorem comp_hom_app_map_upperStarComp_inv_app (sys : System C) {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z) (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h)
    (G : C Z) :
    (upperComp sys f g fg hfg).hom.app ((sys.L h).obj G) ≫
        (sys.L f).map ((upperComp sys g h gh hgh).inv.app G) =
      (upperComp sys fg h fgh hfgh).inv.app G ≫
        (upperComp sys f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom.app G := by
  have key := NatTrans.congr_app (comp_assoc' sys f g h fg gh fgh hfg hgh hfgh) G
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at key
  have := CategoryTheory.comp_inv_eq_inv_comp_of_eq _ _ _ _ key.symm
  rwa [NatIso.inv_hom_app, ← Functor.map_inv, NatIso.inv_hom_app] at this

@[irreducible]
private noncomputable def square (sys : System C)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) : sys.L g ⋙ sys.L f' ≅ sys.L f ⋙ sys.L g' :=
  (upperComp sys f' g (g' ≫ f) sq.w).symm ≪≫ upperComp sys g' f (g' ≫ f) rfl

private noncomputable abbrev bcSquare (sys : System C)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) : TwoSquare (sys.R f) (sys.L g') (sys.L g) (sys.R f') :=
  mateEquiv (sys.adj f) (sys.adj f')
    (TwoSquare.mk (sys.L g) (sys.L f) (sys.L f') (sys.L g') (square sys sq).hom)

@[irreducible]
private noncomputable def bc (sys : System C)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) : sys.R f ⋙ sys.L g ⟶ sys.L g' ⋙ sys.R f' :=
  (bcSquare sys sq).natTrans

variable {X'' X' X Y'' Y' Y : Scheme.{u}} {g'' : X'' ⟶ X'} {g' : X' ⟶ X}
  {f'' : X'' ⟶ Y''} {f' : X' ⟶ Y'} {f : X ⟶ Y} {h : Y'' ⟶ Y'} {g : Y' ⟶ Y}

open scoped TwoSquare in
private theorem square_paste_horiz (sys : System C) (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g'' f'' f' h) (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) :
    (square sys sq).hom =
      Functor.whiskerRight (upperComp sys h g (h ≫ g) rfl).hom (sys.L f'') ≫
        (TwoSquare.mk (sys.L g) (sys.L f) (sys.L f') (sys.L g') (square sys sq₁).hom ≫ₕ
          TwoSquare.mk (sys.L h) (sys.L f') (sys.L f'') (sys.L g'') (square sys sq₂).hom).natTrans ≫
        Functor.whiskerLeft (sys.L f) (upperComp sys g'' g' (g'' ≫ g') rfl).inv := by
  refine NatTrans.ext (funext fun F => ?_)
  simp only [square, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.comp_obj, TwoSquare.hComp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Category.assoc]
  rw [map_comp_hom_app_upperStarComp_inv_app_assoc sys f'' h g (g'' ≫ f')
    (h ≫ g) ((g'' ≫ g') ≫ f) sq₂.w rfl (by rw [Category.assoc, sq₁.w, Category.assoc]),
    comp_hom_app_map_upperStarComp_inv_app_assoc sys g'' f' g (g'' ≫ f')
    (g' ≫ f) ((g'' ≫ g') ≫ f) rfl sq₁.w (by rw [Category.assoc, sq₁.w, Category.assoc]),
    map_comp_hom_app_upperStarComp_inv_app sys g'' g' f (g'' ≫ g') (g' ≫ f)
    ((g'' ≫ g') ≫ f) rfl rfl rfl, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app_assoc]

open scoped TwoSquare in
private theorem bcSquare_paste_horiz (sys : System C) (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g'' f'' f' h)
    (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) :
    bcSquare sys sq =
      ((bcSquare sys sq₁ ≫ᵥ bcSquare sys sq₂).whiskerRight
        (upperComp sys h g (h ≫ g) rfl).hom).whiskerLeft
        (upperComp sys g'' g' (g'' ≫ g') rfl).inv := by
  have h1 : TwoSquare.mk (sys.L (h ≫ g)) (sys.L f) (sys.L f'') (sys.L (g'' ≫ g'))
      (square sys sq).hom =
      ((TwoSquare.mk (sys.L g) (sys.L f) (sys.L f') (sys.L g') (square sys sq₁).hom ≫ₕ
        TwoSquare.mk (sys.L h) (sys.L f') (sys.L f'') (sys.L g'') (square sys sq₂).hom).whiskerTop
          (upperComp sys h g (h ≫ g) rfl).hom).whiskerBottom
          (upperComp sys g'' g' (g'' ≫ g') rfl).inv := by
    refine TwoSquare.ext _ _ fun F => ?_
    have := NatTrans.congr_app (square_paste_horiz sys sq₁ sq₂ sq) F
    simpa only [TwoSquare.whiskerBottom_app, TwoSquare.whiskerTop_app, NatTrans.comp_app,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc] using this
  rw [bcSquare, h1, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp]

private theorem bc_paste_horiz_app (sys : System C) (sq₁ : CommSq g' f' f g)
    (sq₂ : CommSq g'' f'' f' h)
    (sq : CommSq (g'' ≫ g') f'' f (h ≫ g)) (F : C X) :
    (bc sys sq).app F =
      (upperComp sys h g (h ≫ g) rfl).hom.app ((sys.R f).obj F) ≫
        (sys.L h).map ((bc sys sq₁).app F) ≫
        (bc sys sq₂).app ((sys.L g').obj F) ≫
        (sys.R f'').map ((upperComp sys g'' g' (g'' ≫ g') rfl).inv.app F) := by
  have := NatTrans.congr_app (bcSquare_paste_horiz sys sq₁ sq₂ sq) F
  simp only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.vComp_app,
    Functor.comp_obj, Category.assoc] at this
  simp only [bc]
  exact this

@[irreducible]
private noncomputable def rightSquare (sys : System C)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) : sys.R g' ⋙ sys.R f ≅ sys.R f' ⋙ sys.R g :=
  lowerComp sys g' f (g' ≫ f) rfl ≪≫ (lowerComp sys f' g (g' ≫ f) sq.w).symm

private theorem mate_bc (sys : System C)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    (mateEquiv (sys.adj g') (sys.adj g)
      (TwoSquare.mk (sys.R f) (sys.L g') (sys.L g) (sys.R f') (bc sys sq))).natTrans =
      (rightSquare sys sq).hom := by
  rw [bc, bcSquare, iterated_mateEquiv_conjugateEquiv]
  simp only [square, Iso.trans_hom, Iso.symm_hom]
  unfold rightSquare
  change conjugateEquiv _ _ ((upperComp sys f' g (g' ≫ f) sq.w).inv ≫
    (upperComp sys g' f (g' ≫ f) rfl).hom) = (lowerComp sys g' f (g' ≫ f) rfl).hom ≫
      (lowerComp sys f' g (g' ≫ f) sq.w).inv
  rw [← conjugateEquiv_comp _ (sys.adj (g' ≫ f))]
  congr 1
  · exact congrArg Iso.hom (conjugate_comp sys g' f (g' ≫ f) rfl)
  · exact congrArg Iso.inv (conjugate_comp sys f' g (g' ≫ f) sq.w)

private theorem bc_formula (sys : System C)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) (F : C X) :
    (bc sys sq).app F =
      (sys.L g).map ((sys.R f).map ((sys.adj g').unit.app F) ≫
        (lowerComp sys g' f (g' ≫ f) rfl).hom.app _ ≫
        (lowerComp sys f' g (g' ≫ f) sq.w).inv.app _) ≫
        (sys.adj g).counit.app _ := by
  have hm : bcSquare sys sq = (mateEquiv (sys.adj g') (sys.adj g)).symm
      (TwoSquare.mk _ _ _ _ (rightSquare sys sq).hom) := by
    apply (mateEquiv (sys.adj g') (sys.adj g)).eq_symm_apply.mpr
    simpa only [bc] using mate_bc sys sq
  unfold bc
  rw [hm]
  simp [mateEquiv, rightSquare]

private theorem isIso_of_isIso_comp₄ {D : Type*} [Category D]
    {W₀ W₁ W₂ W₃ W₄ : D} (x : W₀ ⟶ W₁) (y : W₁ ⟶ W₂)
    (z : W₂ ⟶ W₃) (w : W₃ ⟶ W₄) [IsIso x] [IsIso z] [IsIso w]
    (h : IsIso (x ≫ y ≫ z ≫ w)) : IsIso y := by
  have : IsIso (y ≫ z ≫ w) := IsIso.of_isIso_comp_left x _
  have : IsIso ((y ≫ z) ≫ w) := by rwa [Category.assoc]
  have : IsIso (y ≫ z) := IsIso.of_isIso_comp_right _ w
  exact IsIso.of_isIso_comp_right y z

private theorem isIso_paste_horiz_of_eq (sys : System C)
    {X₁ Z₁ Y₁ Y₂ S T : Scheme.{u}} {g : T ⟶ S} {p₂ : Z₁ ⟶ S}
    {e₂ : Y₂ ⟶ T} {h₂ : Y₂ ⟶ Z₁} {p₁ : X₁ ⟶ Z₁}
    {e₁ : Y₁ ⟶ Y₂} {h₁ : Y₁ ⟶ X₁} {e₀ : Y₁ ⟶ T} {p₀ : X₁ ⟶ S}
    (sq₂ : CommSq e₂ h₂ g p₂) (sq₁ : CommSq e₁ h₁ h₂ p₁)
    (sq₀ : CommSq e₀ h₁ g p₀) (he : e₁ ≫ e₂ = e₀) (hp : p₁ ≫ p₂ = p₀)
    (F : C T)
    (hF₂ : IsIso ((bc sys sq₂).app F))
    (hF₁ : IsIso ((bc sys sq₁).app ((sys.L e₂).obj F))) :
    IsIso ((bc sys sq₀).app F) := by
  subst he hp
  rw [bc_paste_horiz_app sys sq₂ sq₁ sq₀ F]
  infer_instance

private theorem isIso_local_chart (sys : System C)
    {X Y S T U V T' Y' : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : CommSq e h g f) {a : U ⟶ X} {fi : U ⟶ V} {b : V ⟶ S}
    {c : T' ⟶ T} {gi : T' ⟶ V} (hc : CommSq c gi g b)
    {ei : Y' ⟶ T'} {hi : Y' ⟶ U} (sqi : CommSq ei hi gi fi)
    {d : Y' ⟶ Y} (sqa : CommSq d hi h a)
    (hd : ei ≫ c = d ≫ e) (hp : fi ≫ b = a ≫ f) (F : C T)
    (hcIso : IsIso (bc sys hc))
    (haIso : IsIso (bc sys sqa))
    (hF : IsIso ((bc sys sqi).app ((sys.L c).obj F))) :
    IsIso ((sys.L a).map ((bc sys sq).app F)) := by
  have hout := isIso_paste_horiz_of_eq sys hc sqi
    (sqa.horiz_comp sq) hd hp F (by infer_instance) hF
  rw [bc_paste_horiz_app sys sq sqa] at hout
  exact isIso_of_isIso_comp₄ _ _ _ _ hout

end AlgebraicGeometry.Etale.SetExchangePasting

namespace AlgebraicGeometry.Etale.SetExchangeTransport

private noncomputable def L {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  Scheme.etaleSetPullback f
private noncomputable def R {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  lowerStar (Type (u + 1)) f
private noncomputable def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : L f ⊣ R f :=
  setUpperLowerAdjunction f
private noncomputable def dcomp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) : R f ⋙ R g ≅ R fg :=
  lowerStarComp (Type (u + 1)) f g fg hfg

private noncomputable def sys :
    SetExchangePasting.System (fun X : Scheme.{u} =>
      Sheaf X.smallEtaleTopology (Type (u + 1))) where
  L := @L
  R := @R
  adj := @adj
  dcomp := @dcomp
  assoc := by
    intro X Y Z V f g h fgh hfgh
    exact lowerStarComp_assoc (Type (u + 1)) f g h fgh hfgh

private noncomputable abbrev bc
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :=
  SetExchangePasting.bc sys sq

private theorem bc_app_eq
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) :
    (bc sq.toCommSq.flip).app F = setBaseChangeArrow sq F := by
  simpa only [bc, sys, L, R, adj, dcomp, SetExchangePasting.lowerComp, setBaseChangeArrow] using
    SetExchangePasting.bc_formula sys sq.toCommSq.flip F

private theorem etale_bc_isIso
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    [AlgebraicGeometry.Etale g] [AlgebraicGeometry.Etale g'] :
    IsIso (bc sq.toCommSq) := by
  let ag := localizationRestrictionLowerStarAdjunction (Type (u + 1)) g inferInstance
  let ag' := localizationRestrictionLowerStarAdjunction (Type (u + 1)) g' inferInstance
  let ρ := (adj g).leftAdjointUniq ag
  let ρ' := (adj g').leftAdjointUniq ag'
  let loc := localizationRestrictionBaseChangeMap (Type (u + 1)) sq.toCommSq.flip
  have heq : bc sq.toCommSq =
      Functor.whiskerLeft (R f) ρ.hom ≫ loc ≫ Functor.whiskerRight ρ'.inv (R f') := by
    have hmate := SetExchangePasting.mate_bc sys sq.toCommSq
    have hm := congrArg TwoSquare.natTrans
      (mateEquiv_leftAdjointUniq (adj g') ag' (adj g) ag
        (TwoSquare.mk (R f) (localizationRestriction (Type (u + 1)) g' inferInstance)
          (localizationRestriction (Type (u + 1)) g inferInstance) (R f') loc))
    apply (mateEquiv (adj g') (adj g)).injective
    change (mateEquiv (adj g') (adj g) (TwoSquare.mk _ _ _ _ (bc sq.toCommSq))).natTrans = _
    refine hmate.trans ?_
    refine Eq.trans ?_ hm.symm
    simpa only [SetExchangePasting.rightSquare, SetExchangePasting.lowerComp,
      sys, R, dcomp, squareLowerStarIso] using
      (mateEquiv_localizationRestrictionBaseChangeMap (Type (u + 1)) sq.toCommSq.flip).symm
  have : IsIso loc :=
    isIso_localizationRestrictionBaseChangeMap_of_isPullback (Type (u + 1)) sq.flip
  rw [heq]
  infer_instance

end AlgebraicGeometry.Etale.SetExchangeTransport

namespace AlgebraicGeometry.Etale

open SetExchangeTransport
/-- Restricting the exchange arrow to one etale chart transports invertibility from its
associated local square. No covering or joint surjectivity is required here.

Source: Stacks Project, Tag 0EZR, proof of `lemma-base-change-local`, the two displayed
restriction identities and their compatibility with exchange.
(blueprint: lem-sbc-sets-local-exchange-isIso-transport).

Proof: Construct d : Y' to Y by the universal property of the global Cartesian
square. Pasting the local square with hc and cancelling the global square proves that
d, hi, h, a is Cartesian. Both c and d are etale by base change. The ordinary etale
exchange is invertible because inverse image is restriction to the localized site.
Transport that comparison from restriction to the specified set-valued inverse image
using uniqueness of left adjoints. Define the composition comparisons of these left
adjoints by conjugating direct-image composition, and prove their associativity by
conjugating direct-image associativity. The mate pasting law now writes the exchange
of the outer rectangle in two ways: first as the local exchange composed with the
invertible exchange for hc, and second as inverse image along a of the global exchange
composed with the invertible exchange for d. Cancel the comparison isomorphisms and
the exchange for d. Finally the iterated-mates identity identifies this mate definition
with the stated unit/composition/counit definition of setBaseChangeArrow. -/
theorem setBaseChangeArrow_local_isIso
    {X Y S T U V T' Y' : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g)
    (a : U ⟶ X) [AlgebraicGeometry.Etale a]
    (fi : U ⟶ V) (b : V ⟶ S) [AlgebraicGeometry.Etale b]
    (wfactor : fi ≫ b = a ≫ f)
    (c : T' ⟶ T) (gi : T' ⟶ V) (hc : IsPullback c gi g b)
    {ei : Y' ⟶ T'} {hi : Y' ⟶ U}
    (localSquare : ChosenCartesianSquare hi ei fi gi)
    (F : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (hF : IsIso (setBaseChangeArrow localSquare ((Scheme.etaleSetPullback c).obj F))) :
    IsIso ((Scheme.etaleSetPullback a).map (setBaseChangeArrow sq F)) := by
  have sqPB : IsPullback e h g f :=
    (IsPullback.of_iso_pullback sq.toCommSq sq.isoPullback sq.hom_fst sq.hom_snd).flip
  have localPB : IsPullback ei hi gi fi :=
    (IsPullback.of_iso_pullback localSquare.toCommSq localSquare.isoPullback
      localSquare.hom_fst localSquare.hom_snd).flip
  let d := sqPB.lift (ei ≫ c) (hi ≫ a) (by
    rw [Category.assoc, hc.w, ← Category.assoc, localPB.w, Category.assoc,
      wfactor, Category.assoc])
  have hd : d ≫ e = ei ≫ c := sqPB.lift_fst _ _ _
  have sqa : IsPullback d hi h a := by
    refine IsPullback.of_right ?_ (sqPB.lift_snd _ _ _) sqPB
    rw [hd, ← wfactor]
    exact localPB.paste_horiz hc
  have : AlgebraicGeometry.Etale c := MorphismProperty.of_isPullback hc.flip inferInstance
  have : AlgebraicGeometry.Etale d := MorphismProperty.of_isPullback sqa.flip inferInstance
  have hcIso : IsIso (bc hc.toCommSq) := etale_bc_isIso hc
  have haIso : IsIso (bc sqa.toCommSq) := etale_bc_isIso sqa
  have hFi : IsIso ((bc localPB.toCommSq).app ((L c).obj F)) := by
    rw [bc_app_eq localSquare]
    exact hF
  have result := SetExchangePasting.isIso_local_chart sys sqPB.toCommSq hc.toCommSq
    localPB.toCommSq sqa.toCommSq hd.symm wfactor F hcIso haIso hFi
  change IsIso ((L a).map ((bc sq.toCommSq.flip).app F)) at result
  rw [bc_app_eq sq] at result
  exact result


end AlgebraicGeometry.Etale
