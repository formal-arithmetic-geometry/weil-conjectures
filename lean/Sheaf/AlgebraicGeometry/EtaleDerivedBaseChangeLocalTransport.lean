/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N1
-/
module

public import Sheaf.AlgebraicGeometry.BaseChangeMapAbelianAndSets
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMap
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import Sheaf.CategoryTheory.DerivedExactMateCompatibility

/-!
# Transport of degreewise exchange invertibility to a single etale chart

Source: Stacks Project, Tag 0EZR, proof of `lemma-base-change-local` (2) and (3),
using Tag 0D6G (blueprint: lem-sbc-derived-local-exchange-isIso-transport).
-/

@[expose] public section

set_option autoImplicit false

universe u v
open CategoryTheory CategoryTheory.Limits Category
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.DerivedExchangePasting

variable {C : Scheme.{u} → Type v} [∀ X, Category.{u + 1} (C X)]

private structure DerivedSystem (C : Scheme.{u} → Type v) [∀ X, Category.{u + 1} (C X)] where
  L : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → (C Y ⥤ C X)
  R : ∀ {X Y : Scheme.{u}}, (X ⟶ Y) → (C X ⥤ C Y)
  adj : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), L f ⊣ R f
  ucomp : ∀ {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (_hfg : fg = f ≫ g), L fg ≅ L g ⋙ L f
  assoc : ∀ {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h),
    (ucomp f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
      Functor.whiskerRight (ucomp g h gh hgh).hom (L f) =
    (ucomp fg h fgh hfgh).hom ≫ Functor.whiskerLeft (L h) (ucomp f g fg hfg).hom

private noncomputable abbrev upperComp (sys : DerivedSystem C) {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :=
  sys.ucomp f g fg hfg

private theorem comp_assoc' (sys : DerivedSystem C) {W X Y Z : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z) (hfg : fg = f ≫ g) (hgh : gh = g ≫ h)
    (hfgh : fgh = fg ≫ h) :
    (upperComp sys f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
        Functor.whiskerRight (upperComp sys g h gh hgh).hom (sys.L f) =
      (upperComp sys fg h fgh hfgh).hom ≫
        Functor.whiskerLeft (sys.L h) (upperComp sys f g fg hfg).hom := by
  exact sys.assoc f g h fg gh fgh hfg hgh hfgh

@[reassoc]
private theorem map_comp_hom_app_upperStarComp_inv_app
    (sys : DerivedSystem C) {W X Y Z : Scheme.{u}}
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
private theorem comp_hom_app_map_upperStarComp_inv_app
    (sys : DerivedSystem C) {W X Y Z : Scheme.{u}}
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
private noncomputable def square (sys : DerivedSystem C)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) : sys.L g ⋙ sys.L f' ≅ sys.L f ⋙ sys.L g' :=
  (upperComp sys f' g (g' ≫ f) sq.w).symm ≪≫ upperComp sys g' f (g' ≫ f) rfl

private noncomputable abbrev bcSquare (sys : DerivedSystem C)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) : TwoSquare (sys.R f) (sys.L g') (sys.L g) (sys.R f') :=
  mateEquiv (sys.adj f) (sys.adj f')
    (TwoSquare.mk (sys.L g) (sys.L f) (sys.L f') (sys.L g') (square sys sq).hom)

@[irreducible]
private noncomputable def bc (sys : DerivedSystem C)
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) : sys.R f ⋙ sys.L g ⟶ sys.L g' ⋙ sys.R f' :=
  (bcSquare sys sq).natTrans

variable {X'' X' X Y'' Y' Y : Scheme.{u}} {g'' : X'' ⟶ X'} {g' : X' ⟶ X}
  {f'' : X'' ⟶ Y''} {f' : X' ⟶ Y'} {f : X ⟶ Y} {h : Y'' ⟶ Y'} {g : Y' ⟶ Y}

open scoped TwoSquare in
private theorem square_paste_horiz (sys : DerivedSystem C) (sq₁ : CommSq g' f' f g)
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
private theorem bcSquare_paste_horiz (sys : DerivedSystem C) (sq₁ : CommSq g' f' f g)
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

private theorem bc_paste_horiz_app (sys : DerivedSystem C) (sq₁ : CommSq g' f' f g)
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

private theorem isIso_paste_horiz_of_eq_homology (sys : DerivedSystem C)
    {X₁ Z₁ Y₁ Y₂ S T : Scheme.{u}} {g : T ⟶ S} {p₂ : Z₁ ⟶ S}
    {e₂ : Y₂ ⟶ T} {h₂ : Y₂ ⟶ Z₁} {p₁ : X₁ ⟶ Z₁}
    {e₁ : Y₁ ⟶ Y₂} {h₁ : Y₁ ⟶ X₁} {e₀ : Y₁ ⟶ T} {p₀ : X₁ ⟶ S}
    (sq₂ : CommSq e₂ h₂ g p₂) (sq₁ : CommSq e₁ h₁ h₂ p₁)
    (sq₀ : CommSq e₀ h₁ g p₀) (he : e₁ ≫ e₂ = e₀) (hp : p₁ ≫ p₂ = p₀)
    (F : C T) {D : Type*} [Category D] (H : C X₁ ⥤ D)
    (hF₂ : IsIso ((bc sys sq₂).app F))
    (hF₁ : IsIso (H.map ((bc sys sq₁).app ((sys.L e₂).obj F)))) :
    IsIso (H.map ((bc sys sq₀).app F)) := by
  subst he hp
  rw [bc_paste_horiz_app sys sq₂ sq₁ sq₀ F,
    Functor.map_comp, Functor.map_comp, Functor.map_comp]
  infer_instance

end AlgebraicGeometry.Etale.DerivedExchangePasting

namespace AlgebraicGeometry.Etale.DerivedExchangeTransport
private noncomputable def L {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  D(upperStar AddCommGrpCat.{u + 1} f)
private noncomputable def R {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  R(lowerStar AddCommGrpCat.{u + 1} f)
private noncomputable def adj {X Y : Scheme.{u}} (f : X ⟶ Y) : L f ⊣ R f :=
  mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
private noncomputable def comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) : L fg ≅ L g ⋙ L f :=
  Functor.mapDerivedCategoryNatIso (upperStarComp AddCommGrpCat.{u + 1} f g fg hfg) ≪≫
    Functor.mapDerivedCategoryCompIso _ _

private theorem comp_assoc {W X Y Z : Scheme.{u}}
    (f : W ⟶ X) (g : X ⟶ Y)
    (h : Y ⟶ Z)
    (fg : W ⟶ Y) (gh : X ⟶ Z) (fgh : W ⟶ Z)
    (hfg : fg = f ≫ g) (hgh : gh = g ≫ h) (hfgh : fgh = fg ≫ h) :
    (comp f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])).hom ≫
      Functor.whiskerRight (comp g h gh hgh).hom (L f) =
    (comp fg h fgh hfgh).hom ≫ Functor.whiskerLeft (L h) (comp f g fg hfg).hom := by
  let A := AddCommGrpCat.{u + 1}
  let α₁ := upperStarComp A f gh fgh (by rw [hfgh, hfg, hgh, Category.assoc])
  let α₂ := upperStarComp A g h gh hgh
  let α₃ := upperStarComp A fg h fgh hfgh
  let α₄ := upperStarComp A f g fg hfg
  have heq : α₁ ≪≫ Functor.isoWhiskerRight α₂ (upperStar A f) =
      α₃ ≪≫ Functor.isoWhiskerLeft (upperStar A h) α₄ := by
    ext : 1
    exact upperStarComp_assoc' A f g h fg gh fgh hfg hgh hfgh
  have hmap := congrArg (fun e => (Functor.mapDerivedCategoryNatIso e).hom) heq
  simp only [Functor.mapDerivedCategoryNatIso_trans] at hmap
  simp only [comp, Iso.trans_hom, Functor.whiskerRight_comp, Functor.whiskerLeft_comp,
    Category.assoc]
  simp only [L]
  change (Functor.mapDerivedCategoryNatIso α₁).hom ≫ _ =
    (Functor.mapDerivedCategoryNatIso α₃).hom ≫ _
  rw [← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerRight
      α₂ (upperStar A f)),
    ← reassoc_of% (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft
      (upperStar A h) α₄)]
  rw [← (Functor.mapDerivedCategoryCompIso_assoc
    (upperStar A h) (upperStar A g) (upperStar A f))]
  rw [← Category.assoc, hmap, Category.assoc]

private noncomputable def sys : DerivedExchangePasting.DerivedSystem
    (fun X : Scheme.{u} => DerivedCategory
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) where
  L := @L
  R := @R
  adj := @adj
  ucomp := @comp
  assoc := @comp_assoc

private noncomputable abbrev bc
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :=
  DerivedExchangePasting.bc sys sq

private theorem bc_app_eq
    {X Y S T : Scheme.{u}} {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (bc sq.toCommSq.flip).app K = abelianDerivedBaseChangeArrow sq K := by
  unfold bc DerivedExchangePasting.bc DerivedExchangePasting.bcSquare
    DerivedExchangePasting.square DerivedExchangePasting.upperComp sys comp adj
  rfl

private noncomputable def dcomp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) : R f ⋙ R g ≅ R fg :=
  Functor.rightDerivedFunctorCompIso' (lowerStar AddCommGrpCat.{u + 1} f)
    (lowerStar AddCommGrpCat.{u + 1} g)
    (lowerStarComp AddCommGrpCat.{u + 1} f g fg hfg)

private theorem conjugate_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    conjugateIsoEquiv ((adj g).comp (adj f)) (adj fg) (comp f g fg hfg) =
      dcomp f g fg hfg := by
  ext : 1
  exact (Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g)
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} fg)
    _ (upperStarComp AddCommGrpCat.{u + 1} f g fg hfg)
    (congrArg Iso.hom
      (conjugateIsoEquiv_upperStarComp AddCommGrpCat.{u + 1} f g fg hfg)).symm).symm

private theorem mate_bc
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq g' f' f g) :
    (mateEquiv (adj g') (adj g) (TwoSquare.mk _ _ _ _ (bc sq))).natTrans =
      (dcomp g' f (g' ≫ f) rfl).hom ≫ (dcomp f' g (g' ≫ f) sq.w).inv := by
  unfold bc DerivedExchangePasting.bc DerivedExchangePasting.bcSquare
  dsimp only [sys]
  rw [iterated_mateEquiv_conjugateEquiv]
  simp only [DerivedExchangePasting.square, Iso.trans_hom, Iso.symm_hom,
    DerivedExchangePasting.upperComp]
  rw [← conjugateEquiv_comp _ (adj (g' ≫ f))]
  congr 1
  · exact congrArg Iso.hom (conjugate_comp g' f (g' ≫ f) rfl)
  · exact congrArg Iso.inv (conjugate_comp f' g (g' ≫ f) sq.w)

private theorem leftExact_etaleLowerShriek {W X : Scheme.{u}} (v : W ⟶ X)
    (hv : AlgebraicGeometry.Etale v) :
    PreservesFiniteLimits (etaleLowerShriek AddCommGrpCat.{u + 1} v hv) := by
  have heq : etaleLowerShriek AddCommGrpCat.{u + 1} v hv =
      sheafToPresheaf W.smallEtaleTopology AddCommGrpCat.{u + 1} ⋙
        (MorphismProperty.Over.map ⊤ hv).op.lan ⋙
          presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} := rfl
  have : PreservesFiniteLimits ((MorphismProperty.Over.map ⊤ hv).op.lan :
      (W.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤ X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    SmallSite.preservesFiniteLimits_op_lan_overMap_of_isGrothendieckAbelian _ hv
  rw [heq]
  exact comp_preservesFiniteLimits _ _

private theorem etale_bc_isIso
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g)
    [AlgebraicGeometry.Etale g] : IsIso (bc sq.toCommSq) := by
  let A := AddCommGrpCat.{u + 1}
  have : AlgebraicGeometry.Etale g' := MorphismProperty.of_isPullback sq.flip inferInstance
  have : PreservesFiniteLimits (etaleLowerShriek A g' inferInstance) :=
    leftExact_etaleLowerShriek g' inferInstance
  have : (etaleLowerShriek A g' inferInstance).IsLeftAdjoint :=
    (etaleLowerShriekUpperStarAdjunction A g' inferInstance).isLeftAdjoint
  have : (etaleLowerShriek A g' inferInstance).Additive :=
    (etaleLowerShriekUpperStarAdjunction A g' inferInstance).left_adjoint_additive
  have : (upperStar A g').PreservesKInjectiveComplexes :=
    (etaleLowerShriekUpperStarAdjunction A g' inferInstance).preservesKInjectiveComplexes
  let F := lowerStar A f
  let K := lowerStar A f'
  let G := upperStar A g
  let H := upperStar A g'
  let P := lowerStar A g'
  let Q := lowerStar A g
  let ah := upperStarLowerStarAdjunction A g'
  let ag := upperStarLowerStarAdjunction A g
  let α := lowerStarComp A g' f (g' ≫ f) rfl
  let β := lowerStarComp A f' g (g' ≫ f) sq.w
  let e : P ⋙ F ≅ K ⋙ Q := α ≪≫ β.symm
  let ed : R g' ⋙ R f ≅ R f' ⋙ R g :=
    dcomp g' f (g' ≫ f) rfl ≪≫ (dcomp f' g (g' ≫ f) sq.w).symm
  have heq : (mateEquiv (adj g') (adj g)
      (TwoSquare.mk _ _ _ _ (bc sq.toCommSq))).natTrans = ed.hom := mate_bc sq.toCommSq
  have : IsIso (baseChangeMap A sq.toCommSq) :=
    isIso_baseChangeMap_flip_of_isPullback A sq.flip
  let m : F ⋙ G ≅ H ⋙ K := asIso (baseChangeMap A sq.toCommSq)
  have hm : m.hom = ((mateEquiv ah ag).symm
      (TwoSquare.mk _ _ _ _ e.hom)).natTrans := by
    have hmate := mateEquiv_baseChangeSquare A sq.toCommSq
    have he : mateEquiv ah ag (TwoSquare.mk _ _ _ _ m.hom) =
        TwoSquare.mk _ _ _ _ e.hom := hmate
    exact congrArg TwoSquare.natTrans ((mateEquiv ah ag).eq_symm_apply.mpr he)
  have hed : Functor.rightDerivedFunctorCompUnit P F ≫
      Functor.whiskerLeft DerivedCategory.Qh ed.hom =
    Functor.whiskerRight (NatTrans.mapHomotopyCategory e.hom (.up ℤ))
      DerivedCategory.Qh ≫ Functor.rightDerivedFunctorCompUnit K Q := by
    have hα : Functor.rightDerivedFunctorCompUnit P F ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.rightDerivedFunctorCompIso' P F α).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory α.hom (.up ℤ))
        DerivedCategory.Qh ≫ (lowerStar A (g' ≫ f)).rightDerivedFunctorUnit := by
      have hc : (P ⋙ F).rightDerivedFunctorUnit ≫
          Functor.whiskerLeft DerivedCategory.Qh
            (Functor.rightDerivedFunctorCompIso P F).hom =
          Functor.rightDerivedFunctorCompUnit P F := by
        simp [Functor.rightDerivedFunctorCompIso]
      rw [← hc, Category.assoc, ← Functor.whiskerLeft_comp]
      simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom]
      rw [Iso.hom_inv_id_assoc]
      exact Functor.rightDerivedNatTrans_fac _ _ _ _
        (HomotopyCategory.quasiIso _ (.up ℤ)) _
    have hβ : Functor.rightDerivedFunctorCompUnit K Q ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.rightDerivedFunctorCompIso' K Q β).hom =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory β.hom (.up ℤ))
        DerivedCategory.Qh ≫ (lowerStar A (g' ≫ f)).rightDerivedFunctorUnit := by
      have hc : (K ⋙ Q).rightDerivedFunctorUnit ≫
          Functor.whiskerLeft DerivedCategory.Qh
            (Functor.rightDerivedFunctorCompIso K Q).hom =
          Functor.rightDerivedFunctorCompUnit K Q := by
        simp [Functor.rightDerivedFunctorCompIso]
      rw [← hc, Category.assoc, ← Functor.whiskerLeft_comp]
      simp only [Functor.rightDerivedFunctorCompIso', Iso.trans_hom, Iso.symm_hom]
      rw [Iso.hom_inv_id_assoc]
      exact Functor.rightDerivedNatTrans_fac _ _ _ _
        (HomotopyCategory.quasiIso _ (.up ℤ)) _
    have hiβ : (lowerStar A (g' ≫ f)).rightDerivedFunctorUnit ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.rightDerivedFunctorCompIso' K Q β).inv =
      Functor.whiskerRight (NatTrans.mapHomotopyCategory β.inv (.up ℤ))
        DerivedCategory.Qh ≫ Functor.rightDerivedFunctorCompUnit K Q := by
      have : IsIso (NatTrans.mapHomotopyCategory β.hom (.up ℤ)) := by
        refine ⟨⟨NatTrans.mapHomotopyCategory β.inv (.up ℤ), ?_, ?_⟩⟩
        · rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
            NatTrans.mapHomotopyCategory_id]
        · rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
            NatTrans.mapHomotopyCategory_id]
      apply (cancel_epi (Functor.whiskerRight
        (NatTrans.mapHomotopyCategory β.hom (.up ℤ)) DerivedCategory.Qh)).1
      rw [← Category.assoc, ← hβ, Category.assoc, ← Functor.whiskerLeft_comp,
        Iso.hom_inv_id, Functor.whiskerLeft_id', Category.comp_id,
        ← Category.assoc, ← Functor.whiskerRight_comp,
        ← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
        NatTrans.mapHomotopyCategory_id, Functor.whiskerRight_id', Category.id_comp]
    simp only [ed, Iso.trans_hom, Iso.symm_hom, Functor.whiskerLeft_comp]
    change Functor.rightDerivedFunctorCompUnit P F ≫
      Functor.whiskerLeft DerivedCategory.Qh
        (Functor.rightDerivedFunctorCompIso' P F α).hom ≫
        Functor.whiskerLeft DerivedCategory.Qh
          (Functor.rightDerivedFunctorCompIso' K Q β).inv = _
    rw [← Category.assoc, hα, Category.assoc, hiβ, ← Category.assoc,
      ← Functor.whiskerRight_comp, ← NatTrans.mapHomotopyCategory_comp]
    rfl
  have hcomp := Functor.exactMateComparison_eq F K G H P Q ah ag e m hm ed hed
  have hb : bc sq.toCommSq = (Functor.exactMateComparison F K G H m).hom := by
    apply (mateEquiv (adj g') (adj g)).injective
    change (mateEquiv (adj g') (adj g)
      (TwoSquare.mk _ _ _ _ (bc sq.toCommSq))).natTrans = _
    rw [heq, hcomp]
    exact congrArg TwoSquare.natTrans ((mateEquiv (adj g') (adj g)).apply_symm_apply _).symm
  rw [hb]
  infer_instance

end AlgebraicGeometry.Etale.DerivedExchangeTransport

namespace AlgebraicGeometry.Etale

open DerivedExchangeTransport

/-- The map on one cohomology sheaf of the global exchange becomes invertible on a
single etale chart whenever the associated local exchange is invertible in that degree.
This is a single-chart comparison, without any covering or boundedness condition.

Source: Stacks Project, Tag 0EZR, proof of `lemma-base-change-local` (2), (3), with
Tag 0D6G for unbounded derived direct-image restriction.
(blueprint: lem-sbc-derived-local-exchange-isIso-transport).

Proof: Construct d : Y' to Y by the global pullback property. Pasting and
cancellation show that the square d, hi, h, a is Cartesian. Both d and c are etale.
For an etale morphism, extension by zero is left Kan extension followed by
sheafification; exact coproducts make this left adjoint exact. Its right adjoint,
etale inverse image, therefore preserves K-injectives. Ordinary etale exchange is
invertible by the localization comparison. The exact-adjoint derived-mate theorem
transports it to the unbounded categories. Its determining composite-unit equation
follows from the two right-derived composition comparisons; invert the second
comparison and cancel the ordinary comparison isomorphism. Conjugacy identifies the
derived square comparison with that used in abelianDerivedBaseChangeTransformation.

The composition isomorphisms of exact derived inverse images satisfy associativity:
apply mapDerivedCategoryNatIso to the ordinary coherence equality, then its two
whiskering laws and the associativity of mapDerivedCategoryCompIso. Thus the horizontal
mate-pasting identity applies. Compute the outer rectangle first through hc and the
local square, then through the global square and the square d, hi, h, a. Apply degree-q
homology to both decompositions and cancel all invertible factors, including the two
etale exchanges. Finally use the exact inverse-image homology comparison to identify
H^q of D(a inverse image) with a inverse image of H^q. This uses no bound on K or q,
no cover detection, and no information about the other cohomological degrees. -/
theorem abelianDerivedBaseChangeArrow_local_homology_isIso
    {X Y S T U V T' Y' : Scheme.{u}}
    {h : Y ⟶ X} {e : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (sq : ChosenCartesianSquare h e f g)
    (a : U ⟶ X) [AlgebraicGeometry.Etale a]
    (fi : U ⟶ V) (b : V ⟶ S) [AlgebraicGeometry.Etale b]
    (wfactor : fi ≫ b = a ≫ f)
    (c : T' ⟶ T) (gi : T' ⟶ V) (hc : IsPullback c gi g b)
    {ei : Y' ⟶ T'} {hi : Y' ⟶ U}
    (localSquare : ChosenCartesianSquare hi ei fi gi)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) (q : ℤ)
    (hK : IsIso ((DerivedCategory.homologyFunctor _ q).map
      (abelianDerivedBaseChangeArrow localSquare
        (D(upperStar AddCommGrpCat.{u + 1} c).obj K)))) :
    IsIso ((upperStar AddCommGrpCat.{u + 1} a).map
      ((DerivedCategory.homologyFunctor _ q).map (abelianDerivedBaseChangeArrow sq K))) := by
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
  let H := DerivedCategory.homologyFunctor
    (Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) q
  have hKi : IsIso (H.map ((bc localPB.toCommSq).app ((L c).obj K))) := by
    rw [bc_app_eq localSquare]
    exact hK
  have hout := DerivedExchangePasting.isIso_paste_horiz_of_eq_homology sys
    hc.toCommSq localPB.toCommSq (sqa.toCommSq.horiz_comp sqPB.toCommSq)
    hd.symm wfactor K H (by infer_instance) hKi
  rw [DerivedExchangePasting.bc_paste_horiz_app sys sqPB.toCommSq sqa.toCommSq,
    Functor.map_comp, Functor.map_comp, Functor.map_comp] at hout
  change IsIso (
    H.map ((DerivedExchangePasting.upperComp sys a f (a ≫ f) rfl).hom.app ((sys.R g).obj K)) ≫
      H.map ((sys.L a).map ((bc sqPB.toCommSq).app K)) ≫
      H.map ((bc sqa.toCommSq).app ((sys.L e).obj K)) ≫
      H.map ((sys.R hi).map
        ((DerivedExchangePasting.upperComp sys d e (d ≫ e) rfl).inv.app K))) at hout
  have hv : IsIso (H.map ((sys.L a).map ((bc sqPB.toCommSq).app K))) := by
    let _ : IsIso (
        H.map ((DerivedExchangePasting.upperComp sys a f (a ≫ f) rfl).hom.app ((sys.R g).obj K)) ≫
          H.map ((sys.L a).map ((bc sqPB.toCommSq).app K)) ≫
          H.map ((bc sqa.toCommSq).app ((sys.L e).obj K)) ≫
          H.map ((sys.R hi).map
            ((DerivedExchangePasting.upperComp sys d e (d ≫ e) rfl).inv.app K))) := hout
    have htail : IsIso (
        H.map ((sys.L a).map ((bc sqPB.toCommSq).app K)) ≫
          H.map ((bc sqa.toCommSq).app ((sys.L e).obj K)) ≫
          H.map ((sys.R hi).map
            ((DerivedExchangePasting.upperComp sys d e (d ≫ e) rfl).inv.app K))) :=
      IsIso.of_isIso_comp_left
        (H.map ((DerivedExchangePasting.upperComp sys a f (a ≫ f) rfl).hom.app
          ((sys.R g).obj K))) _
    have hmid : IsIso (
        (H.map ((sys.L a).map ((bc sqPB.toCommSq).app K)) ≫
          H.map ((bc sqa.toCommSq).app ((sys.L e).obj K))) ≫
          H.map ((sys.R hi).map
            ((DerivedExchangePasting.upperComp sys d e (d ≫ e) rfl).inv.app K))) := by
      simpa only [Category.assoc] using htail
    let _ : IsIso (
        (H.map ((sys.L a).map ((bc sqPB.toCommSq).app K)) ≫
          H.map ((bc sqa.toCommSq).app ((sys.L e).obj K))) ≫
          H.map ((sys.R hi).map
            ((DerivedExchangePasting.upperComp sys d e (d ≫ e) rfl).inv.app K))) := hmid
    have hleft : IsIso (
        H.map ((sys.L a).map ((bc sqPB.toCommSq).app K)) ≫
          H.map ((bc sqa.toCommSq).app ((sys.L e).obj K))) :=
      IsIso.of_isIso_comp_right
        (H.map ((sys.L a).map ((bc sqPB.toCommSq).app K)) ≫
          H.map ((bc sqa.toCommSq).app ((sys.L e).obj K)))
        (H.map ((sys.R hi).map
          ((DerivedExchangePasting.upperComp sys d e (d ≫ e) rfl).inv.app K)))
    let _ : IsIso (
        H.map ((sys.L a).map ((bc sqPB.toCommSq).app K)) ≫
          H.map ((bc sqa.toCommSq).app ((sys.L e).obj K))) := hleft
    exact IsIso.of_isIso_comp_right
      (H.map ((sys.L a).map ((bc sqPB.toCommSq).app K)))
      (H.map ((bc sqa.toCommSq).app ((sys.L e).obj K)))
  change IsIso (H.map ((L a).map ((bc sq.toCommSq.flip).app K))) at hv
  rw [bc_app_eq sq] at hv
  exact (NatIso.isIso_map_iff
    ((upperStar AddCommGrpCat.{u + 1} a).mapDerivedCategoryHomologyFunctorIso q)
    (abelianDerivedBaseChangeArrow sq K)).2 hv


end AlgebraicGeometry.Etale
