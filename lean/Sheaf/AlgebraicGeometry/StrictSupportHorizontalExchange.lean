/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q46
-/
module

public import Sheaf.AlgebraicGeometry.StrictTowerCompositionMaps
public import Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus
public import Sheaf.AlgebraicGeometry.StrictConstantTowerOperations
public import Sheaf.AlgebraicGeometry.StrictTowerOpenExtension
public import Sheaf.Paper.ProjectionCompactification
public import WeilConjectures.Compactification.BaseChange
import Sheaf.AlgebraicGeometry.StrictTowerPullbackSquarePasting
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import all Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus

/-!
# Horizontal exchange for strict compact support

Source: Stacks Project, Tags 07A7 and 0E47, remarks `remark-base-change` and
`remark-compose-base-change-horizontal`; the strict proper/open two-factor consequence
of the blueprint coherence sentence (blueprint: lem-cbc-strict-support-horizontal-exchange).

All functors act on the ordinary unbounded derived categories of strict towers.
Cartesian diagrams express the supplied base-changed compactifications, independently
of the presentation of their fibre products. In particular they include
`Compactification.baseChange` and its iterated base change.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale.StrictTower

variable (B : Type (u + 1)) [CommRing B]

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] G R J adj gComp gId beta squareG towers_hasDerivedCategory

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem exchange_comp {V V₁ V₂ T T₁ T₂ : Scheme.{u}}
    (p : V ⟶ T) (p₁ : V₁ ⟶ T₁) (p₂ : V₂ ⟶ T₂)
    (g : T₁ ⟶ T) (h : T₂ ⟶ T₁) (a : V₁ ⟶ V) (b : V₂ ⟶ V₁)
    (w₁ : a ≫ p = p₁ ≫ g) (w₂ : b ≫ p₁ = p₂ ≫ h)
    (w : (b ≫ a) ≫ p = p₂ ≫ (h ≫ g)) (N : Derived B V) :
    (exchange B (b ≫ a) p₂ p (h ≫ g) w).app N =
      (gComp B h g).hom.app ((R B p).obj N) ≫
        (G B h).map ((exchange B a p₁ p g w₁).app N) ≫
        (exchange B b p₂ p₁ h w₂).app ((G B a).obj N) ≫
        (R B p₂).map ((gComp B b a).inv.app N) := by
  let α := TwoSquare.mk _ _ _ _ (squareG B a p₁ p g w₁).hom
  let β := TwoSquare.mk _ _ _ _ (squareG B b p₂ p₁ h w₂).hom
  have hs : TwoSquare.mk _ _ _ _ (squareG B (b ≫ a) p₂ p (h ≫ g) w).hom =
      ((α.hComp β).whiskerTop (gComp B h g).hom).whiskerBottom
        (gComp B b a).inv := by
    ext M
    have hi := squareG_pasting_inv B p p₁ p₂ g h a b w₁ w₂ w M
    simp only [α, β, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      TwoSquare.hComp, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Functor.comp_obj, Category.assoc]
    change (squareG B (b ≫ a) p₂ p (h ≫ g) w).hom.app M =
      (G B p₂).map ((gComp B h g).hom.app M) ≫
        (squareG B b p₂ p₁ h w₂).hom.app ((G B g).obj M) ≫
        (G B b).map ((squareG B a p₁ p g w₁).hom.app M) ≫
        (gComp B b a).inv.app ((G B p).obj M)
    apply (cancel_epi ((squareG B (b ≫ a) p₂ p (h ≫ g) w).inv.app M)).1
    rw [Iso.inv_hom_id_app]
    rw [← reassoc_of% hi]
    rw [Iso.inv_hom_id_app_assoc, ← (G B b).map_comp_assoc, Iso.inv_hom_id_app]
    dsimp only [Functor.comp_obj, Functor.id_obj]
    rw [(G B b).map_id, Category.id_comp, Iso.hom_inv_id_app]
  have hm := congrArg (mateEquiv (adj B p) (adj B p₂)) hs
  rw [mateEquiv_whiskerTop_whiskerBottom,
    mateEquiv_vcomp (adj B p) (adj B p₁) (adj B p₂)] at hm
  have he := congr_app hm N
  simp only [TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
    TwoSquare.vComp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Functor.comp_obj, Category.assoc] at he
  change (exchange B (b ≫ a) p₂ p (h ≫ g) w).app N =
    (gComp B h g).hom.app ((R B p).obj N) ≫
      (G B h).map ((exchange B a p₁ p g w₁).app N) ≫
      (exchange B b p₂ p₁ h w₂).app ((G B a).obj N) ≫
      (R B p₂).map ((gComp B b a).inv.app N) at he
  simpa only [Category.assoc] using he

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem exchange_id {V T : Scheme.{u}} (p : V ⟶ T)
    (w : (𝟙 V) ≫ p = p ≫ (𝟙 T)) (N : Derived B V) :
    (exchange B (𝟙 V) p p (𝟙 T) w).app N ≫
        (R B p).map ((gId B V).hom.app N) =
      (gId B T).hom.app ((R B p).obj N) := by
  have hs : TwoSquare.mk _ _ _ _ (squareG B (𝟙 V) p p (𝟙 T) w).hom =
      ((TwoSquare.hId (G B p)).whiskerTop (gId B T).hom).whiskerBottom
        (gId B V).inv := by
    ext M
    have hi := squareG_id B p w M
    simp only [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.hId,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app, Category.assoc]
    dsimp only [Functor.comp_obj, Functor.id_obj]
    simp only [Category.id_comp]
    change (squareG B (𝟙 V) p p (𝟙 T) w).hom.app M =
      (G B p).map ((gId B T).hom.app M) ≫
        (gId B V).inv.app ((G B p).obj M)
    apply (cancel_epi ((squareG B (𝟙 V) p p (𝟙 T) w).inv.app M)).1
    rw [Iso.inv_hom_id_app, ← Category.assoc, hi, Iso.hom_inv_id_app]
    rfl
  have hm := congrArg (mateEquiv (adj B p) (adj B p)) hs
  rw [mateEquiv_whiskerTop_whiskerBottom] at hm
  have he := congr_app hm N
  change (exchange B (𝟙 V) p p (𝟙 T) w).app N =
    ((gId B T).hom.app ((R B p).obj N) ≫
      (mateEquiv (adj B p) (adj B p) (TwoSquare.hId (G B p))).app N) ≫
      (R B p).map ((gId B V).inv.app N) at he
  rw [he]
  have hmId := congr_app (mateEquiv_unitors (adj B p)) N
  change (mateEquiv (adj B p) (adj B p) (TwoSquare.hId (G B p))).app N =
    𝟙 _ ≫ 𝟙 _ at hmId
  rw [hmId]
  simp only [Category.comp_id, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj, Functor.id_obj]
  rw [(R B p).map_id, Category.id_comp, Category.comp_id]

private theorem beta_rearrange {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y : C} {Z A B₀ : D} (e : X ≅ Y)
    (v : Z ⟶ F.obj X) (a : Z ⟶ A) (b : A ⟶ B₀) (c : B₀ ⟶ F.obj Y)
    (hv : a ≫ b ≫ c = v ≫ F.map e.hom) :
    v = a ≫ b ≫ c ≫ F.map e.inv := by
  have hp := ((F.mapIso e).eq_comp_inv).2 hv.symm
  simpa only [Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc] using hp

private theorem twoFactor_pasting
    {C C₁ C₂ D D₁ D₂ E E₁ E₂ : Type*}
    [Category C] [Category C₁] [Category C₂] [Category D] [Category D₁] [Category D₂]
    [Category E] [Category E₁] [Category E₂]
    (J₀ : C ⥤ D) (J₁ : C₁ ⥤ D₁) (J₂ : C₂ ⥤ D₂)
    (R₀ : D ⥤ E) (R₁ : D₁ ⥤ E₁) (R₂ : D₂ ⥤ E₂)
    (g : E ⥤ E₁) (h : E₁ ⥤ E₂) (gh : E ⥤ E₂)
    (a : D ⥤ D₁) (b : D₁ ⥤ D₂) (ba : D ⥤ D₂)
    (x : C ⥤ C₁) (y : C₁ ⥤ C₂) (yx : C ⥤ C₂)
    (cg : gh ≅ g ⋙ h) (ca : ba ≅ a ⋙ b) (cx : yx ≅ x ⋙ y)
    (e₀ : R₀ ⋙ g ⟶ a ⋙ R₁) (e₁ : R₁ ⋙ h ⟶ b ⋙ R₂)
    (e : R₀ ⋙ gh ⟶ ba ⋙ R₂)
    (β₀ : J₀ ⋙ a ≅ x ⋙ J₁) (β₁ : J₁ ⋙ b ≅ y ⋙ J₂) (β : J₀ ⋙ ba ≅ yx ⋙ J₂)
    (he : ∀ N, e.app N = cg.hom.app (R₀.obj N) ≫ h.map (e₀.app N) ≫
      e₁.app (a.obj N) ≫ R₂.map (ca.inv.app N))
    (hβ : ∀ M, β.hom.app M = ca.hom.app (J₀.obj M) ≫ b.map (β₀.hom.app M) ≫
      β₁.hom.app (x.obj M) ≫ J₂.map (cx.inv.app M)) :
    Functor.whiskerLeft J₀ e ≫ Functor.whiskerRight β.hom R₂ =
      Functor.whiskerLeft (J₀ ⋙ R₀) cg.hom ≫
        Functor.whiskerRight
          (Functor.whiskerLeft J₀ e₀ ≫ Functor.whiskerRight β₀.hom R₁) h ≫
        Functor.whiskerLeft x
          (Functor.whiskerLeft J₁ e₁ ≫ Functor.whiskerRight β₁.hom R₂) ≫
        Functor.whiskerRight cx.inv (J₂ ⋙ R₂) := by
  apply NatTrans.ext
  funext M
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map]
  rw [he, hβ]
  simp only [Functor.map_comp, Category.assoc]
  rw [← R₂.map_comp_assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  rw [R₂.map_id, Category.id_comp]
  have hn := e₁.naturality (β₀.hom.app M)
  dsimp only [Functor.comp_map] at hn
  rw [← reassoc_of% hn]

attribute [local irreducible] exchange
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Identity base change is identity under the canonical pullback identity comparisons.
A quasi-compact open in a compactification is exactly the separated finite-type setting.
Source: Stacks, Tags 07A7 and 0E47, and the blueprint coherence sentence
(blueprint: lem-cbc-strict-support-horizontal-exchange).
Proof: use `def-weil-pbc-adjunction-mate` and clause 4 of `lem-weil-pbc-mate-pasting`:
the mate of the identity pullback square is identity after the normalized comparisons
of `def-cbc-strict-constant-tower-operations`. The identity clause of
`lem-cbc-strict-tower-proper-open-calculus` identifies the open factor with identity.
Their whiskered composite is the stated identity comparison. This takes place on
unbounded derived strict towers, without evaluation or coefficient restrictions. -/
theorem supportExchange_id {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) [QuasiCompact c.i] :
    compositionE B c c (𝟙 X) (𝟙 Y) (𝟙 c.Z)
        IsPullback.of_id_fst.w IsPullback.of_id_fst.w IsPullback.of_id_fst ≫
      Functor.whiskerRight (gId B X).hom (compositionF B c) =
    Functor.whiskerLeft (compositionF B c) (gId B Y).hom := by
  ext M
  dsimp only [compositionE, compositionF, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_map]
  rw [Category.assoc, ← (R B c.g).map_comp,
    beta_id B c.i IsPullback.of_id_fst.w IsPullback.of_id_fst M]
  exact exchange_id B c.g IsPullback.of_id_fst.w ((J B c.i).obj M)

attribute [-instance] CategoryTheory.catToReflQuiver in
/-- Horizontal pasting for both the actual two-factor exchange and its specified
transpose-normalized open factor. The equalities are of natural transformations,
so apply naturally to every unbounded derived strict tower.
Source: Stacks, Tags 07A7 and 0E47, and the blueprint coherence sentence
(blueprint: lem-cbc-strict-support-horizontal-exchange).
Proof:
1. Apply `lem-cbc-strict-tower-pullback-square-pasting` to the proper vertical maps
   `c.g`, `c₁.g`, `c₂.g` and the transverse maps `g`, `h`, `a`, `b`. Clause 1 of
   `lem-weil-pbc-mate-pasting`, for the normalized `adj` adjunctions, expresses the
   outer proper exchange as the paste of the two exchanges with `gComp` comparisons.
2. The successive-base-change clause of `lem-cbc-strict-tower-proper-open-calculus`
   gives exactly the second equality, since `beta` is the inverse open-unit transpose.
   Its finite-origin condition pertains only to proper/open invertibility, not beta.
3. Substitute these identities into the defining proper/open composite. The two
   consecutive ambient pullback compositors cancel under `R B c₂.g`. Naturality of
   the second proper exchange at the first beta component interchanges the middle
   factors. Regrouping by associativity and functoriality gives the first equality.
4. Naturality is built into the existing `compositionE`, which is a composite of whiskered
   natural transformations. The identity case is `supportExchange_id`. None of the
   steps uses evaluation, finite origin, boundedness, completeness, or faithfulness. -/
theorem supportExchange_comp {X X₁ X₂ Y Y₁ Y₂ : Scheme.{u}}
    {f : X ⟶ Y} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂}
    (c : Compactification f) (c₁ : Compactification f₁) (c₂ : Compactification f₂)
    [QuasiCompact c.i]
    (g : Y₁ ⟶ Y) (h : Y₂ ⟶ Y₁)
    (a : c₁.Z ⟶ c.Z) (b : c₂.Z ⟶ c₁.Z) (gX : X₁ ⟶ X) (hX : X₂ ⟶ X₁)
    (sp₁ : IsPullback a c₁.g c.g g) (sp₂ : IsPullback b c₂.g c₁.g h)
    (sj₁ : IsPullback gX c₁.i c.i a) (sj₂ : IsPullback hX c₂.i c₁.i b) :
    (compositionE B c c₂ (hX ≫ gX) (h ≫ g) (b ≫ a)
        (sj₂.paste_horiz sj₁).w (sp₂.paste_horiz sp₁).w (sj₂.paste_horiz sj₁) =
      Functor.whiskerLeft (compositionF B c) (gComp B h g).hom ≫
        Functor.whiskerRight (compositionE B c c₁ gX g a sj₁.w sp₁.w sj₁) (G B h) ≫
        Functor.whiskerLeft (G B gX) (compositionE B c₁ c₂ hX h b sj₂.w sp₂.w sj₂) ≫
        Functor.whiskerRight (gComp B hX gX).inv (compositionF B c₂)) ∧
    ((beta B (hX ≫ gX) c₂.i c.i (b ≫ a)
          (sj₂.paste_horiz sj₁).w (sj₂.paste_horiz sj₁)).hom =
      Functor.whiskerLeft (J B c.i) (gComp B b a).hom ≫
        Functor.whiskerRight (beta B gX c₁.i c.i a sj₁.w sj₁).hom (G B b) ≫
        Functor.whiskerLeft (G B gX) (beta B hX c₂.i c₁.i b sj₂.w sj₂).hom ≫
        Functor.whiskerRight (gComp B hX gX).inv (J B c₂.i)) := by
  have hb (M : Derived B X) := beta_comp B c.i c₁.i c₂.i a b gX hX
    sj₁.w sj₂.w (sj₂.paste_horiz sj₁).w sj₁ sj₂ (sj₂.paste_horiz sj₁) M
  have hb' (M : Derived B X) :
      (beta B (hX ≫ gX) c₂.i c.i (b ≫ a)
        (sj₂.paste_horiz sj₁).w (sj₂.paste_horiz sj₁)).hom.app M =
      (gComp B b a).hom.app ((J B c.i).obj M) ≫
        (G B b).map ((beta B gX c₁.i c.i a sj₁.w sj₁).hom.app M) ≫
        (beta B hX c₂.i c₁.i b sj₂.w sj₂).hom.app ((G B gX).obj M) ≫
        (J B c₂.i).map ((gComp B hX gX).inv.app M) := by
    exact beta_rearrange (J B c₂.i)
      (Iso.mk ((gComp B hX gX).hom.app M) ((gComp B hX gX).inv.app M)
        (Iso.hom_inv_id_app _ M) (Iso.inv_hom_id_app _ M)) _ _ _ _ (hb M)
  constructor
  · exact twoFactor_pasting (J B c.i) (J B c₁.i) (J B c₂.i)
      (R B c.g) (R B c₁.g) (R B c₂.g)
      (G B g) (G B h) (G B (h ≫ g)) (G B a) (G B b) (G B (b ≫ a))
      (G B gX) (G B hX) (G B (hX ≫ gX))
      (gComp B h g) (gComp B b a) (gComp B hX gX)
      (exchange B a c₁.g c.g g sp₁.w) (exchange B b c₂.g c₁.g h sp₂.w)
      (exchange B (b ≫ a) c₂.g c.g (h ≫ g) (sp₂.paste_horiz sp₁).w)
      (beta B gX c₁.i c.i a sj₁.w sj₁) (beta B hX c₂.i c₁.i b sj₂.w sj₂)
      (beta B (hX ≫ gX) c₂.i c.i (b ≫ a)
        (sj₂.paste_horiz sj₁).w (sj₂.paste_horiz sj₁))
      (exchange_comp B c.g c₁.g c₂.g g h a b sp₁.w sp₂.w (sp₂.paste_horiz sp₁).w)
      hb'
  · apply NatTrans.ext
    funext M
    exact hb' M

end AlgebraicGeometry.ProEtale.StrictTower
