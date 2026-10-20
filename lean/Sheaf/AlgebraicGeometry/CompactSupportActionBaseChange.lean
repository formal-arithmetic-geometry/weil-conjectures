/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q100
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion
import Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Compact-support actions and arbitrary base change

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
lem-amb-linear-trace-invariance.proof.md, paragraphs 1 and 2
(blueprint: lem-amb-compact-action-base-change).

The constructions below use the ordinary etale bounded-below derived formalism.
The exchange is the existing exchange for the actual Cartesian square, followed by
its existing canonical comparison to the supplied target compactification.

## Main statements

* `compactSupportActionSquare`: the automorphism square is Cartesian.
* `compactSupportAction_id`: the identity coefficient action is the identity.
* `compactSupportActionBaseChange`: invertibility, independence of compactification,
  and the equality of actual action morphisms under arbitrary base change.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- The automorphism square over the identity is Cartesian. Its comparison to the
chosen pullback is the universal map `(a, f)`.
Source: blueprint linear-trace proof, paragraph 1
(blueprint: lem-amb-compact-action-base-change).

Proof: The comparison is `pullback.lift a.hom f`. Its inverse is the first projection
followed by `a.inv`. The identities follow by the two projection identities and
`a.hom ≫ f = f`; uniqueness is def-pc-fibre-product. -/
theorem compactSupportActionSquare {X Y : Scheme.{u}} (f : X ⟶ Y)
    (a : X ≅ X) (ha : a.hom ≫ f = f) : IsPullback a.hom f f (𝟙 Y) := by
  exact IsPullback.of_horiz_isIso ⟨by simpa using ha⟩

section ExchangeCoherence

variable (F : CompactSupportFormalism.{u + 2, u + 1, u}) [F.HasProperExchange]
/-- Canonical compact-support exchange with a supplied target compactification.
Source: blueprint linear-trace proof, paragraphs 1 and 2; thm-cbc-finite-torsion
(blueprint: lem-amb-compact-action-base-change).
Construct this before specializing the formalism, so the coherence proofs do not unfold
chosen derived resolutions. -/
noncomputable def compactSupportFormalExchange
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c : Compactification f) (d : Compactification f') :
    F.shriek c ⋙ F.pb g ⟶ F.pb g' ⋙ F.shriek d :=
  (F.shriekBaseChangeOfIsPullback sq c).natTrans ≫
    Functor.whiskerLeft (F.pb g') (F.shriekIso (c.ofIsPullback sq) d).hom

/-- The action induced by exchange and a coefficient map in a compact-support formalism.
Source: blueprint linear-trace proof, paragraph 1
(blueprint: lem-amb-compact-action-base-change). -/
noncomputable def compactSupportFormalAction
    (F : CompactSupportFormalism.{u + 2, u + 1, u}) [F.HasProperExchange]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c : Compactification f) {a : X ⟶ X} (sq : IsPullback a f f (𝟙 Y))
    (K : F.obj X) (theta : (F.pb a).obj K ⟶ K) :
    (F.shriek c).obj K ⟶ (F.shriek c).obj K :=
  (F.pbId Y).inv.app ((F.shriek c).obj K) ≫
    (compactSupportFormalExchange F sq c c).app K ≫ (F.shriek c).map theta

/-- Pull a coefficient isomorphism back through the canonical square comparison.
Source: blueprint linear-trace proof, paragraph 2
(blueprint: lem-amb-compact-action-base-change). -/
noncomputable def compactSupportFormalCoefficientIso
    (F : CompactSupportFormalism.{u + 2, u + 1, u})
    {X X' : Scheme.{u}} (v : X' ⟶ X) (a : X ⟶ X) (a' : X' ⟶ X')
    (hw : a' ≫ v = v ≫ a) (K : F.obj X) (theta : (F.pb a).obj K ≅ K) :
    (F.pb a').obj ((F.pb v).obj K) ≅ (F.pb v).obj K :=
  (F.sqIso a' v v a hw).app K ≪≫ (F.pb v).mapIso theta

private theorem action_isIso
    (F : CompactSupportFormalism.{u + 2, u + 1, u})
    [F.HasProperExchange] [F.HasProperBaseChange]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c : Compactification f) {a : X ⟶ X} (sq : IsPullback a f f (𝟙 Y))
    (K : F.obj X) (theta : (F.pb a).obj K ≅ K) :
    IsIso (compactSupportFormalAction F c sq K theta.hom) := by
  have : IsIso (F.shriekBaseChangeOfIsPullback sq c).natTrans :=
    CompactSupportFormalism.isIso_shriekBaseChange F c (c.ofIsPullback sq)
      _ (c.isPullback_i_ofIsPullback sq) (c.isPullback_g_ofIsPullback sq).flip
  unfold compactSupportFormalAction compactSupportFormalExchange
  infer_instance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ex_target
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c : Compactification f)
    (d e : Compactification f') :
    compactSupportFormalExchange F sq c d ≫ Functor.whiskerLeft (F.pb g') (F.shriekIso d e).hom =
      compactSupportFormalExchange F sq c e := by
  simp only [compactSupportFormalExchange, Category.assoc, ← Functor.whiskerLeft_comp,
    ← Iso.trans_hom, F.shriekIso_trans]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ex_source
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c e : Compactification f)
    (d : Compactification f') :
    Functor.whiskerRight (F.shriekIso c e).hom (F.pb g) ≫ compactSupportFormalExchange F sq e d =
      compactSupportFormalExchange F sq c d := by
  let := c.hasCompactification
  let := d.hasCompactification
  let q := HasCompactification.compactification f
  let q' := HasCompactification.compactification f'
  have hc : (F.lowerShriekBaseChange sq).natTrans =
      Functor.whiskerRight (F.shriekIso q c).hom (F.pb g) ≫
        compactSupportFormalExchange F sq c q' := by
    have h := congrArg TwoSquare.natTrans (F.lowerShriekBaseChange_eq sq c)
    simpa only [compactSupportFormalExchange, TwoSquare.whiskerTop,
      TwoSquare.whiskerBottom, Category.assoc] using h
  have he : (F.lowerShriekBaseChange sq).natTrans =
      Functor.whiskerRight (F.shriekIso q e).hom (F.pb g) ≫
        compactSupportFormalExchange F sq e q' := by
    have h := congrArg TwoSquare.natTrans (F.lowerShriekBaseChange_eq sq e)
    simpa only [compactSupportFormalExchange, TwoSquare.whiskerTop,
      TwoSquare.whiskerBottom, Category.assoc] using h
  have hq : Functor.whiskerRight (F.shriekIso c e).hom (F.pb g) ≫
      compactSupportFormalExchange F sq e q' =
      compactSupportFormalExchange F sq c q' := by
    apply (cancel_epi (Functor.whiskerRight (F.shriekIso q c).hom (F.pb g))).mp
    rw [← Category.assoc, ← Functor.whiskerRight_comp, ← Iso.trans_hom,
      F.shriekIso_trans, ← he, hc]
  rw [← ex_target F sq e q' d, ← Category.assoc, hq, ex_target]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exchange_model
    (F : CompactSupportFormalism.{u + 2, u + 1, u}) [F.HasProperExchange]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c : Compactification f) (d : Compactification f')
    (h : d.Z ⟶ c.Z) (hi : IsPullback g' d.i c.i h)
    (hp : IsPullback h d.g c.g g) :
    (F.shriekBaseChangeOfIsPullback sq c).natTrans ≫
        Functor.whiskerLeft (F.pb g') (F.shriekIso (c.ofIsPullback sq) d).hom =
      (F.shriekBaseChange c d h hi hp).natTrans := by
  let r : d.Refinement (c.ofIsPullback sq) :=
    { hom := hp.isoPullback.hom
      i_hom := by
        apply pullback.hom_ext
        · simp only [Category.assoc, IsPullback.isoPullback_hom_fst]
          exact hi.w.symm.trans (c.ofIsPullback_i_fst sq).symm
        · simp only [Category.assoc, IsPullback.isoPullback_hom_snd]
          exact d.comm.symm.trans (c.ofIsPullback_i_snd sq).symm
      hom_g := hp.isoPullback_hom_snd }
  have hr : IsPullback d.i (𝟙 X') r.hom (c.ofIsPullback sq).i :=
    IsPullback.of_vert_isIso ⟨by simpa using r.i_hom⟩
  have hid : IsPullback c.i (𝟙 X) (Compactification.Refinement.id c).hom c.i :=
    by simpa only [Compactification.Refinement.id] using
      (IsPullback.of_id_snd : IsPullback c.i (𝟙 X) (𝟙 c.Z) c.i)
  have he := F.shriekBaseChange_refinementComparison
    (Compactification.Refinement.id c) hid r hr h hi hp
    (pullback.fst c.g g) (c.isPullback_i_ofIsPullback sq)
    (c.isPullback_g_ofIsPullback sq).flip
    (by simpa only [Compactification.Refinement.id, Category.comp_id] using
      hp.isoPullback_hom_fst.symm)
  rw [F.refinementComparison_eq_id _ hid rfl] at he
  have hrcomp : F.refinementComparison r hr =
      (F.shriekIso (c.ofIsPullback sq) d).hom := by
    rw [← F.shriekIso_symm d (c.ofIsPullback sq), F.shriekIso_eq_symm r hr]
    rfl
  ext K
  have hh := congrArg (fun t ↦ t.app K) he.symm
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, NatTrans.id_app, hrcomp] at hh
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at hh
  exact hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ex_paste_model
    {X Y X' Y' X'' Y'' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {f'' : X'' ⟶ Y''} {a : Y'' ⟶ Y'} {b : Y' ⟶ Y}
    {a' : X'' ⟶ X'} {b' : X' ⟶ X}
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback a' f'' f' a) (sq₂ : IsPullback b' f' f b)
    (c : Compactification f) (K : F.obj X) :
    (F.pb a).map ((compactSupportFormalExchange F sq₂ c (c.ofIsPullback sq₂)).app K) ≫
        (compactSupportFormalExchange F sq₁ (c.ofIsPullback sq₂)
          ((c.ofIsPullback sq₂).ofIsPullback sq₁)).app ((F.pb b').obj K) =
      (F.pbComp' a b (a ≫ b) rfl).inv.app ((F.shriek c).obj K) ≫
        (compactSupportFormalExchange F (sq₁.paste_horiz sq₂) c
          ((c.ofIsPullback sq₂).ofIsPullback sq₁)).app K ≫
        (F.shriek ((c.ofIsPullback sq₂).ofIsPullback sq₁)).map
          ((F.pbComp' a' b' (a' ≫ b') rfl).hom.app K) := by
  let d := c.ofIsPullback sq₂
  let e := d.ofIsPullback sq₁
  let h₁ := pullback.fst d.g a
  let h₂ := pullback.fst c.g b
  have hi₁ := d.isPullback_i_ofIsPullback sq₁
  have hi₂ := c.isPullback_i_ofIsPullback sq₂
  have hp₁ := (d.isPullback_g_ofIsPullback sq₁).flip
  have hp₂ := (c.isPullback_g_ofIsPullback sq₂).flip
  have hi := hi₁.paste_horiz hi₂
  have hp := hp₁.paste_horiz hp₂
  have he := exchange_model F (sq₁.paste_horiz sq₂) c e (h₁ ≫ h₂) hi hp
  have h := congrArg (fun t ↦ t.natTrans.app K)
    (F.shriekBaseChange_paste_horiz c d e h₁ h₂ hi₁ hp₁ hi₂ hp₂ hi hp)
  change compactSupportFormalExchange F (sq₁.paste_horiz sq₂) c e = _ at he
  rw [← he] at h
  simp only [TwoSquare.whiskerLeft, TwoSquare.whiskerRight, TwoSquare.vComp,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Functor.comp_obj] at h
  have hh := congrArg (fun t ↦
    (F.pbComp' a b (a ≫ b) rfl).inv.app ((F.shriek c).obj K) ≫ t ≫
      (F.shriek e).map ((F.pbComp' a' b' (a' ≫ b') rfl).hom.app K)) h
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app] at hh
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hh
  simpa only [compactSupportFormalExchange, F.shriekIso_refl, Iso.refl_hom, NatTrans.comp_app,
    Functor.whiskerLeft_app, NatTrans.id_app, Functor.comp_obj,
    Category.comp_id, Category.assoc] using hh.symm
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ex_paste
    {X Y X' Y' X'' Y'' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {f'' : X'' ⟶ Y''} {a : Y'' ⟶ Y'} {b : Y' ⟶ Y}
    {a' : X'' ⟶ X'} {b' : X' ⟶ X}
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback a' f'' f' a) (sq₂ : IsPullback b' f' f b)
    (c : Compactification f) (d : Compactification f') (e : Compactification f'')
    (K : F.obj X) :
    (F.pb a).map ((compactSupportFormalExchange F sq₂ c d).app K) ≫
        (compactSupportFormalExchange F sq₁ d e).app ((F.pb b').obj K) =
      (F.pbComp' a b (a ≫ b) rfl).inv.app ((F.shriek c).obj K) ≫
        (compactSupportFormalExchange F (sq₁.paste_horiz sq₂) c e).app K ≫
        (F.shriek e).map ((F.pbComp' a' b' (a' ≫ b') rfl).hom.app K) := by
  let d₀ := c.ofIsPullback sq₂
  let e₀ := d₀.ofIsPullback sq₁
  have hs := congr_app (ex_source F sq₁ d₀ d e) ((F.pb b').obj K)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hs
  calc
    _ = (F.pb a).map ((compactSupportFormalExchange F sq₂ c d₀).app K) ≫
        (compactSupportFormalExchange F sq₁ d₀ e).app ((F.pb b').obj K) := by
      rw [← ex_target F sq₂ c d₀ d]
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.map_comp,
        Category.assoc]
      rw [hs]
    _ = ((F.pb a).map ((compactSupportFormalExchange F sq₂ c d₀).app K) ≫
        (compactSupportFormalExchange F sq₁ d₀ e₀).app ((F.pb b').obj K)) ≫
        (F.shriekIso e₀ e).hom.app ((F.pb a').obj ((F.pb b').obj K)) := by
      rw [← ex_target F sq₁ d₀ e₀ e]
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
    _ = (F.pbComp' a b (a ≫ b) rfl).inv.app ((F.shriek c).obj K) ≫
        (compactSupportFormalExchange F (sq₁.paste_horiz sq₂) c e₀).app K ≫
        (F.shriek e₀).map ((F.pbComp' a' b' (a' ≫ b') rfl).hom.app K) ≫
        (F.shriekIso e₀ e).hom.app ((F.pb a').obj ((F.pb b').obj K)) := by
      rw [ex_paste_model]
      simp only [Category.assoc]
      rfl
    _ = (F.pbComp' a b (a ≫ b) rfl).inv.app ((F.shriek c).obj K) ≫
        (compactSupportFormalExchange F (sq₁.paste_horiz sq₂) c e₀).app K ≫
        (F.shriekIso e₀ e).hom.app ((F.pb (a' ≫ b')).obj K) ≫
        (F.shriek e).map ((F.pbComp' a' b' (a' ≫ b') rfl).hom.app K) := by
      have hn := (F.shriekIso e₀ e).hom.naturality
        ((F.pbComp' a' b' (a' ≫ b') rfl).hom.app K)
      exact congrArg (fun t ↦ (F.pbComp' a b (a ≫ b) rfl).inv.app
        ((F.shriek c).obj K) ≫
          (compactSupportFormalExchange F (sq₁.paste_horiz sq₂) c e₀).app K ≫ t) hn
    _ = _ := by
      have ht := congr_app (ex_target F (sq₁.paste_horiz sq₂) c e₀ e) K
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at ht
      rw [← Category.assoc ((compactSupportFormalExchange F (sq₁.paste_horiz sq₂) c e₀).app K), ht]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ex_paste'
    {X Y X' Y' X'' Y'' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {f'' : X'' ⟶ Y''} {a : Y'' ⟶ Y'} {b : Y' ⟶ Y}
    {a' : X'' ⟶ X'} {b' : X' ⟶ X}
    [QuasiCompact f] [QuasiCompact f'] [QuasiCompact f'']
    (sq₁ : IsPullback a' f'' f' a) (sq₂ : IsPullback b' f' f b)
    (t : X'' ⟶ X) (g : Y'' ⟶ Y) (ht : a' ≫ b' = t) (hg : a ≫ b = g)
    (sq : IsPullback t f'' f g)
    (c : Compactification f) (d : Compactification f') (e : Compactification f'')
    (K : F.obj X) :
    (F.pb a).map ((compactSupportFormalExchange F sq₂ c d).app K) ≫
        (compactSupportFormalExchange F sq₁ d e).app ((F.pb b').obj K) =
      (F.pbComp' a b g hg).inv.app ((F.shriek c).obj K) ≫
        (compactSupportFormalExchange F sq c e).app K ≫
        (F.shriek e).map ((F.pbComp' a' b' t ht).hom.app K) := by
  subst ht hg
  exact ex_paste F sq₁ sq₂ c d e K
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ex_action_exchange
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {g : Y' ⟶ Y} {a : X ⟶ X} {a' : X' ⟶ X'}
    [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback v f' f g) (sa : IsPullback a f f (𝟙 Y))
    (sa' : IsPullback a' f' f' (𝟙 Y')) (hw : a' ≫ v = v ≫ a)
    (c : Compactification f) (d : Compactification f') (K : F.obj X) :
    (F.pb g).map ((F.pbId Y).inv.app ((F.shriek c).obj K) ≫
        (compactSupportFormalExchange F sa c c).app K) ≫
        (compactSupportFormalExchange F sq c d).app ((F.pb a).obj K) =
      (compactSupportFormalExchange F sq c d).app K ≫
        (F.pbId Y').inv.app ((F.shriek d).obj ((F.pb v).obj K)) ≫
        (compactSupportFormalExchange F sa' d d).app ((F.pb v).obj K) ≫
        (F.shriek d).map ((F.sqIso a' v v a hw).hom.app K) := by
  have so : IsPullback (v ≫ a) f' f g := by
    simpa only [Category.comp_id] using sq.paste_horiz sa
  have h₁ := ex_paste' F sq sa (v ≫ a) g rfl (Category.comp_id g) so c c d K
  have h₂ := ex_paste' F sa' sq (v ≫ a) g hw (Category.id_comp g) so c d d K
  rw [F.pbComp'_id_right_inv_app] at h₁
  rw [F.pbComp'_id_left_inv_app] at h₂
  have h₂' := congrArg (fun t ↦
    (F.pbId Y').inv.app ((F.pb g).obj ((F.shriek c).obj K)) ≫ t) h₂
  rw [Iso.inv_hom_id_app_assoc] at h₂'
  have hn := (F.pbId Y').inv.naturality ((compactSupportFormalExchange F sq c d).app K)
  simp only [Functor.id_map, Functor.comp_obj] at hn
  rw [← Category.assoc, ← hn, Category.assoc] at h₂'
  rw [F.sqIso_eq a' v v a hw (v ≫ a) hw rfl]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc]
  rw [h₁]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [reassoc_of% h₂']
  simp only [← Functor.map_comp, Iso.hom_inv_id_app_assoc]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ex_action_naturality
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {g : Y' ⟶ Y} {a : X ⟶ X} {a' : X' ⟶ X'}
    [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback v f' f g) (sa : IsPullback a f f (𝟙 Y))
    (sa' : IsPullback a' f' f' (𝟙 Y')) (hw : a' ≫ v = v ≫ a)
    (c : Compactification f) (d : Compactification f') (K : F.obj X)
    (theta : (F.pb a).obj K ≅ K) :
    (F.pb g).map (compactSupportFormalAction F c sa K theta.hom) ≫
        (compactSupportFormalExchange F sq c d).app K =
      (compactSupportFormalExchange F sq c d).app K ≫
        compactSupportFormalAction F d sa' ((F.pb v).obj K)
          (compactSupportFormalCoefficientIso F v a a' hw K theta).hom := by
  unfold compactSupportFormalAction compactSupportFormalCoefficientIso
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom]
  have hn := (compactSupportFormalExchange F sq c d).naturality theta.hom
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [hn]
  rw [← Category.assoc, ← Category.assoc,
    ← Functor.map_comp, ex_action_exchange F sq sa sa' hw c d K]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ex_action_comparison
    {X Y : Scheme.{u}} {f : X ⟶ Y} {a : X ⟶ X} [QuasiCompact f]
    (sa : IsPullback a f f (𝟙 Y)) (c d : Compactification f) (K : F.obj X)
    (theta : (F.pb a).obj K ⟶ K) :
    compactSupportFormalAction F c sa K theta ≫ (F.shriekIso c d).hom.app K =
      (F.shriekIso c d).hom.app K ≫ compactSupportFormalAction F d sa K theta := by
  unfold compactSupportFormalAction
  have hs := congr_app (ex_source F sa c d d) K
  have ht := congr_app (ex_target F sa c c d) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hs ht
  have hn := (F.shriekIso c d).hom.naturality theta
  have hi := (F.pbId Y).inv.naturality ((F.shriekIso c d).hom.app K)
  simp only [Functor.id_map] at hi
  simp only [Category.assoc]
  rw [hn, ← Category.assoc ((compactSupportFormalExchange F sa c c).app K), ht, ← hs,
    ← Category.assoc,
    ← Category.assoc, ← hi]
  simp only [Category.assoc]

end ExchangeCoherence

/-- The canonical compact-support exchange, with any supplied target compactification.
Source: blueprint linear-trace proof, paragraphs 1 and 2; thm-cbc-finite-torsion
(blueprint: lem-amb-compact-action-base-change).
It is the exchange for `c.ofIsPullback sq`, followed by the canonical compactification
comparison, rather than a freely chosen isomorphism. -/
noncomputable def compactSupportActionExchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c : Compactification f) (d : Compactification f') :
    (derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek c ⋙
        (derivedPlusFormalism (ModuleCat.{u + 1} A)).pb g ⟶
      (derivedPlusFormalism (ModuleCat.{u + 1} A)).pb g' ⋙
        (derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek d :=
  compactSupportFormalExchange (derivedPlusFormalism (ModuleCat.{u + 1} A)) sq c d


/-- The actual morphism `Rf_!(theta) ∘ E_a(K)`, including the identity-pullback
identification on the base.
Source: blueprint linear-trace proof, paragraph 1
(blueprint: lem-amb-compact-action-base-change). -/
noncomputable def compactSupportAction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f]
    (c : Compactification f) {a : X ⟶ X} (sq : IsPullback a f f (𝟙 Y))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (theta : ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb a).obj K ≅ K) :
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek c).obj K ⟶
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriek c).obj K :=
  compactSupportFormalAction (derivedPlusFormalism (ModuleCat.{u + 1} A))
    c sq K theta.hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exchange_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {g : Y' ⟶ Y} {g' : X' ⟶ X} [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] [QuasiCompact f']
    (sq : IsPullback g' f' f g) (c : Compactification f) (d : Compactification f') :
    compactSupportActionExchange A sq c d =
      compactSupportFormalExchange (derivedPlusFormalism (ModuleCat.{u + 1} A)) sq c d := rfl

private theorem action_eq
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (c : Compactification f) {a : X ⟶ X}
    (sq : IsPullback a f f (𝟙 Y))
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (theta : ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb a).obj K ≅ K) :
    compactSupportAction A c sq K theta =
      compactSupportFormalAction (derivedPlusFormalism (ModuleCat.{u + 1} A))
        c sq K theta.hom := rfl

/-- The actual fibre-product automorphism `a ×_Y 1_T`.
Source: blueprint linear-trace proof, paragraph 2
(blueprint: lem-amb-compact-action-base-change). -/
noncomputable def compactSupportActionPullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : X ≅ X) (ha : a.hom ≫ f = f)
    {T : Scheme.{u}} (u : T ⟶ Y) : pullback f u ≅ pullback f u :=
  asIso (pullback.map f u f u a.hom (𝟙 T) (𝟙 Y)
    (by simpa only [Category.comp_id] using ha.symm) (by simp))

/-- Pull back the coefficient isomorphism through the canonical inverse-image
composition comparison attached to `u' a_T = a u'`.
Source: blueprint linear-trace proof, paragraph 2
(blueprint: lem-amb-compact-action-base-change). -/
noncomputable def compactSupportActionPullbackCoefficient
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : X ≅ X) (ha : a.hom ≫ f = f)
    {T : Scheme.{u}} (u : T ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (theta : ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb a.hom).obj K ≅ K) :
    ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb
        (compactSupportActionPullback f a ha u).hom).obj
          (((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb (pullback.fst f u)).obj K) ≅
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb (pullback.fst f u)).obj K :=
  compactSupportFormalCoefficientIso (derivedPlusFormalism (ModuleCat.{u + 1} A))
    (pullback.fst f u) a.hom (compactSupportActionPullback f a ha u).hom
    (by simp [compactSupportActionPullback, pullback.map]) K theta

private theorem coefficient_eq
    (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (a : X ≅ X) (ha : a.hom ≫ f = f)
    {T : Scheme.{u}} (u : T ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (theta : ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb a.hom).obj K ≅ K) :
    compactSupportActionPullbackCoefficient A f a ha u K theta =
      compactSupportFormalCoefficientIso (derivedPlusFormalism (ModuleCat.{u + 1} A))
        (pullback.fst f u) a.hom (compactSupportActionPullback f a ha u).hom
        (by simp [compactSupportActionPullback, pullback.map]) K theta := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The identity action, with `theta` the canonical identification of identity inverse
image with `K`, is the identity morphism.
Source: blueprint linear-trace proof, paragraph 1
(blueprint: lem-amb-compact-action-base-change).

Proof: Apply the identity clause of thm-cbc-finite-torsion. Its canonical comparisons
cancel the inserted identity-pullback identification, and functoriality sends the
identity coefficient morphism to the identity. -/
theorem compactSupportAction_id
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) [QuasiCompact c.i]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    compactSupportAction A c
        (compactSupportActionSquare f (Iso.refl X) (Category.id_comp f)) K
        ((upperStarIdDerivedPlus (ModuleCat.{u + 1} A) X).app K) = 𝟙 _ := by
  let F := derivedPlusFormalism (ModuleCat.{u + 1} A)
  have hi : IsPullback (𝟙 X) c.i c.i (𝟙 c.Z) := IsPullback.of_id_fst
  have hp : IsPullback (𝟙 c.Z) c.g c.g (𝟙 Y) := IsPullback.of_id_fst
  have he := exchange_model F
    (compactSupportActionSquare f (Iso.refl X) (Category.id_comp f)) c c
    (𝟙 c.Z) hi hp
  change compactSupportActionExchange A _ c c = _ at he
  rw [compactSupportAction, compactSupportFormalAction]
  change _ ≫ (compactSupportActionExchange A _ c c).app K ≫ _ = _
  rw [he, F.shriekBaseChange_id c hi hp]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_hom_app, Functor.leftUnitor_inv_app, Category.id_comp,
    Category.assoc, Iso.app_hom]
  dsimp only [Functor.id_obj]
  erw [Category.id_comp]
  change (F.pbId Y).inv.app _ ≫ (F.pbId Y).hom.app _ ≫
    (F.shriek c).map ((F.pbId X).inv.app K) ≫
      (F.shriek c).map ((F.pbId X).hom.app K) = 𝟙 _
  rw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Compact-support actions are automorphisms, commute with every canonical
compactification comparison, and commute with arbitrary base change using any supplied
compactification on the fibre product.
Source: blueprint linear-trace proof, paragraphs 1 and 2
(blueprint: lem-amb-compact-action-base-change).

Proof, following the five steps of the DAG node:
1. Use compactSupportActionSquare: the comparison `(a,f)` has inverse `a.inv pr_1`.
2. thm-cbc-finite-torsion makes exchange invertible. The coefficient isomorphism is
sent to an isomorphism by Rf_!, hence the composite action is invertible. Naturality
of the canonical comparisons from lem-amb-etale-compact-comparisons gives the displayed
independence equation for any second compactification.
3. The identity clause is compactSupportAction_id, by the identity exchange law.
4. Separatedness and finite type survive base change, and the supplied compactification
is used directly. The formal coherence argument needs no Noetherianity assertion for the
fibre product and no auxiliary compactification existence theorem. The universal property
gives `u' a_T = a u'`. Let delta identify `u'^* a^* K` with
`a_T^* u'^* K`, and put D = F_T(delta) C_u(a^*K). Horizontal pasting in
thm-cbc-finite-torsion gives D u^*E_a = E_aT C_u. Naturality at theta gives
C_u u^*F(theta) = F_T(theta_T) D. Associativity yields the displayed equation.
5. The same theorem makes exchange independent of all compactification choices.
Naturality of the comparisons from lem-amb-etale-compact-comparisons also transports
F_T(theta_T) and F_T(delta). Thus the equation uses the specified maps for arbitrary d,
even when d is not the pulled-back compactification. -/
theorem compactSupportActionBaseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    (f : X ⟶ Y) [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f) [QuasiCompact c.i]
    (a : X ≅ X) (ha : a.hom ≫ f = f)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (theta : ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb a.hom).obj K ≅ K) :
    IsIso (compactSupportAction A c (compactSupportActionSquare f a ha) K theta) ∧
    (∀ (d : Compactification f) [QuasiCompact d.i],
      compactSupportAction A c (compactSupportActionSquare f a ha) K theta ≫
          ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriekIso c d).hom.app K =
        ((derivedPlusFormalism (ModuleCat.{u + 1} A)).shriekIso c d).hom.app K ≫
          compactSupportAction A d (compactSupportActionSquare f a ha) K theta) ∧
    (∀ (T : Scheme.{u}) [IsNoetherian T] (u : T ⟶ Y)
      (d : Compactification (pullback.snd f u)) [QuasiCompact d.i],
      ((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb u).map
          (compactSupportAction A c (compactSupportActionSquare f a ha) K theta) ≫
          (compactSupportActionExchange A (IsPullback.of_hasPullback f u) c d).app K =
        (compactSupportActionExchange A (IsPullback.of_hasPullback f u) c d).app K ≫
          compactSupportAction A d
            (compactSupportActionSquare (pullback.snd f u)
              (compactSupportActionPullback f a ha u)
              (by simp [compactSupportActionPullback, pullback.map]))
            (((derivedPlusFormalism (ModuleCat.{u + 1} A)).pb (pullback.fst f u)).obj K)
            (compactSupportActionPullbackCoefficient A f a ha u K theta)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact action_isIso (derivedPlusFormalism (ModuleCat.{u + 1} A)) c
      (compactSupportActionSquare f a ha) K theta
  · intro d _
    have h := ex_action_comparison (derivedPlusFormalism (ModuleCat.{u + 1} A))
      (compactSupportActionSquare f a ha) c d K theta.hom
    exact h
  · intro T _ u d _
    have h := ex_action_naturality (derivedPlusFormalism (ModuleCat.{u + 1} A))
      (IsPullback.of_hasPullback f u)
      (compactSupportActionSquare f a ha)
      (compactSupportActionSquare (pullback.snd f u)
        (compactSupportActionPullback f a ha u)
        (by simp [compactSupportActionPullback, pullback.map]))
      (by simp [compactSupportActionPullback, pullback.map]) c d K theta
    rw [action_eq, exchange_eq, action_eq, coefficient_eq]
    exact h

end AlgebraicGeometry.Etale
