/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Coherence of natural transformations between left derived functors

Let `Q₁ : ℋ₁ ⥤ 𝒟₁` and `Q₂ : ℋ₂ ⥤ 𝒟₂` be localization functors (typically from homotopy
categories to derived categories), and let `LE : 𝒟₁ ⥤ 𝒟₂` be a left derived functor of
`EH : ℋ₁ ⥤ ℋ₂` with counit `κE : Q₁ ⋙ LE ⟶ EH ⋙ Q₂`. A natural transformation between
composites of left derived functors is determined by its composite with the counits on the image
of `Q₁` (`Functor.leftDerived_ext`). This file records the diagram chases built on this, for
arbitrary categories, functors and natural transformations:

- `Adjunction.leftDerived_transpose_app` computes, on the image of `Q₁`, the transpose along an
  adjunction `LE ⊣ LRes` of a natural transformation `θ : LT ⟶ LE ⋙ LRes` characterized by the
  counits.
- `Adjunction.leftDerived_transpose_naturality_app` shows that two such transposes are compatible
  with comparison maps `LE₁ ⋙ LgS ≅ LgR ⋙ LE₃` and `LT₁ ⋙ LgR ⟶ LgR ⋙ LT₃`, on the image of
  `Q₁`.
- `Functor.leftDerived_app_comp_map_app_eq_app` and
  `Functor.leftDerived_app_comp_map_app_eq_app_comp`: the natural transformation
  `LE ⋙ Lq ⟶ Lp ⋙ LE` induced on left derived functors by a natural transformation
  `E ⋙ q ⟶ p ⋙ E` on homotopy categories is compatible with identities and with composition
  whenever the latter is.

## Implementation notes

The statements involve composites of counits such as
`Functor.whiskerRight αE Lq ≫ Functor.whiskerLeft (E.mapHomotopyCategory c) αq`. These are
ascribed the right-associated functor types `Qv ⋙ LE ⋙ Lq ⟶ E.mapHomotopyCategory c ⋙ ⋯`,
which is how the composite counits of concrete derived functors are usually defined; this keeps
the instances of these lemmas syntactically aligned with the concrete counits, so that the kernel
does not unfold concrete derived categories to compare differently bracketed functors.

The counit of the composite `LE ⋙ LRes` in `Adjunction.leftDerived_transpose_app` is taken as a
morphism `εK` together with its formula `hε`: in the applications, its target is only
definitionally equal to `Q₁.obj (ResH.obj (EH.obj K))`.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory

section Transpose

variable {𝒟₁ 𝒟₂ ℋ₁ ℋ₂ : Type*} [Category 𝒟₁] [Category 𝒟₂] [Category ℋ₁] [Category ℋ₂]
  {Q₁ : ℋ₁ ⥤ 𝒟₁} {Q₂ : ℋ₂ ⥤ 𝒟₂} {LE : 𝒟₁ ⥤ 𝒟₂} {LRes : 𝒟₂ ⥤ 𝒟₁} {LT : 𝒟₁ ⥤ 𝒟₁}
  {TH : ℋ₁ ⥤ ℋ₁} {EH : ℋ₁ ⥤ ℋ₂} {ResH : ℋ₂ ⥤ ℋ₁} {TEH : ℋ₁ ⥤ ℋ₂}

/-- **The transpose of a derived natural transformation.** Let `κE` and `κT` be the counits of
left derived functors `LE` and `LT` of `EH` and `TH`, let `adj : LE ⊣ LRes` be an adjunction
whose counit is computed by `hadj` from an adjunction `adjH : EH ⊣ ResH`, where
`fac : Q₂ ⋙ LRes ≅ ResH ⋙ Q₁`, and let `θ : LT ⟶ LE ⋙ LRes` be induced by
`πK : TH K ⟶ ResH (EH K)` (`hθ`, where `εK` is the counit of `LE ⋙ LRes`, `hε`). If the
transpose of `πK` along `adjH` is `e ≫ p` (`hkey`), then the transpose of `θ` along `adj` is
induced by `e ≫ p`:
```
LE (LT (Q₁ K)) ──LE θ──▶ LE (LRes (LE (Q₁ K))) ──ε──▶ LE (Q₁ K) ──κE K──▶ Q₂ (EH K)
      │                                                                    ▲
  LE (κT K)                                                                │ Q₂ (e ≫ p)
      ▼                                                                    │
LE (Q₁ (TH K)) ─────────────────κE (TH K)──────────────────▶ Q₂ (EH (TH K)) ┘
```
-/
lemma Adjunction.leftDerived_transpose_app (κE : Q₁ ⋙ LE ⟶ EH ⋙ Q₂)
    (κT : Q₁ ⋙ LT ⟶ TH ⋙ Q₁) (fac : Q₂ ⋙ LRes ≅ ResH ⋙ Q₁) (θ : LT ⟶ LE ⋙ LRes)
    (adj : LE ⊣ LRes) (adjH : EH ⊣ ResH) (e : TH ⋙ EH ≅ TEH) (p : TEH ⟶ EH)
    (hadj : ∀ K, adj.counit.app (Q₂.obj K) =
      LE.map (fac.hom.app K) ≫ κE.app (ResH.obj K) ≫ Q₂.map (adjH.counit.app K))
    (K : ℋ₁) (πK : TH.obj K ⟶ ResH.obj (EH.obj K))
    (εK : LRes.obj (LE.obj (Q₁.obj K)) ⟶ Q₁.obj (ResH.obj (EH.obj K)))
    (hε : εK = LRes.map (κE.app K) ≫ fac.hom.app (EH.obj K))
    (hθ : θ.app (Q₁.obj K) ≫ εK = κT.app K ≫ Q₁.map πK)
    (hkey : EH.map πK ≫ adjH.counit.app (EH.obj K) = e.hom.app K ≫ p.app K) :
    LE.map (θ.app (Q₁.obj K)) ≫ adj.counit.app (LE.obj (Q₁.obj K)) ≫ κE.app K =
      LE.map (κT.app K) ≫ κE.app (TH.obj K) ≫ Q₂.map (e.hom.app K ≫ p.app K) := by
  rw [hε] at hθ
  have hθ' := congrArg LE.map hθ
  simp only [Functor.map_comp] at hθ'
  have hnat := adj.counit.naturality (κE.app K)
  have hκ := κE.naturality πK
  dsimp at hnat hκ
  rw [← hnat, hadj, reassoc_of% hθ', reassoc_of% hκ, ← Functor.map_comp, hkey]

variable {𝒟₃ 𝒟₄ ℋ₃ ℋ₄ : Type*} [Category 𝒟₃] [Category 𝒟₄] [Category ℋ₃] [Category ℋ₄]
  {Q₃ : ℋ₃ ⥤ 𝒟₃} {Q₄ : ℋ₄ ⥤ 𝒟₄} {LT₁ : 𝒟₁ ⥤ 𝒟₁} {LT₃ : 𝒟₃ ⥤ 𝒟₃} {LE₁ : 𝒟₁ ⥤ 𝒟₂}
  {LE₃ : 𝒟₃ ⥤ 𝒟₄} {LgR : 𝒟₁ ⥤ 𝒟₃} {LgS : 𝒟₂ ⥤ 𝒟₄} {LRes₂ : 𝒟₂ ⥤ 𝒟₁} {LRes₄ : 𝒟₄ ⥤ 𝒟₃}
  {T₁ : ℋ₁ ⥤ ℋ₁} {T₃ : ℋ₃ ⥤ ℋ₃} {E₁ : ℋ₁ ⥤ ℋ₂} {E₃ : ℋ₃ ⥤ ℋ₄} {gR : ℋ₁ ⥤ ℋ₃}
  {gS : ℋ₂ ⥤ ℋ₄} {TE₁ : ℋ₁ ⥤ ℋ₂} {TE₃ : ℋ₃ ⥤ ℋ₄}

/-- **Naturality of transposes of derived natural transformations.** Let `θ₁ : LT₁ ⟶ LE₁ ⋙ LRes₂`
and `θ₃ : LT₃ ⟶ LE₃ ⋙ LRes₄` be natural transformations between left derived functors (with
counits `κ…`), with transposes `θᵢ♯ = LEᵢ θᵢ ≫ εᵢ : LTᵢ ⋙ LEᵢ ⟶ LEᵢ` along `adjᵢ`, and let
`α : LE₁ ⋙ LgS ≅ LgR ⋙ LE₃` and `β : LT₁ ⋙ LgR ⟶ LgR ⋙ LT₃` be induced by `σ` and `τ` on
homotopy categories (`hα`, `hβ`). Suppose that the transposes are induced by `e₁ ≫ p₁` and
`e₃ ≫ p₃` on homotopy categories (`htr₁`, `htr₃`, see `Adjunction.leftDerived_transpose_app`)
and that these form a commutative square with `σ` and `τ` (`hH`). Then the square
```
LgS (LE₁ (LT₁ K)) ──LgS θ₁♯──▶ LgS (LE₁ K)
        │                          │
       α                           α
        ▼                          ▼
LE₃ (LgR (LT₁ K)) ──LE₃ β──▶ LE₃ (LT₃ (LgR K)) ──θ₃♯──▶ LE₃ (LgR K)
```
commutes on `K = Q₁ K'` after composition with the counit of `LgR ⋙ LE₃`. -/
lemma Adjunction.leftDerived_transpose_naturality_app
    (κT₁ : Q₁ ⋙ LT₁ ⟶ T₁ ⋙ Q₁) (κT₃ : Q₃ ⋙ LT₃ ⟶ T₃ ⋙ Q₃)
    (κE₁ : Q₁ ⋙ LE₁ ⟶ E₁ ⋙ Q₂) (κE₃ : Q₃ ⋙ LE₃ ⟶ E₃ ⋙ Q₄)
    (κgR : Q₁ ⋙ LgR ⟶ gR ⋙ Q₃) (κgS : Q₂ ⋙ LgS ⟶ gS ⋙ Q₄)
    (θ₁ : LT₁ ⟶ LE₁ ⋙ LRes₂) (θ₃ : LT₃ ⟶ LE₃ ⋙ LRes₄)
    (adj₁ : LE₁ ⊣ LRes₂) (adj₃ : LE₃ ⊣ LRes₄)
    (α : LE₁ ⋙ LgS ≅ LgR ⋙ LE₃) (β : LT₁ ⋙ LgR ⟶ LgR ⋙ LT₃)
    (σ : E₁ ⋙ gS ≅ gR ⋙ E₃) (τ : T₁ ⋙ gR ⟶ gR ⋙ T₃)
    (e₁ : T₁ ⋙ E₁ ≅ TE₁) (p₁ : TE₁ ⟶ E₁) (e₃ : T₃ ⋙ E₃ ≅ TE₃) (p₃ : TE₃ ⟶ E₃)
    (hα : ∀ K, α.hom.app (Q₁.obj K) ≫
        (Functor.whiskerRight κgR LE₃ ≫ Functor.whiskerLeft gR κE₃ :
          Q₁ ⋙ LgR ⋙ LE₃ ⟶ gR ⋙ E₃ ⋙ Q₄).app K =
      (Functor.whiskerRight κE₁ LgS ≫ Functor.whiskerLeft E₁ κgS :
          Q₁ ⋙ LE₁ ⋙ LgS ⟶ E₁ ⋙ gS ⋙ Q₄).app K ≫ Q₄.map (σ.hom.app K))
    (hβ : ∀ K, β.app (Q₁.obj K) ≫
        (Functor.whiskerRight κgR LT₃ ≫ Functor.whiskerLeft gR κT₃ :
          Q₁ ⋙ LgR ⋙ LT₃ ⟶ gR ⋙ T₃ ⋙ Q₃).app K =
      (Functor.whiskerRight κT₁ LgR ≫ Functor.whiskerLeft T₁ κgR :
          Q₁ ⋙ LT₁ ⋙ LgR ⟶ T₁ ⋙ gR ⋙ Q₃).app K ≫ Q₃.map (τ.app K))
    (htr₁ : ∀ K, LE₁.map (θ₁.app (Q₁.obj K)) ≫ adj₁.counit.app (LE₁.obj (Q₁.obj K)) ≫
        κE₁.app K =
      LE₁.map (κT₁.app K) ≫ κE₁.app (T₁.obj K) ≫ Q₂.map (e₁.hom.app K ≫ p₁.app K))
    (htr₃ : ∀ K, LE₃.map (θ₃.app (Q₃.obj K)) ≫ adj₃.counit.app (LE₃.obj (Q₃.obj K)) ≫
        κE₃.app K =
      LE₃.map (κT₃.app K) ≫ κE₃.app (T₃.obj K) ≫ Q₄.map (e₃.hom.app K ≫ p₃.app K))
    (hH : ∀ K, gS.map (e₁.hom.app K ≫ p₁.app K) ≫ σ.hom.app K =
      σ.hom.app (T₁.obj K) ≫ E₃.map (τ.app K) ≫ e₃.hom.app (gR.obj K) ≫ p₃.app (gR.obj K))
    (K : ℋ₁) :
    (LgS.map (LE₁.map (θ₁.app (Q₁.obj K)) ≫ adj₁.counit.app (LE₁.obj (Q₁.obj K))) ≫
      α.hom.app (Q₁.obj K)) ≫
        (Functor.whiskerRight κgR LE₃ ≫ Functor.whiskerLeft gR κE₃ :
          Q₁ ⋙ LgR ⋙ LE₃ ⟶ gR ⋙ E₃ ⋙ Q₄).app K =
    (α.hom.app (LT₁.obj (Q₁.obj K)) ≫
      LE₃.map (β.app (Q₁.obj K) ≫ θ₃.app (LgR.obj (Q₁.obj K))) ≫
      adj₃.counit.app (LE₃.obj (LgR.obj (Q₁.obj K)))) ≫
        (Functor.whiskerRight κgR LE₃ ≫ Functor.whiskerLeft gR κE₃ :
          Q₁ ⋙ LgR ⋙ LE₃ ⟶ gR ⋙ E₃ ⋙ Q₄).app K := by
  -- the two composites with `α`, at `K` and at `T₁ K`
  have hα₁ := hα K
  have hα₂ := hα (T₁.obj K)
  -- the transposes on the image of `Q₁` and of `Q₃`
  have hY := congrArg LgS.map (htr₁ K)
  have hZ := htr₃ (gR.obj K)
  -- the comparison `β` and the homotopy category square
  have ha := congrArg LE₃.map (hβ K)
  have hH' := congrArg Q₄.map (hH K)
  -- naturality of the counits, of `θ₃` and of `α`
  have hS := κgS.naturality (e₁.hom.app K ≫ p₁.app K)
  have hϑ := congrArg LE₃.map (θ₃.naturality (κgR.app K))
  have hΨ := κE₃.naturality (τ.app K)
  have hn := α.hom.naturality (κT₁.app K)
  have hε := adj₃.counit.naturality (LE₃.map (κgR.app K))
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.map_comp, Functor.comp_map, Functor.comp_obj, Category.assoc]
    at hα₁ hα₂ hY hZ ha hS hϑ hΨ hn hH' hε ⊢
  rw [hα₁, reassoc_of% hY, reassoc_of% hS, hH', ← reassoc_of% hε,
    ← reassoc_of% hϑ, hZ, reassoc_of% ha, reassoc_of% hΨ, ← reassoc_of% hn, reassoc_of% hα₂]

end Transpose

section HomotopyCategory

variable {ι : Type*} {c : ComplexShape ι}

/-- **Derived natural transformations and identities.** Let `LE`, `Lp` and `Lq` be left derived
functors of `E`, `p` and `q` on homotopy categories, with counits `αE`, `αp` and `αq`, and let
`Φ : LE ⋙ Lq ⟶ Lp ⋙ LE` be induced by `eH : E ⋙ q ⟶ p ⋙ E` (`hΦ`). If `ιR : Lp ⟶ 𝟭` and
`ιS : Lq ⟶ 𝟭` are induced by `βR : p ⟶ 𝟭` and `βS : q ⟶ 𝟭` (`hR`, `hS`) and `eH` is compatible
with them (`he`), then so is `Φ`:
```
Lq (LE K) ──Φ K──▶ LE (Lp K)
     ╲                 │
   ιS (LE K)        LE (ιR K)
        ╲              ▼
         ╰──────────▶ LE K
```
-/
lemma Functor.leftDerived_app_comp_map_app_eq_app {V W DV DW : Type*} [Category V] [Category W]
    [Preadditive V] [Preadditive W] [Category DV] [Category DW]
    {Qv : HomotopyCategory V c ⥤ DV} {Qw : HomotopyCategory W c ⥤ DW}
    (Wv : MorphismProperty (HomotopyCategory V c)) [Qv.IsLocalization Wv]
    {E : V ⥤ W} {p : V ⥤ V} {q : W ⥤ W} [E.Additive] [p.Additive] [q.Additive]
    {LE : DV ⥤ DW} (αE : Qv ⋙ LE ⟶ E.mapHomotopyCategory c ⋙ Qw)
    [LE.IsLeftDerivedFunctor αE Wv]
    {Lp : DV ⥤ DV} (αp : Qv ⋙ Lp ⟶ p.mapHomotopyCategory c ⋙ Qv)
    {Lq : DW ⥤ DW} (αq : Qw ⋙ Lq ⟶ q.mapHomotopyCategory c ⋙ Qw)
    (Φ : LE ⋙ Lq ⟶ Lp ⋙ LE)
    (eH : E.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c ⟶
      p.mapHomotopyCategory c ⋙ E.mapHomotopyCategory c)
    (hΦ : ∀ K, Φ.app (Qv.obj K) ≫
        (Functor.whiskerRight αp LE ≫ Functor.whiskerLeft (p.mapHomotopyCategory c) αE :
          Qv ⋙ Lp ⋙ LE ⟶ p.mapHomotopyCategory c ⋙ E.mapHomotopyCategory c ⋙ Qw).app K =
      (Functor.whiskerRight αE Lq ≫ Functor.whiskerLeft (E.mapHomotopyCategory c) αq :
          Qv ⋙ LE ⋙ Lq ⟶ E.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c ⋙ Qw).app K ≫
        Qw.map (X := (E.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c).obj K) (eH.app K))
    (ιR : Lp ⟶ 𝟭 DV) (βR : p ⟶ 𝟭 V)
    (hR : ∀ K, ιR.app (Qv.obj K) =
      αp.app K ≫ Qv.map ((NatTrans.mapHomotopyCategory βR c).app K))
    (ιS : Lq ⟶ 𝟭 DW) (βS : q ⟶ 𝟭 W)
    (hS : ∀ K, ιS.app (Qw.obj K) =
      αq.app K ≫ Qw.map ((NatTrans.mapHomotopyCategory βS c).app K))
    (he : ∀ K, eH.app K ≫
        (E.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory βR c).app K) =
      (NatTrans.mapHomotopyCategory βS c).app ((E.mapHomotopyCategory c).obj K))
    (K : DV) :
    Φ.app K ≫ LE.map (ιR.app K) = ιS.app (LE.obj K) := by
  have key : (Φ ≫ Functor.whiskerRight ιR LE : LE ⋙ Lq ⟶ LE) =
      (Functor.whiskerLeft LE ιS : LE ⋙ Lq ⟶ LE) := by
    apply Functor.leftDerived_ext (LF := LE) (α := αE) (W := Wv)
    ext K
    have h := hΦ K
    have hn := αE.naturality ((NatTrans.mapHomotopyCategory βR c).app K)
    have hn' := ιS.naturality (αE.app K)
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc, Functor.comp_map, Functor.id_map] at h hn hn' ⊢
    simp only [hR, Functor.map_comp, Category.assoc]
    -- `hn` is stated at `(𝟭 V).mapHomotopyCategory c` applied to `K`, definitionally `K`
    erw [hn]
    rw [reassoc_of% h, ← Qw.map_comp, he K, ← hS]
    exact hn'
  simpa using NatTrans.congr_app key K

/-- **Derived natural transformations and composition.** Let `Φ`, `Φ₁` and `Φ₁₂` be natural
transformations between left derived functors induced by `eH`, `e₁H` and `e₁₂H` on homotopy
categories (`hΦ`, `hΦ₁`, `hΦ₁₂`, as in `Functor.leftDerived_app_comp_map_app_eq_app`), and let
`cR : Lp₁₂ ≅ Lp ⋙ Lp₁` and `cS : Lq₁₂ ⟶ Lq ⋙ Lq₁` be induced by `γR` and `γS` (`hcR`, `hcS`).
If `e₁₂H`, `eH` and `e₁H` are compatible with `γR` and `γS` (`he`), then the pentagon
```
Lq₁₂ (LEY K) ──Φ₁₂ K──▶ LET (Lp₁₂ K)
      │                        │
  cS (LEY K)              LET (cR K)
      ▼                        ▼
Lq₁ (Lq (LEY K)) ──Lq₁ (Φ K)──▶ Lq₁ (LEZ (Lp K)) ──Φ₁ (Lp K)──▶ LET (Lp₁ (Lp K))
```
commutes. -/
lemma Functor.leftDerived_app_comp_map_app_eq_app_comp
    {VY VZ VT WY WZ WT DY DZ DT D'Y D'Z D'T : Type*}
    [Category VY] [Category VZ] [Category VT] [Category WY] [Category WZ] [Category WT]
    [Preadditive VY] [Preadditive VZ] [Preadditive VT] [Preadditive WY] [Preadditive WZ]
    [Preadditive WT]
    [Category DY] [Category DZ] [Category DT] [Category D'Y] [Category D'Z] [Category D'T]
    {QY : HomotopyCategory VY c ⥤ DY} {QZ : HomotopyCategory VZ c ⥤ DZ}
    {QT : HomotopyCategory VT c ⥤ DT} {Q'Y : HomotopyCategory WY c ⥤ D'Y}
    {Q'Z : HomotopyCategory WZ c ⥤ D'Z} {Q'T : HomotopyCategory WT c ⥤ D'T}
    (Wq : MorphismProperty (HomotopyCategory VY c)) [QY.IsLocalization Wq]
    {EY : VY ⥤ WY} {EZ : VZ ⥤ WZ} {ET : VT ⥤ WT} {p : VY ⥤ VZ} {p₁ : VZ ⥤ VT}
    {p₁₂ : VY ⥤ VT} {q : WY ⥤ WZ} {q₁ : WZ ⥤ WT} {q₁₂ : WY ⥤ WT}
    [EY.Additive] [EZ.Additive] [ET.Additive] [p.Additive] [p₁.Additive] [p₁₂.Additive]
    [q.Additive] [q₁.Additive] [q₁₂.Additive]
    {LEY : DY ⥤ D'Y} (αEY : QY ⋙ LEY ⟶ EY.mapHomotopyCategory c ⋙ Q'Y)
    {LEZ : DZ ⥤ D'Z} (αEZ : QZ ⋙ LEZ ⟶ EZ.mapHomotopyCategory c ⋙ Q'Z)
    {LET : DT ⥤ D'T} (αET : QT ⋙ LET ⟶ ET.mapHomotopyCategory c ⋙ Q'T)
    {Lp : DY ⥤ DZ} (αp : QY ⋙ Lp ⟶ p.mapHomotopyCategory c ⋙ QZ)
    {Lp₁ : DZ ⥤ DT} (αp₁ : QZ ⋙ Lp₁ ⟶ p₁.mapHomotopyCategory c ⋙ QT)
    {Lp₁₂ : DY ⥤ DT} (αp₁₂ : QY ⋙ Lp₁₂ ⟶ p₁₂.mapHomotopyCategory c ⋙ QT)
    {Lq : D'Y ⥤ D'Z} (αq : Q'Y ⋙ Lq ⟶ q.mapHomotopyCategory c ⋙ Q'Z)
    {Lq₁ : D'Z ⥤ D'T} (αq₁ : Q'Z ⋙ Lq₁ ⟶ q₁.mapHomotopyCategory c ⋙ Q'T)
    {Lq₁₂ : D'Y ⥤ D'T} (αq₁₂ : Q'Y ⋙ Lq₁₂ ⟶ q₁₂.mapHomotopyCategory c ⋙ Q'T)
    [hLp₁₂ : (Lp₁₂ ⋙ LET).IsLeftDerivedFunctor
      (Functor.whiskerRight αp₁₂ LET ≫ Functor.whiskerLeft (p₁₂.mapHomotopyCategory c) αET :
        QY ⋙ Lp₁₂ ⋙ LET ⟶ p₁₂.mapHomotopyCategory c ⋙ ET.mapHomotopyCategory c ⋙ Q'T) Wq]
    (Φ : LEY ⋙ Lq ⟶ Lp ⋙ LEZ)
    (eH : EY.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c ⟶
      p.mapHomotopyCategory c ⋙ EZ.mapHomotopyCategory c)
    (hΦ : ∀ K, Φ.app (QY.obj K) ≫
        (Functor.whiskerRight αp LEZ ≫ Functor.whiskerLeft (p.mapHomotopyCategory c) αEZ :
          QY ⋙ Lp ⋙ LEZ ⟶ p.mapHomotopyCategory c ⋙ EZ.mapHomotopyCategory c ⋙ Q'Z).app K =
      (Functor.whiskerRight αEY Lq ≫ Functor.whiskerLeft (EY.mapHomotopyCategory c) αq :
          QY ⋙ LEY ⋙ Lq ⟶ EY.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c ⋙ Q'Z).app K ≫
        Q'Z.map (X := (EY.mapHomotopyCategory c ⋙ q.mapHomotopyCategory c).obj K) (eH.app K))
    (Φ₁ : LEZ ⋙ Lq₁ ⟶ Lp₁ ⋙ LET)
    (e₁H : EZ.mapHomotopyCategory c ⋙ q₁.mapHomotopyCategory c ⟶
      p₁.mapHomotopyCategory c ⋙ ET.mapHomotopyCategory c)
    (hΦ₁ : ∀ K, Φ₁.app (QZ.obj K) ≫
        (Functor.whiskerRight αp₁ LET ≫ Functor.whiskerLeft (p₁.mapHomotopyCategory c) αET :
          QZ ⋙ Lp₁ ⋙ LET ⟶ p₁.mapHomotopyCategory c ⋙ ET.mapHomotopyCategory c ⋙ Q'T).app K =
      (Functor.whiskerRight αEZ Lq₁ ≫ Functor.whiskerLeft (EZ.mapHomotopyCategory c) αq₁ :
          QZ ⋙ LEZ ⋙ Lq₁ ⟶ EZ.mapHomotopyCategory c ⋙ q₁.mapHomotopyCategory c ⋙ Q'T).app K ≫
        Q'T.map (X := (EZ.mapHomotopyCategory c ⋙ q₁.mapHomotopyCategory c).obj K) (e₁H.app K))
    (Φ₁₂ : LEY ⋙ Lq₁₂ ⟶ Lp₁₂ ⋙ LET)
    (e₁₂H : EY.mapHomotopyCategory c ⋙ q₁₂.mapHomotopyCategory c ⟶
      p₁₂.mapHomotopyCategory c ⋙ ET.mapHomotopyCategory c)
    (hΦ₁₂ : ∀ K, Φ₁₂.app (QY.obj K) ≫
        (Functor.whiskerRight αp₁₂ LET ≫ Functor.whiskerLeft (p₁₂.mapHomotopyCategory c) αET :
          QY ⋙ Lp₁₂ ⋙ LET ⟶ p₁₂.mapHomotopyCategory c ⋙ ET.mapHomotopyCategory c ⋙ Q'T).app K =
      (Functor.whiskerRight αEY Lq₁₂ ≫ Functor.whiskerLeft (EY.mapHomotopyCategory c) αq₁₂ :
          QY ⋙ LEY ⋙ Lq₁₂ ⟶ EY.mapHomotopyCategory c ⋙ q₁₂.mapHomotopyCategory c ⋙ Q'T).app K ≫
        Q'T.map (X := (EY.mapHomotopyCategory c ⋙ q₁₂.mapHomotopyCategory c).obj K)
          (e₁₂H.app K))
    (cR : Lp₁₂ ≅ Lp ⋙ Lp₁) (γR : p₁₂ ≅ p ⋙ p₁)
    (hcR : ∀ K, cR.inv.app (QY.obj K) ≫ αp₁₂.app K =
      Lp₁.map (αp.app K) ≫ αp₁.app ((p.mapHomotopyCategory c).obj K) ≫
        QT.map (X := ((p ⋙ p₁).mapHomotopyCategory c).obj K)
          ((NatTrans.mapHomotopyCategory γR.inv c).app K))
    (cS : Lq₁₂ ⟶ Lq ⋙ Lq₁) (γS : q₁₂ ⟶ q ⋙ q₁)
    (hcS : ∀ K, cS.app (Q'Y.obj K) ≫ Lq₁.map (αq.app K) ≫
        αq₁.app ((q.mapHomotopyCategory c).obj K) =
      αq₁₂.app K ≫ Q'T.map ((NatTrans.mapHomotopyCategory γS c).app K))
    (he : ∀ K, e₁₂H.app K ≫
        (ET.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory γR.hom c).app K) =
      (NatTrans.mapHomotopyCategory γS c).app ((EY.mapHomotopyCategory c).obj K) ≫
        (q₁.mapHomotopyCategory c).map (eH.app K) ≫ e₁H.app ((p.mapHomotopyCategory c).obj K))
    (K : DY) :
    Φ₁₂.app K ≫ LET.map (cR.hom.app K) =
      cS.app (LEY.obj K) ≫ Lq₁.map (Φ.app K) ≫ Φ₁.app (Lp.obj K) := by
  have key : Φ₁₂ =
      Functor.whiskerLeft _ cS ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight Φ _ ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ Φ₁ ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight cR.inv _ := by
    apply Functor.leftDerived_ext (LF := Lp₁₂ ⋙ LET)
      (α := Functor.whiskerRight αp₁₂ LET ≫
        Functor.whiskerLeft (p₁₂.mapHomotopyCategory c) αET) (W := Wq)
    ext K
    have h₀ := hΦ₁₂ K
    have h₁ := hcR K
    have h₂ := αET.naturality ((NatTrans.mapHomotopyCategory γR.inv c).app K)
    have h₃ := Φ₁.naturality (αp.app K)
    have h₄ := hΦ₁ ((p.mapHomotopyCategory c).obj K)
    have h₅ := hΦ K
    have h₆ := αq₁.naturality (eH.app K)
    have h₇ := cS.naturality (αEY.app K)
    have h₈ := hcS ((EY.mapHomotopyCategory c).obj K)
    have h₉ := he K
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Category.assoc] at h₀ h₄ h₅ ⊢
    dsimp at h₂ h₃ h₆ h₇
    have h₅' := congrArg Lq₁.map h₅
    simp only [Functor.map_comp] at h₅'
    have hinv : (ET.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory γR.hom c).app K) ≫
        (ET.mapHomotopyCategory c).map ((NatTrans.mapHomotopyCategory γR.inv c).app K) = 𝟙 _ :=
      ((ET.mapHomotopyCategory c).mapIso ((NatIso.mapHomotopyCategory γR c).app K)).hom_inv_id
    simp only [Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp]
    rw [h₀, ← LET.map_comp_assoc, h₁]
    simp only [Functor.map_comp, Category.assoc]
    rw [h₂, ← reassoc_of% h₃]
    -- `h₄` is stated at `p₁ (p K)`, the goal at the definitionally equal `(p ⋙ p₁) K`
    erw [reassoc_of% h₄]
    rw [reassoc_of% h₅', reassoc_of% h₆, ← reassoc_of% h₇,
      reassoc_of% h₈, ← Q'T.map_comp, ← Q'T.map_comp,
      ← Q'T.map_comp, ← reassoc_of% h₉, hinv, Category.comp_id]
  rw [NatTrans.congr_app key K]
  simp [← Functor.map_comp]

end HomotopyCategory

end CategoryTheory
