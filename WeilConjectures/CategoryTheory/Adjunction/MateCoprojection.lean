/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.CategoryTheory.Adjunction.MateTransposeIsIso

/-!
# Transporting a co-projection map along functors compatible with adjunctions

Let `L₁ ⊣ R₁` (with `L₁ : C ⥤ D`) and `L₂ ⊣ R₂` (with `L₂ : E ⥤ F`) be adjunctions, and let
`G : C ⥤ E` and `H : D ⥤ F` be functors with an isomorphism `α : G ⋙ L₂ ≅ L₁ ⋙ H` whose mate
`R₁ ⋙ G ⟶ H ⋙ R₂` is invertible.

* `CategoryTheory.Adjunction.exists_iso_map_homEquiv_comp_eq`: if `G` carries a map
  `y : L₁ c ⟶ d` to a map `y'` up to isomorphisms, then it carries the transpose of `y` to the
  transpose of `y'` up to isomorphisms.
* `CategoryTheory.Adjunction.exists_natTrans_map_comp_eq_homEquiv_coprojection`: suppose `E` and
  `F` are monoidal, `C` and `D` carry tensor functors `TC` and `TD` and there are pullbacks
  `PC : D ⥤ C` and `PE : F ⥤ E`. Then a projection formula on `C, D` which lies over a projection
  formula on `E, F` gives a natural co-projection map `PC d ⊗ R₁ 1 ⟶ R₁ d` which lies over the
  co-projection map `PE e ⊗ R₂ 𝟙 ⟶ R₂ e` of `E, F`. The latter is the transpose of
  `L₂ (PE e ⊗ R₂ 𝟙) ≅ L₂ (R₂ 𝟙 ⊗ PE e) ≅ L₂ R₂ 𝟙 ⊗ e ⟶ 𝟙 ⊗ e ≅ e`. Only the existence of
  the comparison isomorphisms is asserted.
-/

@[expose] public section

open scoped CategoryTheory.Prod

namespace CategoryTheory

open MonoidalCategory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  {G : C ⥤ E} {H : D ⥤ F}

/-- Let `α : G ⋙ L₂ ⟶ L₁ ⋙ H` be a square whose mate is invertible at `d`. If `G` carries
`y : L₁ c ⟶ d` to `y' : L₂ e ⟶ H d` up to isomorphisms `ψ : G c ≅ e` and `σ : H d ≅ H d`, then
it carries the transpose `c ⟶ R₁ d` of `y` to the transpose `e ⟶ R₂ (H d)` of `y'` up to
isomorphisms. The hypothesis and the conclusion are the commutative squares
```
L₂ (G c) --α--> H (L₁ c) --H y--> H d        G c --G (y♭)--> G (R₁ d)
   |                               |           |                 |
L₂ ψ                               σ           ψ                 φ
   v                               v           v                 v
L₂ e  ------------y'------------> H d         e  ----y'♭----> R₂ (H d)
```
where `♭` denotes the transposes. -/
theorem Adjunction.exists_iso_map_homEquiv_comp_eq (α : TwoSquare G L₁ L₂ H) {c : C} {e : E}
    {d : D} [IsIso ((mateEquiv adj₁ adj₂ α).natTrans.app d)]
    (y : L₁.obj c ⟶ d) (y' : L₂.obj e ⟶ H.obj d) (ψ : G.obj c ≅ e) (σ : H.obj d ≅ H.obj d)
    (h : α.natTrans.app c ≫ H.map y ≫ σ.hom = L₂.map ψ.hom ≫ y') :
    ∃ φ : G.obj (R₁.obj d) ≅ R₂.obj (H.obj d),
      G.map (adj₁.homEquiv _ _ y) ≫ φ.hom = ψ.hom ≫ adj₂.homEquiv _ _ y' := by
  refine ⟨asIso ((mateEquiv adj₁ adj₂ α).natTrans.app d) ≪≫ R₂.mapIso σ, ?_⟩
  apply (adj₂.homEquiv _ _).symm.injective
  have h₁ := Adjunction.homEquiv_symm_map_comp_app adj₁ adj₂ (mateEquiv adj₁ adj₂ α)
    (adj₁.homEquiv _ _ y)
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at h₁
  rw [Iso.trans_hom, asIso_hom, Functor.mapIso_hom, ← Category.assoc,
    Adjunction.homEquiv_naturality_right_symm, h₁, Category.assoc, h,
    Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]

variable [MonoidalCategory E] [BraidedCategory E] [MonoidalCategory F]

set_option backward.isDefEq.respectTransparency false in
/-- **Transport of the co-projection map.** Let `L₁ ⊣ R₁` and `L₂ ⊣ R₂` be adjunctions, with
`E` and `F` monoidal, and let `α : G ⋙ L₂ ≅ L₁ ⋙ H` have invertible mate. Let `TC`, `TD` be
tensor functors on `C`, `D`, `PC : D ⥤ C`, `PE : F ⥤ E` pullbacks, and
`pf : L₂ M ⊗ K ⟶ L₂ (M ⊗ PE K)` an invertible projection map on `E, F`, natural in `M`. Assume
a projection formula `e : L₁ M ⊗ K ≅ L₁ (M ⊗ PC K)` on `C, D` lies over `pf` through comparisons
`τC`, `τD` of the tensor functors and `γ` of the pullbacks, that is, the square
```
H (L₁ M ⊗ K) ----H e----> H (L₁ (M ⊗ PC K)) --α⁻¹--> L₂ (G (M ⊗ PC K))
     |                                                      |
    τD                                                L₂ (τC ≫ G M ◁ γ)
     v                                                      v
H (L₁ M) ⊗ H K --α⁻¹ ▷ _--> L₂ (G M) ⊗ H K --pf--> L₂ (G M ⊗ PE (H K))
```
commutes, and `TD` has a left unit `one`
(with `H one ≅ 𝟙_ F`) and `TC` a symmetry.

Then there is a co-projection map `PC d ⊗ R₁ one ⟶ R₁ d`, natural in `d`, which `G` carries
to the co-projection map `PE (H d) ⊗ R₂ 𝟙 ⟶ R₂ (H d)` of `E, F` up to isomorphisms. That is,
```
G (PC d ⊗ R₁ one) ----G π_d----> G (R₁ d)
        |                           |
        ψ                           φ
        v                           v
PE (H d) ⊗ R₂ 𝟙 ------------> R₂ (H d)
```
commutes, the bottom map being the transpose of
`L₂ (PE (H d) ⊗ R₂ 𝟙) ≅ L₂ (R₂ 𝟙 ⊗ PE (H d)) ≅ L₂ R₂ 𝟙 ⊗ H d ⟶ 𝟙 ⊗ H d ≅ H d`. -/
theorem Adjunction.exists_natTrans_map_comp_eq_homEquiv_coprojection
    (TC : C × C ⥤ C) (TD : D × D ⥤ D) (PC : D ⥤ C) (PE : F ⥤ E)
    (α : G ⋙ L₂ ≅ L₁ ⋙ H)
    [∀ d, IsIso ((mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α.hom)).natTrans.app d)]
    (τC : TC ⋙ G ≅ G.prod G ⋙ tensor E) (τD : TD ⋙ H ≅ H.prod H ⋙ tensor F)
    (γ : PC ⋙ G ≅ H ⋙ PE)
    (e : L₁.prod (𝟭 D) ⋙ TD ≅ (𝟭 C).prod PC ⋙ TC ⋙ L₁)
    (pf : ∀ M K, L₂.obj M ⊗ K ⟶ L₂.obj (M ⊗ PE.obj K)) [∀ M K, IsIso (pf M K)]
    (hpf : ∀ {M M' : E} (g : M ⟶ M') (K : F),
      L₂.map g ▷ K ≫ pf M' K = pf M K ≫ L₂.map (g ▷ PE.obj K))
    (hcompat : ∀ M K, H.map (e.hom.app (M, K)) ≫ α.inv.app _ ≫
        L₂.map (τC.hom.app (M, PC.obj K) ≫ G.obj M ◁ γ.hom.app K) =
      τD.hom.app (L₁.obj M, K) ≫ α.inv.app M ▷ H.obj K ≫ pf (G.obj M) (H.obj K))
    (b : TC ≅ Prod.swap C C ⋙ TC) (one : D) (u : Prod.sectR one D ⋙ TD ≅ 𝟭 D)
    (υ : H.obj one ≅ 𝟙_ F) :
    ∃ π : PC ⋙ (𝟭 C).prod' ((Functor.const C).obj (R₁.obj one)) ⋙ TC ⟶ R₁,
      ∀ d, ∃ (φ : G.obj (R₁.obj d) ≅ R₂.obj (H.obj d))
        (ψ : G.obj ((PC ⋙ (𝟭 C).prod' ((Functor.const C).obj (R₁.obj one)) ⋙ TC).obj d) ≅
          PE.obj (H.obj d) ⊗ R₂.obj (𝟙_ F)),
        G.map (π.app d) ≫ φ.hom = ψ.hom ≫ adj₂.homEquiv _ _
          (L₂.map (β_ _ _).hom ≫ inv (pf (R₂.obj (𝟙_ F)) (H.obj d)) ≫
            adj₂.counit.app (𝟙_ F) ▷ H.obj d ≫ (λ_ (H.obj d)).hom) := by
  -- the adjoint `L₁ (PC d ⊗ R₁ one) ⟶ d` of the co-projection map
  let c : ∀ d, L₁.obj (TC.obj (PC.obj d, R₁.obj one)) ⟶ d := fun d ↦
    L₁.map (b.hom.app (PC.obj d, R₁.obj one) :
        TC.obj (PC.obj d, R₁.obj one) ⟶ TC.obj (R₁.obj one, PC.obj d)) ≫
      (e.inv.app (R₁.obj one, d) :
        L₁.obj (TC.obj (R₁.obj one, PC.obj d)) ⟶ TD.obj (L₁.obj (R₁.obj one), d)) ≫
      TD.map (adj₁.counit.app one ×ₘ 𝟙 d) ≫ (u.hom.app d : TD.obj (one, d) ⟶ d)
  have hc : ∀ {d d' : D} (g : d ⟶ d'),
      L₁.map (TC.map (PC.map g ×ₘ 𝟙 (R₁.obj one))) ≫ c d' = c d ≫ g := by
    intro d d' g
    have hb : TC.map (PC.map g ×ₘ 𝟙 (R₁.obj one)) ≫ (b.hom.app (PC.obj d', R₁.obj one) :
          TC.obj (PC.obj d', R₁.obj one) ⟶ TC.obj (R₁.obj one, PC.obj d')) =
        (b.hom.app (PC.obj d, R₁.obj one) :
          TC.obj (PC.obj d, R₁.obj one) ⟶ TC.obj (R₁.obj one, PC.obj d)) ≫
          TC.map (𝟙 (R₁.obj one) ×ₘ PC.map g) :=
      b.hom.naturality _
    have he : L₁.map (TC.map (𝟙 (R₁.obj one) ×ₘ PC.map g)) ≫ (e.inv.app (R₁.obj one, d') :
          L₁.obj (TC.obj (R₁.obj one, PC.obj d')) ⟶ TD.obj (L₁.obj (R₁.obj one), d')) =
        (e.inv.app (R₁.obj one, d) :
          L₁.obj (TC.obj (R₁.obj one, PC.obj d)) ⟶ TD.obj (L₁.obj (R₁.obj one), d)) ≫
          TD.map (𝟙 (L₁.obj (R₁.obj one)) ×ₘ g) := by
      have := e.inv.naturality (𝟙 (R₁.obj one) ×ₘ g)
      dsimp at this
      rwa [L₁.map_id] at this
    have hu : TD.map (𝟙 one ×ₘ g) ≫ (u.hom.app d' : TD.obj (one, d') ⟶ d') =
        (u.hom.app d : TD.obj (one, d) ⟶ d) ≫ g :=
      u.hom.naturality g
    have hT : TD.map (𝟙 (L₁.obj (R₁.obj one)) ×ₘ g) ≫ TD.map (adj₁.counit.app one ×ₘ 𝟙 d') =
        TD.map (adj₁.counit.app one ×ₘ 𝟙 d) ≫ TD.map (𝟙 one ×ₘ g) := by
      rw [← TD.map_comp, ← TD.map_comp]
      congr 1
      ext <;> simp
    simp only [c]
    rw [← L₁.map_comp_assoc, hb, L₁.map_comp_assoc, reassoc_of% he]
    rw [reassoc_of% hT, hu]
    simp only [Category.assoc]
  refine ⟨{ app d := adj₁.homEquiv _ _ (c d)
            naturality d d' g := by
              dsimp
              rw [← adj₁.homEquiv_naturality_left, ← adj₁.homEquiv_naturality_right]
              exact congrArg _ (hc g) }, fun d ↦ ?_⟩
  -- the comparison isomorphisms
  let a : G.obj (R₁.obj one) ≅ R₂.obj (𝟙_ F) :=
    asIso ((mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α.hom)).natTrans.app one) ≪≫ R₂.mapIso υ
  let κ : G.obj (TC.obj (R₁.obj one, PC.obj d)) ≅ G.obj (R₁.obj one) ⊗ PE.obj (H.obj d) :=
    τC.app (R₁.obj one, PC.obj d) ≪≫ whiskerLeftIso (G.obj (R₁.obj one)) (γ.app d)
  let ψ : G.obj (TC.obj (PC.obj d, R₁.obj one)) ≅ PE.obj (H.obj d) ⊗ R₂.obj (𝟙_ F) :=
    G.mapIso (b.app (PC.obj d, R₁.obj one)) ≪≫ κ ≪≫ whiskerRightIso a (PE.obj (H.obj d)) ≪≫
      (β_ (PE.obj (H.obj d)) (R₂.obj (𝟙_ F))).symm
  let σ : H.obj d ≅ H.obj d :=
    (H.mapIso (u.app d)).symm ≪≫ τD.app (one, d) ≪≫ whiskerRightIso υ (H.obj d) ≪≫
      λ_ (H.obj d)
  -- the projection formulas
  have hpf' : α.hom.app (TC.obj (R₁.obj one, PC.obj d)) ≫ H.map (e.inv.app (R₁.obj one, d)) ≫
      τD.hom.app (L₁.obj (R₁.obj one), d) =
        L₂.map κ.hom ≫ inv (pf (G.obj (R₁.obj one)) (H.obj d)) ≫
          α.hom.app (R₁.obj one) ▷ H.obj d := by
    have h₂ : H.map (e.hom.app (R₁.obj one, d)) ≫ α.inv.app _ ≫ L₂.map κ.hom ≫
        inv (pf (G.obj (R₁.obj one)) (H.obj d)) ≫ α.hom.app (R₁.obj one) ▷ H.obj d =
          τD.hom.app (L₁.obj (R₁.obj one), d) := by
      have := hcompat (R₁.obj one) d
      simp only [κ, Iso.trans_hom, Iso.app_hom, whiskerLeftIso_hom] at this ⊢
      rw [reassoc_of% this]
      simp [← comp_whiskerRight]
    rw [← h₂]
    simp
  -- the counits
  have hε : α.hom.app (R₁.obj one) ≫ H.map (adj₁.counit.app one) ≫ υ.hom =
      L₂.map a.hom ≫ adj₂.counit.app (𝟙_ F) := by
    have := mateEquiv_counit adj₁ adj₂ (TwoSquare.mk _ _ _ _ α.hom) one
    simp only [a, Iso.trans_hom, asIso_hom, Functor.mapIso_hom, L₂.map_comp, Category.assoc]
    refine ((reassoc_of% this) υ.hom).symm.trans ?_
    exact congrArg (L₂.map _ ≫ ·) (adj₂.counit_naturality υ.hom).symm
  -- the projection map, at `a`
  have hpfa : inv (pf (G.obj (R₁.obj one)) (H.obj d)) ≫ L₂.map a.hom ▷ H.obj d =
      L₂.map (a.hom ▷ PE.obj (H.obj d)) ≫ inv (pf (R₂.obj (𝟙_ F)) (H.obj d)) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← hpf, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  have hτ := τD.hom.naturality (adj₁.counit.app one ×ₘ 𝟙 d)
  have hn := α.hom.naturality (b.hom.app (PC.obj d, R₁.obj one))
  dsimp at hτ hn
  have e₁ : H.map (c d) ≫ σ.hom = H.map (L₁.map (b.hom.app (PC.obj d, R₁.obj one))) ≫
      H.map (e.inv.app (R₁.obj one, d)) ≫ τD.hom.app (L₁.obj (R₁.obj one), d) ≫
        (H.map (adj₁.counit.app one) ≫ υ.hom) ▷ H.obj d ≫ (λ_ (H.obj d)).hom := by
    simp only [c, σ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv, Iso.app_inv, Iso.app_hom,
      H.map_comp, Category.assoc]
    rw [← H.map_comp_assoc (u.hom.app d), Iso.hom_inv_id_app, H.map_id, Category.id_comp,
      reassoc_of% hτ]
    simp [comp_whiskerRight]
  obtain ⟨φ, hφ⟩ := adj₁.exists_iso_map_homEquiv_comp_eq adj₂ (TwoSquare.mk _ _ _ _ α.hom)
    (c d) (L₂.map (β_ _ _).hom ≫ inv (pf (R₂.obj (𝟙_ F)) (H.obj d)) ≫
      adj₂.counit.app (𝟙_ F) ▷ H.obj d ≫ (λ_ (H.obj d)).hom) ψ σ (by
      change α.hom.app _ ≫ H.map (c d) ≫ σ.hom = _
      rw [e₁, ← reassoc_of% hn, reassoc_of% hpf', ← comp_whiskerRight_assoc, ← Category.assoc,
        hε, comp_whiskerRight_assoc, reassoc_of% hpfa]
      simp only [ψ, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, whiskerRightIso_hom,
        Iso.app_hom, L₂.map_comp, Category.assoc]
      rw [← L₂.map_comp_assoc (β_ _ _).inv, Iso.inv_hom_id, L₂.map_id, Category.id_comp])
  exact ⟨φ, ψ, hφ⟩

end CategoryTheory
