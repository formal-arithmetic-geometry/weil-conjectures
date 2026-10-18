/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

/-!

# Coherence of the compact-support base change on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧`

This file records the pasting laws of the compact-support base change `Ex_!` and its comparison
with the direct-image base change `Ex_*` for proper vertical maps, and derives the compatibility
of `Ex_!` with the units of `Lf^* ⊣ Rf_!` for proper `f`.

## Sorried input

- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz`,
  `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert`: the
  exchange of a pasted cartesian rectangle is the composite of the exchanges of the two squares
  (blueprint `fix-lem-exchanges`, item (2)).
- `ProEtale.CondensedRing.boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper`: for
  proper vertical maps, `Ex_!` is `Ex_*` through `Rf_! ≅ Rf_*` (blueprint
  `def-exchange-projection`, the compactification `f = f ∘ 𝟙`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)]

section Pasting

variable {X₁ X₂ X₃ Y₁ Y₂ Y₃ : Over (Spec (.of k))}
  [LocallyOfFiniteType X₁.hom] [QuasiCompact X₁.hom] [IsSeparated X₁.hom]
  [LocallyOfFiniteType X₂.hom] [QuasiCompact X₂.hom] [IsSeparated X₂.hom]
  [LocallyOfFiniteType X₃.hom] [QuasiCompact X₃.hom] [IsSeparated X₃.hom]
  [LocallyOfFiniteType Y₁.hom] [QuasiCompact Y₁.hom] [IsSeparated Y₁.hom]
  [LocallyOfFiniteType Y₂.hom] [QuasiCompact Y₂.hom] [IsSeparated Y₂.hom]
  [LocallyOfFiniteType Y₃.hom] [QuasiCompact Y₃.hom] [IsSeparated Y₃.hom]

/-- **Horizontal pasting of `Ex_!`** (blueprint `fix-lem-exchanges`, item (2)): for cartesian
squares `g'₁ ≫ f₂ = f₁ ≫ g₁` and `g'₂ ≫ f = f₂ ≫ g₂`, the exchange of the outer rectangle is
`L(g₁ ≫ g₂)^* Rf_! ≅ Lg₁^* Lg₂^* Rf_! ⟶ Lg₁^* Rf₂_! Lg'₂^* ⟶ Rf₁_! Lg'₁^* Lg'₂^*
≅ Rf₁_! L(g'₁ ≫ g'₂)^*`. -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_horiz
    {g'₁ : X₁ ⟶ X₂} {g'₂ : X₂ ⟶ X₃} {f₁ : X₁ ⟶ Y₁} {f₂ : X₂ ⟶ Y₂} {f : X₃ ⟶ Y₃}
    {g₁ : Y₁ ⟶ Y₂} {g₂ : Y₂ ⟶ Y₃} (sq₁ : IsPullback g'₁ f₁ f₂ g₁) (sq₂ : IsPullback g'₂ f₂ f g₂)
    (K : Dᵇc(X₃.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (sq₁.paste_horiz sq₂)).app K =
      (boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g₁ g₂).hom.app
          ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f).obj K) ≫
        (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g₁).map
          ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₂).app K) ≫
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₁).app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g'₂).obj K) ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f₁).map
          ((boundedConstructibleUpperStarComp (Profinite.padicAlgClRingObj ℓ) ℓ g'₁ g'₂).inv.app
            K) :=
  sorry

/-- **Vertical pasting of `Ex_!`** (blueprint `fix-lem-exchanges`, item (2)): for cartesian
squares `h ≫ v₂ = v₁ ≫ k` and `k ≫ w₂ = w₁ ≫ l`, the exchange of the outer rectangle is
`Ll^* R(v₂ ≫ w₂)_! ≅ Ll^* Rw₂_! Rv₂_! ⟶ Rw₁_! Lk^* Rv₂_! ⟶ Rw₁_! Rv₁_! Lh^*
≅ R(v₁ ≫ w₁)_! Lh^*`. -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_paste_vert
    {h : X₁ ⟶ X₂} {v₁ : X₁ ⟶ Y₁} {v₂ : X₂ ⟶ Y₂} {k : Y₁ ⟶ Y₂} {w₁ : Y₁ ⟶ X₃} {w₂ : Y₂ ⟶ Y₃}
    {l : X₃ ⟶ Y₃} (sq₁ : IsPullback h v₁ v₂ k) (sq₂ : IsPullback k w₁ w₂ l)
    (M : Dᵇc(X₂.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ (sq₁.paste_vert sq₂)).app M =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ l).map
          ((boundedConstructibleLowerShriekComp_padicAlgCl ℓ v₂ w₂).hom.app M) ≫
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₂).app
          ((boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ v₂).obj M) ≫
        (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ w₁).map
          ((boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₁).app M) ≫
        (boundedConstructibleLowerShriekComp_padicAlgCl ℓ v₁ w₁).inv.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ h).obj M) :=
  sorry

end Pasting

section Proper

variable {X Y X' Y' : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom] [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom]
  [IsSeparated X'.hom] [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **`Ex_!` for proper vertical maps is `Ex_*`** (blueprint `def-exchange-projection`: `Ex_!` is
represented by `Ex_*` for the compactification `f = f ∘ 𝟙` of a proper `f`): under the
identifications `Rf_! ≅ Rf_*` and `Rf'_! ≅ Rf'_*`, the compact-support base change of a
cartesian square with `f` and `f'` proper is the direct-image base change. -/
theorem boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper
    (sq : IsPullback g' f' f g) [IsProper f.left] [IsProper f'.left]
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app K ≫
        (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f').hom.app
          ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g').obj K) =
      (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
          ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).hom.app K) ≫
        (boundedConstructibleBaseChange (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq).app K :=
  sorry

/-- The exchange `Rf ⋙ G ⟶ G' ⋙ Rf'` of an isomorphism `θ : G ⋙ Lf' ≅ Lf ⋙ G'` along the
adjunctions `Lf ⊣ Rf` and `Lf' ⊣ Rf'` is compatible with the units. -/
lemma Adjunction.map_unit_app_comp_exchangeRight_app {A B A' B' : Type*} [Category A] [Category B]
    [Category A'] [Category B'] {Lf : B ⥤ A} {Rf : A ⥤ B} {Lf' : B' ⥤ A'} {Rf' : A' ⥤ B'}
    {G : B ⥤ B'} {G' : A ⥤ A'} (af : Lf ⊣ Rf) (af' : Lf' ⊣ Rf') (θ : G ⋙ Lf' ≅ Lf ⋙ G')
    (M : B) :
    G.map (af.unit.app M) ≫ (Adjunction.exchangeRight af af' θ).app (Lf.obj M) =
      af'.unit.app (G.obj M) ≫ Rf'.map (θ.hom.app M) := by
  rw [Adjunction.exchangeRight_app]
  erw [← af'.unit_naturality_assoc]
  rw [← Rf'.map_comp_assoc, ← Rf'.map_comp]
  have hθ := θ.hom.naturality (af.unit.app M)
  simp only [Functor.comp_map] at hθ
  erw [hθ]
  rw [Category.assoc, ← G'.map_comp]
  erw [af.left_triangle_components]
  simp

/-- **`Ex_!` is compatible with the units of `Lf^* ⊣ Rf_!`** for proper vertical maps:
`Lg^*(η_f) ≫ Ex_! = η_{f'} ≫ Rf'_!(θ_sq)` with `θ_sq : Lg^* Lf'^* ≅ Lf^* Lg'^*`. -/
lemma map_unit_app_comp_boundedConstructibleLowerShriekBaseChange_padicAlgCl_app
    (sq : IsPullback g' f' f g) [IsProper f.left] [IsProper f'.left]
    (M : Dᵇc(Y.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).map
        ((boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f).unit.app M) ≫
      (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq).app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M) =
    (boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl ℓ f').unit.app
        ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g).obj M) ≫
      (boundedConstructibleLowerShriek (Profinite.padicAlgClRingObj ℓ) ℓ f').map
        ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
          sq.toCommSq).hom.app M) := by
  have hP := boundedConstructibleLowerShriekBaseChange_padicAlgCl_of_isProper ℓ sq
    ((boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ f).obj M)
  have hU := Adjunction.map_unit_app_comp_exchangeRight_app
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ f)
    (boundedConstructibleUpperStarLowerStarAdjunction (Profinite.padicAlgClRingObj ℓ) ℓ f')
    (boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ sq.toCommSq)
    M
  rw [← boundedConstructibleBaseChange_eq_exchangeRight] at hU
  have hn := (boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f').inv.naturality
    ((boundedConstructiblePullbackSquareComparison (Profinite.padicAlgClRingObj ℓ) ℓ
      sq.toCommSq).hom.app M)
  simp only [boundedConstructibleUpperStarLowerShriekAdjunction_padicAlgCl,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.map_comp, Category.assoc]
  rw [← cancel_mono ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f').hom.app _)]
  simp only [Category.assoc]
  rw [hP, ← Functor.map_comp_assoc
    (boundedConstructibleUpperStar (Profinite.padicAlgClRingObj ℓ) ℓ g)
    ((boundedConstructibleLowerShriekIsoLowerStar_padicAlgCl ℓ f).inv.app _), Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hU]
  erw [← reassoc_of% hn, Iso.inv_hom_id_app, Category.comp_id]

/-- The compact-support base changes of squares with equal sides agree up to the casts. -/
lemma boundedConstructibleLowerShriekBaseChange_padicAlgCl_congr_app
    {g'₁ g'₂ : X' ⟶ X} {f'₁ f'₂ : X' ⟶ Y'} {f₁ f₂ : X ⟶ Y} {g₁ g₂ : Y' ⟶ Y}
    (sq₁ : IsPullback g'₁ f'₁ f₁ g₁) (sq₂ : IsPullback g'₂ f'₂ f₂ g₂) (h₁ : g'₁ = g'₂)
    (h₂ : f'₁ = f'₂) (h₃ : f₁ = f₂) (h₄ : g₁ = g₂)
    (K : Dᵇc(X.left)⟦Profinite.padicAlgClRingObj ℓ⟧) :
    (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₁).app K =
      eqToHom (by subst h₃ h₄; rfl) ≫
        (boundedConstructibleLowerShriekBaseChange_padicAlgCl ℓ sq₂).app K ≫
        eqToHom (by subst h₁ h₂; rfl) := by
  subst h₁ h₂ h₃ h₄
  simp

end Proper

end AlgebraicGeometry.ProEtale.CondensedRing
