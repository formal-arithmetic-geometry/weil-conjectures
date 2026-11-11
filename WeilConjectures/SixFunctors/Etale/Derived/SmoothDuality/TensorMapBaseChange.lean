/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.EtaleDualityBaseChange
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction

/-!
# Base change of the tensor maps of the exceptional inverse image

For a cartesian square `g' ≫ f = f' ≫ g` with `f'` quasi-compact, the base change map
`β : Lg'^* Rf^! ⟶ Rf'^! Lg^*` (`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`)
intertwines the tensor maps `Rf^! M ⊗ᴸ Lf^* N ⟶ Rf^!(M ⊗ᴸ N)` of `f` and of `f'`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap`), the co-projection maps of
`lem-pur-coprojection`. This is `CategoryTheory.Adjunction.projectionTensorMap_mateEquiv` for the
compatibility of the projection map with base change
(`AlgebraicGeometry.Etale.projectionMap_rightDerivedLowerShriekBaseChangeMap`).

## Main statements

- `AlgebraicGeometry.Etale.rightDerivedUpperShriekTensorMap_baseChange`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

-- The instances of
-- `WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.EtaleDualityBaseChange`, under which
-- the base change of the projection map matches syntactically.
attribute [local instance high] SymmetricCategory.toBraidedCategory

attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' f' f g) [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

/-- **Base change of the co-projection.** The base change map `β : Lg'^* Rf^! ⟶ Rf'^! Lg^*`
intertwines the tensor maps of `f` and `f'`:
```
Lg'^*(Rf^! M ⊗ Lf^* N) ──Lg'^* τ──▶ Lg'^* Rf^!(M ⊗ N) ──β──▶ Rf'^! Lg^*(M ⊗ N)
        ≅ │                                                   │ ≅
          ▼                                                   ▼
Lg'^* Rf^! M ⊗ Lg'^* Lf^* N ──β ⊗ κ──▶ Rf'^! Lg^* M ⊗ Lf'^* Lg^* N ──τ'──▶ Rf'^!(Lg^* M ⊗ Lg^* N)
```
-/
theorem rightDerivedUpperShriekTensorMap_baseChange
    (M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((g')^*[ModuleCat.{u + 1} Λ])).map (rightDerivedUpperShriekTensorMap f M N) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ sq).app (M ⊗ N) ≫
          (R(f')^![Λ]).map (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g M N).hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g' _ _).hom ≫
        (rightDerivedUpperShriekBaseChangeMap Λ sq).app M ▷ _ ≫
          _ ◁ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq N ≫
            rightDerivedUpperShriekTensorMap f' _ _ := by
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  have hlib := projectionMap_rightDerivedLowerShriekBaseChangeMap Λ sq
  simp only [← leftDerivedUpperStarTensorIso_hom] at hlib
  exact Adjunction.projectionTensorMap_mateEquiv
    (rightDerivedUpperShriekAdjunction Λ f)
    (rightDerivedUpperShriekAdjunction Λ f')
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f).app M).app N)
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f').app M).app N)
    (projectionMap_app_app_naturality_left f')
    (fun M M' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g' M M').hom)
    (fun N N' ↦ (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g N N').hom)
    (fun φ N'' ↦ leftDerivedUpperStarTensorIso_hom_naturality_left g φ N'')
    (fun N ↦ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq N)
    (rightDerivedLowerShriekBaseChangeMap Λ sq) (inv (rightDerivedLowerShriekBaseChangeMap Λ sq))
    (fun M ↦ by simp [NatIso.isIso_inv_app]) hlib M N

omit [Finite Λ] in
/-- The monoidal computation behind
`AlgebraicGeometry.Etale.dualizingComplexTensorMap_baseChange`. -/
private lemma dualizingComplexTensorMap_baseChange_aux {C : Type*} [Category* C]
    [MonoidalCategory C] {P Q Q₁ R R₂ R₃ R₄ W V U M M' : C} (lμ : P ⟶ Q₁) (lt : P ⟶ Q)
    (ll : Q ⟶ Q₁) (bK : Q₁ ⟶ R) (b1K : Q ⟶ R₂) (rl : R₂ ⟶ R) (rτ : R₂ ⟶ R₃) (ru : R₃ ⟶ R₄)
    (rl' : R₄ ⟶ R) (τ : P ⟶ W ⊗ M) (B : W ⟶ V) (c : M ⟶ M') (t : V ⊗ M' ⟶ R₃) (Ru : V ⟶ U)
    (t₁ : U ⊗ M' ⟶ R₄) (μ : U ⊗ M' ⟶ R) (hμ : lμ = lt ≫ ll) (hμ' : μ = t₁ ≫ rl')
    (hnat : ll ≫ bK = b1K ≫ rl) (hl : rl = rτ ≫ ru ≫ rl')
    (h : lt ≫ b1K ≫ rτ = τ ≫ B ▷ M ≫ V ◁ c ≫ t) (hu : Ru ▷ M' ≫ t₁ = t ≫ ru) :
    lμ ≫ bK = τ ≫ (B ≫ Ru) ▷ M ≫ U ◁ c ≫ μ := by
  rw [hμ, hμ', Category.assoc, hnat, hl, reassoc_of% h, ← reassoc_of% hu, comp_whiskerRight,
    Category.assoc, whisker_exchange_assoc]

/-- **Base change of the canonical tensor map** `μ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K`
(`AlgebraicGeometry.Etale.dualizingComplexTensorMap`): the base change map
`β : Lg'^* Rf^! ⟶ Rf'^! Lg^*` intertwines `Lg'^* μ_{f,K}` with `μ_{f', Lg^* K}`, through the
tensor structure of `Lg'^*`, the base change `Lg'^* ω_f ⟶ Rf'^! Lg^* Λ_Y ≅ ω_{f'}` of the
dualizing complexes and `Lg'^* Lf^* ≅ Lf'^* Lg^*`. -/
theorem dualizingComplexTensorMap_baseChange
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((g')^*[ModuleCat.{u + 1} Λ])).map (dualizingComplexTensorMap Λ f K) ≫
        (rightDerivedUpperShriekBaseChangeMap Λ sq).app K =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) g' _ _).hom ≫
        ((rightDerivedUpperShriekBaseChangeMap Λ sq).app (𝟙_ _) ≫
          (R(f')^![Λ]).map (leftDerivedUpperStarUnitIso _ g).hom) ▷ _ ≫
          _ ◁ derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq K ≫
            dualizingComplexTensorMap Λ f' ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) := by
  have h := rightDerivedUpperShriekTensorMap_baseChange sq (𝟙_ _) K
  have hnat := (rightDerivedUpperShriekBaseChangeMap Λ sq).naturality (λ_ K).hom
  simp only [Functor.comp_map] at hnat
  have hlu := leftDerivedUpperStar_map_derivedTensorLeftUnitor_hom g K
  rw [derivedTensor_map_app, ← leftDerivedUpperStarUnitIso_hom_eq_η] at hlu
  have hl := Adjunction.projectionTensorMap_naturality_left (rightDerivedUpperShriekAdjunction Λ f')
    (fun M N ↦ ((projectionMap (ModuleCat.{u + 1} Λ) f').app M).app N)
    (projectionMap_app_app_naturality_left f') (leftDerivedUpperStarUnitIso _ g).hom
    ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K)
  exact dualizingComplexTensorMap_baseChange_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((L((g')^*[ModuleCat.{u + 1} Λ])).map_comp _ _) rfl hnat
    (by simp only [← Functor.map_comp]; exact congrArg (R(f')^![Λ]).map hlu) h hl

end Etale

end AlgebraicGeometry
