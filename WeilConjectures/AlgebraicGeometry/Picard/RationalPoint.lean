/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Picard.Defs
public import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
public import WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator

/-!
# The Picard functor of a curve with a rational point

Let `X` be a smooth projective curve over a field `k`.  Then `𝒪_T ⟶ f_{T,*} 𝒪_{X_T}` is an
isomorphism for every `k`-scheme `T`, so the hypotheses of the split exact sequence
`0 → Pic T → Pic (X_T) → Pic_{X/k}(T) → 0` of `WeilConjectures/AlgebraicGeometry/Picard/Defs.lean`
hold as soon as `X` has a `k`-rational point `σ`.  Consequently the `σ`-normalized Picard functor
`Pic_{X/k,σ}` is isomorphic to the relative Picard functor `Pic_{X/k}`.

## Main statements

- `AlgebraicGeometry.isIso_pushforwardUnitMap_of_globalSectionsBijective`: `f_* 𝒪_X = 𝒪_k` for a
  quasi-compact quasi-separated `k`-scheme `X` with `H⁰(X, 𝒪_X) = k` (blueprint
  `prop-pc-xk-integral`, part (1)).
- `AlgebraicGeometry.isIso_pushforwardUnitMap_pullback_snd`: `f_{T,*} 𝒪_{X_T} = 𝒪_T` for a proper
  `k`-scheme `X` with `H⁰(X, 𝒪_X) = k` (blueprint `lem-pc-structure-pushforward`).
- `AlgebraicGeometry.isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral`: smooth
  projective curves satisfy the hypotheses of the split exact sequence (blueprint
  `lem-pc-rational-hyp`).
- `AlgebraicGeometry.nonempty_picardFunctorNormalized_iso_picardFunctor`: for a smooth projective
  curve with a rational point `σ`, `Pic_{X/k,σ} ≅ Pic_{X/k}` (blueprint `cor-pc-sigma-pic-iso`).

## Implementation notes

As elsewhere in the Picard chapter, a smooth projective curve over `k` is a `k`-scheme `X` with
`X ⟶ Spec k` smooth of relative dimension `1`, proper and geometrically integral.  Geometric
integrality gives `H⁰(X, 𝒪_X) = k` directly
(`AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyIntegral`), so the rational
point is only needed as the section `σ`; the blueprint instead deduces `H⁰(X, 𝒪_X) = k` from the
rational point for an integral `X`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

/-- If `g^♯ : Γ(B, A) ⟶ Γ(Z, g⁻¹ A)` is bijective for every affine open `A` of `B`, then the
canonical map `𝒪_B ⟶ g_* 𝒪_Z` is an isomorphism: on sections over `A` it is `g^♯`. -/
theorem isIso_pushforwardUnitMap_of_bijective_app {Z B : Scheme.{u}} (g : Z ⟶ B)
    (hg : ∀ A : B.Opens, IsAffineOpen A → Function.Bijective (g.app A)) :
    IsIso (pushforwardUnitMap g) := by
  let φ : Modules.unit B ⟶ (Modules.pushforward g).obj (Modules.unit Z) :=
    pushforwardUnitMap g
  have h1 : Modules.Hom.app φ ⊤ (1 : Γ(B, ⊤)) = (1 : Γ(Z, ⊤)) := by
    have h := Modules.pullbackSection_app_one g (𝟙 (Modules.unit B))
    change Modules.Hom.app (Modules.pullbackObjUnitIso g).hom _
      (Modules.pullbackSection g (Modules.Hom.app (𝟙 _) ⊤ (1 : Γ(B, ⊤)))) = (1 : Γ(Z, ⊤))
    rw [h, CategoryTheory.Functor.map_id, Category.comp_id, ← ConcreteCategory.comp_apply,
      ← Modules.Hom.comp_app, Iso.inv_hom_id]
    rfl
  have happ (A : B.Opens) (b : Γ(B, A)) : Modules.Hom.app φ A b = g.app A b := by
    have hA : Modules.Hom.app φ A (1 : Γ(B, A)) = (1 : Γ(Z, g ⁻¹ᵁ A)) := by
      have hn := Modules.Hom.app_presheaf_map φ (homOfLE le_top : A ⟶ ⊤) (1 : Γ(B, ⊤))
      have e1 : (Modules.unit B).presheaf.map (homOfLE le_top : A ⟶ ⊤).op
          (1 : Γ(B, ⊤)) = (1 : Γ(B, A)) :=
        map_one (B.presheaf.map (homOfLE le_top : A ⟶ ⊤).op).hom
      rw [e1, h1] at hn
      exact hn.trans (map_one (Z.presheaf.map
        (homOfLE (g.preimage_mono (le_top : A ≤ ⊤))).op).hom)
    have h2 := Modules.Hom.app_smul φ b (1 : Γ(B, A))
    rw [smul_eq_mul, mul_one] at h2
    rw [h2, hA]
    exact mul_one (g.app A b)
  refine Modules.isIso_of_bijective_app_of_isAffineOpen φ fun A hA ↦ ?_
  rw [show (Modules.Hom.app φ A : Γ(B, A) → _) = g.app A from funext (happ A)]
  exact hg A hA

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **`f_* 𝒪_X = 𝒪_k`.** For a quasi-compact quasi-separated `k`-scheme `X` with
`H⁰(X, 𝒪_X) = k`, e.g. a smooth proper connected scheme over a separably closed field
(`AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_isSepClosed`), the canonical map
`𝒪_{Spec k} ⟶ f_* 𝒪_X` along the structure map `f : X ⟶ Spec k` is an isomorphism.

(blueprint: `prop-pc-xk-integral`, part (1)) -/
theorem isIso_pushforwardUnitMap_of_globalSectionsBijective [CompactSpace X]
    [QuasiSeparatedSpace X] [GlobalSectionsBijective k X] :
    IsIso (pushforwardUnitMap (X ↘ Spec (.of k))) :=
  isIso_pushforwardUnitMap_of_bijective_app _ fun _ hA ↦ by
    have := GlobalSectionsBijective.isIso_app_of_isPullback (k := k) (X := X)
      IsPullback.of_id_fst hA
    exact ConcreteCategory.bijective_of_isIso _

/-- **The structure sheaf pushes forward to the structure sheaf.** Let `X` be a proper scheme over
a field `k` with `H⁰(X, 𝒪_X) = k`, and let `T` be a `k`-scheme.  Then the canonical map
`𝒪_T ⟶ f_{T,*} 𝒪_{X_T}` is an isomorphism, where `f_T : X_T ⟶ T` is the base change of
`X ⟶ Spec k`.

On an affine open `V = Spec A` of `T`, flat base change along the flat map `k ⟶ A` gives
`Γ(X_V, 𝒪_{X_V}) = H⁰(X, 𝒪_X) ⊗_k A = A`, compatibly with localization.

(blueprint: `lem-pc-structure-pushforward`) -/
theorem isIso_pushforwardUnitMap_pullback_snd [IsProper (X ↘ Spec (.of k))]
    [GlobalSectionsBijective k X] (T : Over (Spec (.of k))) :
    IsIso (pushforwardUnitMap (pullback.snd (X ↘ Spec (.of k)) T.hom)) := by
  let π := pullback.snd (X ↘ Spec (.of k)) T.hom
  let φ : Modules.unit T.left ⟶ (Modules.pushforward π).obj (Modules.unit _) :=
    pushforwardUnitMap π
  -- `φ` sends `1` to `1`
  have h1 : Modules.Hom.app φ ⊤ (1 : Γ(T.left, ⊤)) =
      (1 : Γ(pullback (X ↘ Spec (.of k)) T.hom, ⊤)) := by
    have h := Modules.pullbackSection_app_one π (𝟙 (Modules.unit T.left))
    change Modules.Hom.app (Modules.pullbackObjUnitIso π).hom _
      (Modules.pullbackSection π (Modules.Hom.app (𝟙 _) ⊤ (1 : Γ(T.left, ⊤)))) =
        (1 : Γ(pullback (X ↘ Spec (.of k)) T.hom, ⊤))
    rw [h, CategoryTheory.Functor.map_id, Category.comp_id, ← ConcreteCategory.comp_apply,
      ← Modules.Hom.comp_app,
      Iso.inv_hom_id]
    rfl
  -- on sections over `A`, `φ` is `π^♯`
  have happ (A : T.left.Opens) (b : Γ(T.left, A)) : Modules.Hom.app φ A b = π.app A b := by
    have hA : Modules.Hom.app φ A (1 : Γ(T.left, A)) =
        (1 : Γ(pullback (X ↘ Spec (.of k)) T.hom, π ⁻¹ᵁ A)) := by
      have hn := Modules.Hom.app_presheaf_map φ (homOfLE le_top : A ⟶ ⊤) (1 : Γ(T.left, ⊤))
      have e1 : (Modules.unit T.left).presheaf.map (homOfLE le_top : A ⟶ ⊤).op
          (1 : Γ(T.left, ⊤)) = (1 : Γ(T.left, A)) :=
        map_one (T.left.presheaf.map (homOfLE le_top : A ⟶ ⊤).op).hom
      rw [e1, h1] at hn
      exact hn.trans (map_one ((pullback (X ↘ Spec (.of k)) T.hom).presheaf.map
        (homOfLE (π.preimage_mono (le_top : A ≤ ⊤))).op).hom)
    have h2 := Modules.Hom.app_smul φ b (1 : Γ(T.left, A))
    have h3 : b • (1 : Γ(T.left, A)) = b := by rw [smul_eq_mul, mul_one]
    rw [h3] at h2
    rw [h2, hA]
    exact mul_one (π.app A b)
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace (X ↘ Spec (.of k))
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated (X ↘ Spec (.of k))
  refine Modules.isIso_of_bijective_app_of_isAffineOpen φ fun A hA ↦ ?_
  have := GlobalSectionsBijective.isIso_app_of_isPullback (k := k) (X := X)
    (IsPullback.of_hasPullback (X ↘ Spec (.of k)) T.hom) hA
  rw [show (Modules.Hom.app φ A : Γ(T.left, A) → _) = π.app A from funext (happ A)]
  exact ConcreteCategory.bijective_of_isIso _

/-- **Smooth projective curves satisfy the hypotheses of the split exact sequence.** Let `X` be
a smooth projective curve over a field `k`.  Then `𝒪_T ⟶ f_{T,*} 𝒪_{X_T}` is an isomorphism for
every `k`-scheme `T`: `X` is geometrically integral, so `H⁰(X, 𝒪_X) = k`, and this is
`AlgebraicGeometry.isIso_pushforwardUnitMap_pullback_snd`.  Together with a `k`-rational point
`σ`, these are the hypotheses of `AlgebraicGeometry.bijective_pic_split` (Stacks 0B9U).

(blueprint: `lem-pc-rational-hyp`) -/
theorem isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] (T : Over (Spec (.of k))) :
    IsIso (pushforwardUnitMap (pullback.snd (X ↘ Spec (.of k)) T.hom)) :=
  have := GlobalSectionsBijective.of_geometricallyIntegral (k := k) (X := X)
  isIso_pushforwardUnitMap_pullback_snd T

/-- **`Pic_{X/k,σ}` is isomorphic to `Pic_{X/k}`.** Let `X` be a smooth projective curve over a
field `k` with a `k`-rational point `σ`.  Then the inclusion of the `σ`-normalized Picard functor
followed by the sheafification map, `Pic_{X/k,σ} ⟶ Pic_{X/k}`, is an isomorphism of functors on
`(Sch/k)_fppf`: by
`AlgebraicGeometry.isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral` and
`AlgebraicGeometry.bijective_toPicardFunctor_picardFunctorNormalized` it is bijective on the
sections over every `T`.  In particular `Pic_{X/k,σ}` is an fppf sheaf, representable if and only
if `Pic_{X/k}` is.

(blueprint: `cor-pc-sigma-pic-iso`) -/
theorem nonempty_picardFunctorNormalized_iso_picardFunctor
    [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    [GeometricallyIntegral (X ↘ Spec (.of k))] (σ : Spec (.of k) ⟶ X)
    (hσ : σ ≫ X ↘ Spec (.of k) = 𝟙 (Spec (.of k))) :
    Nonempty ((picardFunctorNormalized (X ↘ Spec (.of k)) σ hσ).toFunctor ≅
      (picardFunctor (X ↘ Spec (.of k))).obj) := by
  have : IsIso ((picardFunctorNormalized (X ↘ Spec (.of k)) σ hσ).ι ≫
      toPicardFunctor (X ↘ Spec (.of k))) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro T
    rw [isIso_iff_bijective]
    exact bijective_toPicardFunctor_picardFunctorNormalized _ σ hσ
      isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral T.unop
  exact ⟨asIso ((picardFunctorNormalized (X ↘ Spec (.of k)) σ hσ).ι ≫
    toPicardFunctor (X ↘ Spec (.of k)))⟩

end AlgebraicGeometry
