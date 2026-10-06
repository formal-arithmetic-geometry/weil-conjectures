/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective
public import WeilConjectures.AlgebraicGeometry.Picard.Defs

/-!
# The Picard functor of a curve with a rational point

Let `X` be a smooth projective curve over a field `k`.  Then `𝒪_T ⟶ f_{T,*} 𝒪_{X_T}` is an
isomorphism for every `k`-scheme `T`, so the hypotheses of the split exact sequence
`0 → Pic T → Pic (X_T) → Pic_{X/k}(T) → 0` of `WeilConjectures/AlgebraicGeometry/Picard/Defs.lean`
hold as soon as `X` has a `k`-rational point `σ`.  Consequently the `σ`-normalized Picard functor
`Pic_{X/k,σ}` is isomorphic to the relative Picard functor `Pic_{X/k}`.

## Main statements

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

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **The structure sheaf pushes forward to the structure sheaf.** Let `X` be a proper scheme over
a field `k` with `H⁰(X, 𝒪_X) = k`, and let `T` be a `k`-scheme.  Then the canonical map
`𝒪_T ⟶ f_{T,*} 𝒪_{X_T}` is an isomorphism, where `f_T : X_T ⟶ T` is the base change of
`X ⟶ Spec k`.

On an affine open `V = Spec A` of `T`, flat base change along the flat map `k ⟶ A` gives
`Γ(X_V, 𝒪_{X_V}) = H⁰(X, 𝒪_X) ⊗_k A = A`, compatibly with localization.

(blueprint: `lem-pc-structure-pushforward`) -/
theorem isIso_pushforwardUnitMap_pullback_snd [IsProper (X ↘ Spec (.of k))]
    [GlobalSectionsBijective k X] (T : Over (Spec (.of k))) :
    IsIso (pushforwardUnitMap (pullback.snd (X ↘ Spec (.of k)) T.hom)) :=
  sorry

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
