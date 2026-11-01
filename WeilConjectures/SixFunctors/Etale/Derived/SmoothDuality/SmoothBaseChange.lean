/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineSpaceBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineSpaceTwistAdjunction
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Etale

/-!
# Arbitrary base change for smooth ambient duality

For a smooth morphism `f : X ⟶ Y` of relative dimension `d` admitting a compactification, over a
quasi-separated base `Y`, with the exponent of `Λ` invertible on `X`, the canonical base change
map `Lg'^* Rf^! ⟶ Rf'^! Lg^*` of a cartesian square with quasi-compact `f'` admitting a
compactification is an isomorphism (blueprint `prop-asd-smooth-base-change`).

The proof reduces, through the étale-local normal form of a smooth morphism
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_affineLine`), to the
étale case (`AlgebraicGeometry.Etale.etaleBaseChange`) and to the affine-line case
(`AlgebraicGeometry.Etale.affineLineBaseChange`), which comes from the projective-line adjunction
and gives the base change compatibility of the affine-space adjunction
(`AlgebraicGeometry.Etale.affineSpaceAdjunction_baseChange`, blueprint `sk-lem-geo-affine-local`).

## Main statements

- `AlgebraicGeometry.Etale.affineSpaceAdjunction_baseChange` (`sk-lem-geo-affine-local`)
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`,
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar`
  (`prop-asd-smooth-base-change`).

## Implementation notes

The blueprint works over Noetherian bases. The reduction to charts composes base change maps,
which is only available for quasi-compact base changes; it is therefore made for a
quasi-separated base `Y`, where the affine opens of `X` and `Y` have quasi-compact inclusions.
The canonical base change map, the mate of the compact-support base change, is only constructed
for a quasi-compact base change `f'`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `sk-lem-geo-affine-local`: Affine space and étale localization, clause 1.

"For the projection `a : 𝔸^d_S ⟶ S`, the right adjoint `a^!` of
`Ra_! : D((𝔸^d_S)_proét, Λ) ⥤ D(S_proét, Λ)` is `a^*(d)[2d]`, with unit and counit compatible
with base change."

Both parts are formalised, for every scheme `S` on which the exponent of `Λ` is invertible:

* `a^! = a^*(d)[2d]`: the functor `La^* ⋙ (-)(d)[2d]` is right adjoint to `Ra_!` (as in
  `cor-amb-affine-space-adjunction`,
  `AlgebraicGeometry.Etale.nonempty_rightDerivedLowerShriek_adjunction_affineSpace`), for any
  normalized Tate twist;
* compatibility of the unit and counit of `Ra_! ⊣ Ra^!` with base change: for every cartesian
  square of `a` with quasi-compact base change `p'` admitting a compactification, the
  canonical base change map `Lg'^* Ra^! ⟶ Rp'^! Lg^*` is an isomorphism. This map is the mate
  of the compact-support exchange, so it records exactly how the unit and counit transform
  under base change.

Clause 2 of the node is `lem-amb-etale-adjoint-locality`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar_of_etale`).
-/
theorem affineSpaceAdjunction_baseChange (d : ℕ) (S : Scheme.{u}) [HasInvertibleExponent Λ S] :
    (∀ [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ],
      Nonempty (rightDerivedLowerShriek (ModuleCat.{u + 1} Λ) (𝔸(ULift.{u} (Fin d); S) ↘ S) ⊣
        L(((𝔸(ULift.{u} (Fin d); S) ↘ S))^*[ModuleCat.{u + 1} Λ]) ⋙
          twistShift Λ 𝔸(ULift.{u} (Fin d); S) d)) ∧
    ∀ ⦃S' P' : Scheme.{u}⦄ {g : S' ⟶ S} {p' : P' ⟶ S'}
      {g' : P' ⟶ 𝔸(ULift.{u} (Fin d); S)} (sq : IsPullback g' p' (𝔸(ULift.{u} (Fin d); S) ↘ S) g)
      [HasCompactification p'] [QuasiCompact p'],
      IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) :=
  ⟨nonempty_rightDerivedLowerShriek_adjunction_affineSpace Λ d S, fun _ _ _ _ _ sq _ _ ↦
    isIso_rightDerivedUpperShriekBaseChangeMap_affineSpace (affineLineBaseChange Λ) d S sq⟩

variable {X Y : Scheme.{u}} [QuasiSeparatedSpace Y] [HasInvertibleExponent Λ X]
  (f : X ⟶ Y) [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]

include d in
/-- Blueprint `prop-asd-smooth-base-change`: Arbitrary base change for smooth ambient duality.

Let `f : X ⟶ Y` be smooth of relative dimension `d` and admit a compactification, with the
exponent of `Λ` invertible on `X`, and let `g : Y' ⟶ Y` be arbitrary, with base change
`f' : X' ⟶ Y'` and `g' : X' ⟶ X`:

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

The canonical morphism `Lg'^* Rf^! ⟶ Rf'^! Lg^*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`, the mate of the
compact-support base change) is an isomorphism; at `Λ_Y` it identifies `Lg'^* ω_f` with
`ω_{f'}`. The canonical morphism is only constructed for quasi-compact `f'`. The base `Y` is
assumed quasi-separated (it is Noetherian in the blueprint): the reduction to the étale-local
charts of `f` composes base change maps, which needs quasi-compact base changes. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension
    {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [HasCompactification f'] [QuasiCompact f'] :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) :=
  isIso_rightDerivedUpperShriekBaseChangeMap_of_affineLine Λ (affineLineBaseChange Λ) f d sq

include d in
/-- Blueprint `prop-asd-smooth-base-change`: Arbitrary base change for smooth ambient duality.

Let `f : X ⟶ Y` and the cartesian square be as in
`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`,
over a quasi-separated base `Y` and with `f'` quasi-compact:

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

Then `Rf^! ⋙ Lg'^* ≅ Lg^* ⋙ Rf'^!`, by the canonical morphism; at `K = Λ_Y` it identifies
`Lg'^* ω_f` with `ω_{f'}`. The hypotheses that `Y` be quasi-separated and `f'` quasi-compact
(both automatic in the Noetherian setting of the blueprint) are those under which the canonical
morphism is constructed and shown to be an isomorphism. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar {X' Y' : Scheme.{u}}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [HasCompactification f'] [QuasiCompact f'] :
    Nonempty (R(f)^![Λ] ⋙ L((g')^*[ModuleCat.{u + 1} Λ]) ≅
      L((g)^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')^![Λ]) :=
  have := isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension Λ f d sq
  ⟨asIso (rightDerivedUpperShriekBaseChangeMap Λ sq)⟩

end Etale

end AlgebraicGeometry
