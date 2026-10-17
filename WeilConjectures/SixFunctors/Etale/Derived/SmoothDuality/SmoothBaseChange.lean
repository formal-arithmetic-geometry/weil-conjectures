/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps

/-!
# Arbitrary base change for smooth ambient duality

For a smooth morphism `f : X ⟶ Y` of pure relative dimension `d` admitting a compactification,
with the exponent of `Λ` invertible on `X`, the formation of `Rf^!` commutes with arbitrary base
change (blueprint `prop-asd-smooth-base-change`, of the subsection `sk-prop-sf-cbc`): the
canonical base change map `Lg'^* Rf^! ⟶ Rf'^! Lg^*`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`, the mate of the compact-support
base change) is an isomorphism. Its proof composes the base change compatibility of the
projective-line adjunction with the étale-local charts of `f`; it is recorded here without proof.

## Main statements

- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`,
  `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar`
  (`prop-asd-smooth-base-change`).

## Implementation notes

The canonical base change morphism is the mate of the compact-support base change `Ex_!`, which
is only constructed for a quasi-compact base change `f'`; the existence of a natural isomorphism,
without this hypothesis, is recorded separately.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}}
  [HasInvertibleExponent Λ X]
  (f : X ⟶ Y) [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]

include d in
/-- Blueprint `prop-asd-smooth-base-change`: Arbitrary base change for smooth ambient duality.

Let `f : X ⟶ Y` be as in `AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`
(`thm-asd-smooth-tensor`) and let `g : Y' ⟶ Y` be arbitrary, with base change `f' : X' ⟶ Y'`
and `g' : X' ⟶ X`:

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
`ω_{f'}`. The canonical morphism is only constructed for quasi-compact `f'`. -/
theorem isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension
    {X' Y' : Scheme.{u}} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [HasCompactification f'] [QuasiCompact f'] :
    IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) :=
  sorry

include d in
/-- Blueprint `prop-asd-smooth-base-change`: Arbitrary base change for smooth ambient duality.

Let `f : X ⟶ Y` be as in `AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`
(`thm-asd-smooth-tensor`) and let `g : Y' ⟶ Y` be arbitrary, with base change `f' : X' ⟶ Y'`
and `g' : X' ⟶ X`:

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

The canonical morphism `Lg'^* Rf^! K ⟶ Rf'^! Lg^* K` is an isomorphism for every complex `K`;
at `K = Λ_Y` it identifies `Lg'^* ω_f` with `ω_{f'}`. The canonical morphism, the mate of the
compact-support base change, is only constructed for quasi-compact `f'`
(`AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_smoothOfRelativeDimension`);
for an arbitrary `f'` the existence of a natural isomorphism `Rf^! ⋙ Lg'^* ≅ Lg^* ⋙ Rf'^!` is
recorded. -/
theorem nonempty_iso_rightDerivedUpperShriek_comp_leftDerivedUpperStar {X' Y' : Scheme.{u}}
    {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
    [HasCompactification f'] :
    Nonempty (R(f)^![ModuleCat.{u + 1} Λ] ⋙ L((g')^*[ModuleCat.{u + 1} Λ]) ≅
      L((g)^*[ModuleCat.{u + 1} Λ]) ⋙ R(f')^![ModuleCat.{u + 1} Λ]) :=
  sorry

end Etale

end AlgebraicGeometry
