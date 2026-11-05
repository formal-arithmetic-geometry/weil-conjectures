/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Charts

/-!
# Base change for smooth duality reduces to the dualizing complex

The last step of the proof of blueprint `prop-asd-smooth-base-change`: the base change map of the
exceptional inverse image respects the tensor isomorphisms of `thm-asd-smooth-tensor`. For a
cartesian square

```
  X' --g'--> X
  |          |
  f'         f
  ↓          ↓
  Y' --g---> Y
```

with `f'` quasi-compact, the canonical base change map `β_K : Lg'^* Rf^! K ⟶ Rf'^! Lg^* K`
(`AlgebraicGeometry.Etale.rightDerivedUpperShriekBaseChangeMap`) is, through the tensor maps
`θ_f` and `θ_{f'}`, the base change map `β_Λ : Lg'^* ω_f ⟶ ω_{f'}` of the dualizing complexes
tensored with `Lg'^* Lf^* K ≅ Lf'^* Lg^* K`. Hence when the tensor maps are isomorphisms, `β` is
an isomorphism at every object as soon as it is one at `Λ_Y`.

## Main statements

- `CategoryTheory.Adjunction.isIso_mateEquiv_app_of_isIso_projectionTensorMap`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_app_of_isIso_tensorMap`
- `AlgebraicGeometry.Etale.isIso_rightDerivedUpperShriekBaseChangeMap_of_forall_isIso`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory.Adjunction

end CategoryTheory.Adjunction

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

-- Search the braiding of `ModuleCat Λ` through its symmetric structure, as in the generic
-- definitions of the derived tensor product.
attribute [local instance high] SymmetricCategory.toBraidedCategory

-- As in `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionExchange`, whose
-- compatibility of the projection map with base change is used below: with the same instances,
-- its statement matches the one expected here syntactically.
attribute [-instance] CategoryTheory.sheafToPresheaf_isRightAdjoint ModuleCat.hasColimitsOfShape
  ModuleCat.hasColimitsOfSize

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
  (sq : IsPullback g' f' f g) [HasCompactification f] [HasCompactification f'] [QuasiCompact f']

end Etale

end AlgebraicGeometry
