/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Integral.StalkPatch

/-!
# Vanishing of restricted germs is an open condition on the geometric fibre

Consider a cartesian square
```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```
with `f` integral, a geometric point `y'` of `Y'` with algebraically closed residue field, and
an affine pointed étale neighbourhood `(U₀, u₀)` of `y' ≫ g`. For a germ `d` of `f'_* G` at
`y'` whose restriction to a geometric point `t₀` of `X'` over `y'` vanishes, the restriction of
`d` to every geometric point `t` of `X'` over `y'` whose image in `X` agrees at `(u₀, t ≫ g')`
with `(u₀, t₀ ≫ g')` on finitely many functions on `U₀ ×_Y X` vanishes as well
(`AlgebraicGeometry.Etale.exists_finset_stalkRestrict_eq_zero`).

The germ is a section `σ` of `G` over `V ×_{Y'} X'` for an affine pointed étale neighbourhood
`(V, v)` of `y'` mapping to `U₀`, the vanishing set of `σ` contains a basic open `D(h)` around
`(v, t₀)`, and `V ×_{Y'} X' = V ×_{U₀} (U₀ ×_Y X)` so the value of `h` at `(v, t)` only
depends on the values of finitely many functions on `U₀ ×_Y X` at `(u₀, t ≫ g')`
(`AlgebraicGeometry.Scheme.Hom.exists_finset_appTopPoint_eq_of_isPullback`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped AlgebraicGeometry.Etale

namespace AlgebraicGeometry

open Scheme Scheme.Hom

variable (Λ : Type (u + 1)) [CommRing Λ] {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} [IsIntegralHom f]

end AlgebraicGeometry
