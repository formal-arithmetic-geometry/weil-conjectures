/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.SeparablyClosed
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget

/-!
# The underived proper base change

For a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the underived base change map `g^* f_* F ⟶ f'_* g'^* F` of
`AlgebraicGeometry.Etale.baseChangeMap` is an isomorphism for every étale sheaf `F` of
`Λ`-modules on `X`. At a geometric point `ȳ'` of `Y'` lying over the geometric point `ȳ` of
`Y`, both stalks are the sections of `F` over the same closed geometric fibre
`X_ȳ = X'_ȳ'`: the stalk of `f_* F` at `ȳ` is `Γ(X ×_Y Y_(ȳ), F|)` over the strict
henselisation, which is `Γ(X_ȳ, F|)` by the degree-zero comparison over a strictly henselian
base, and likewise for `f'`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeMap_of_isProper`: the underived proper base change.

## References

- Stacks Project, Lemma 59.91.5, <https://stacks.math.columbia.edu/tag/0A3T>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

open Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The underived proper exchange is an isomorphism**: for a cartesian square

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the base change map `g^* f_* F ⟶ f'_* g'^* F` is an isomorphism for every
étale sheaf `F` of `Λ`-modules on `X`. At a geometric point `ȳ'` of `Y'` both stalks are the
sections of `F` over the closed geometric fibre `X_ȳ = X'_ȳ'`, by the stalk formula over the
strict henselisation and the degree-zero comparison
`AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_geometricFibre`, and the induced
map of stalks is the identity; geometric stalks are conservative.
(blueprint: `lemma-weil-pbc-proper-underived-exchange`) -/
@[stacks 0A3T]
theorem Etale.isIso_baseChangeMap_of_isProper {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X}
    {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : IsPullback g' f' f g) [IsProper f] :
    IsIso (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
  sorry

end AlgebraicGeometry
