/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.BaseChangeTheorems.MorphismDefs

/-!

# The proper base change theorem for bounded constructible module objects over `C(-, T)`

Let `T` be a commutative topological ring and fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` **proper**, recorded as `sq : IsPullback g' f' f g`. This file states the proper base
change theorem for bounded constructible complexes of module objects over `A_X(T) = C(-, T)`:
the base-change morphism `BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteExtension.BaseChangeTheorems.MorphismDefs`
is an isomorphism of functors `Dᵇc(X)⟦T⟧ ⥤ Dᵇc(Y')⟦T⟧`. No hypothesis is imposed on `g`.

For `T = E` a finite extension of `ℚ_ℓ` (or its ring of integers `𝒪_E`) this is proper base
change for `E`-sheaves: it reduces to the torsion case, the étale proper base change theorem
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`, by writing a constructible
`𝒪_E`-complex as the derived limit of its reductions modulo `ϖⁿ` and inverting `ℓ`
(Bhatt–Scholze, Section 6.7).

Warning: as for the six functors on `Dᵇc(-)⟦T⟧`, the hypotheses are deliberately minimal and are
not the ones under which the statement is a theorem: the coefficient ring `T` should be `𝒪_E` or
`E`. The hypotheses are to be strengthened when the statement is proved. The finite type
hypotheses on `f'` follow from those on `f` by base change; they are carried as instance
arguments since the base-change morphism needs the restricted pushforward along `f'`.

## Main statements

- `ProEtale.ContinuousMapRing.isIso_boundedConstructibleBaseChange_of_isProper`: proper base
  change on bounded constructible complexes.

## References

- Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.7.
- Stacks Project, Section 59.91, *The proper base change theorem*,
  <https://stacks.math.columbia.edu/tag/095S>

-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProEtale.ContinuousMapRing

open Scheme

variable (T : Type) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]

variable {X Y X' Y' : Scheme.{u}}
  [NoetherianSpace X] [NoetherianSpace Y] [NoetherianSpace X'] [NoetherianSpace Y']
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The proper base change theorem** for bounded constructible module objects over `C(-, T)`:
for a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the base-change morphism `BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is an
isomorphism of functors `Dᵇc(X)⟦T⟧ ⥤ Dᵇc(Y')⟦T⟧`. No hypothesis is imposed on `g`. -/
theorem isIso_boundedConstructibleBaseChange_of_isProper [IsProper f]
    [LocallyOfFiniteType f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleBaseChange T sq.toCommSq) :=
  sorry

end AlgebraicGeometry.ProEtale.ContinuousMapRing
