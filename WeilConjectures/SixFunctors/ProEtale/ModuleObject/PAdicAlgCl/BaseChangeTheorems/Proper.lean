/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.BaseChangeTheorems.MorphismDefs

/-!

# The proper base change theorem for bounded constructible module objects over `ℚ̄_ℓ`

Let `ℓ` be a prime and fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` **proper**, recorded as `sq : IsPullback g' f' f g`. This file states the proper base
change theorem for bounded constructible complexes of module objects over `ℚ̄_ℓ,X`:
the base-change morphism `BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.PAdicAlgCl.BaseChangeTheorems.MorphismDefs`
is an isomorphism of functors `Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(Y')⟦ℚ̄_ℓ⟧`. No hypothesis is imposed on `g`.

This is proper base change for `ℚ̄_ℓ`-sheaves. It reduces to proper base change for
`E`-sheaves (`ProEtale.ContinuousMapRing.isIso_boundedConstructibleBaseChange_of_isProper`)
for the finite subextensions `E ⊆ ℚ̄_ℓ` of `ℚ_ℓ`, since a constructible `ℚ̄_ℓ`-complex is defined
over some such `E` and the functors commute with the extension of scalars `ℚ̄_ℓ ⊗_E -`; that
case in turn reduces to the étale proper base change theorem
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper` (Bhatt–Scholze, Section 6.8).

Warning: as for the six functors on `Dᵇc(-)⟦ℚ̄_ℓ⟧`, the hypotheses are deliberately minimal and
are not the ones under which the statement is a theorem. The hypotheses are to be strengthened
when the statement is proved. The finite type
hypotheses on `f'` follow from those on `f` by base change; they are carried as instance
arguments since the base-change morphism needs the restricted pushforward along `f'`.

## Main statements

- `ProEtale.PadicAlgClRing.isIso_boundedConstructibleBaseChange_of_isProper`: proper base
  change on bounded constructible complexes.

## References

- Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.7.
- Stacks Project, Section 59.91, *The proper base change theorem*,
  <https://stacks.math.columbia.edu/tag/095S>

-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProEtale.PadicAlgClRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]

variable {X Y X' Y' : Scheme.{u}}
  [NoetherianSpace X] [NoetherianSpace Y] [NoetherianSpace X'] [NoetherianSpace Y']
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The proper base change theorem** for bounded constructible module objects over `ℚ̄_ℓ`:
for a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the base-change morphism `BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is an
isomorphism of functors `Dᵇc(X)⟦ℚ̄_ℓ⟧ ⥤ Dᵇc(Y')⟦ℚ̄_ℓ⟧`. No hypothesis is imposed on `g`. -/
theorem isIso_boundedConstructibleBaseChange_of_isProper [IsProper f]
    [LocallyOfFiniteType f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleBaseChange ℓ sq.toCommSq) :=
  sorry

end AlgebraicGeometry.ProEtale.PadicAlgClRing
