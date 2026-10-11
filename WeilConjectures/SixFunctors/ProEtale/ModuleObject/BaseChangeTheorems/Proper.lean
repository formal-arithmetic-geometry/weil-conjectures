/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

/-!

# The proper base change theorem for bounded constructible module objects over `Λ`

Let `Λ` be a commutative condensed ring and fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` **proper**, recorded as `sq : IsPullback g' f' f g`. This file states the proper base
change theorem for bounded constructible complexes of module objects over `Λ_X = p_X^* Λ`:
the base-change morphism `BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs`
is an isomorphism of functors `Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y')⟦Λ⟧`. No hypothesis is imposed on `g`.

For `Λ = E` a finite extension of `ℚ_ℓ` (or its ring of integers `𝒪_E`) this is proper base
change for `E`-sheaves: it reduces to the torsion case, the étale proper base change theorem
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`, by writing a constructible
`𝒪_E`-complex as the derived limit of its reductions modulo `ϖⁿ` and inverting `ℓ`
(Bhatt–Scholze, Section 6.7).

Warning: as for the six functors on `Dᵇc(-)⟦Λ⟧`, the hypotheses are deliberately minimal and are
not the ones under which the statement is a theorem: the coefficient ring `Λ` should be `𝒪_E` or
`E`. The hypotheses are to be strengthened when the statement is proved. The finite type
hypotheses on `f'` follow from those on `f` by base change; they are carried as instance
arguments since the base-change morphism needs the restricted pushforward along `f'`.

## Main statements

- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper`: proper base
  change on bounded constructible complexes.

## References

- Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.7.
- Stacks Project, Section 59.91, *The proper base change theorem*,
  <https://stacks.math.columbia.edu/tag/095S>

-/

@[expose] public section

universe u

open scoped CategoryTheory.Obj

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

variable {X Y X' Y' : Scheme.{u}}
  [NoetherianSpace X] [NoetherianSpace Y] [NoetherianSpace X'] [NoetherianSpace Y']
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The proper base change theorem** for bounded constructible module objects over `Λ`:
for a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the base-change morphism `BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is an
isomorphism of functors `Dᵇc(X)⟦Λ⟧ ⥤ Dᵇc(Y')⟦Λ⟧`. No hypothesis is imposed on `g`. -/
theorem isIso_boundedConstructibleBaseChange_of_isProper [IsProper f]
    [LocallyOfFiniteType f'] [QuasiCompact f'] (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleBaseChange Λ sq.toCommSq) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
