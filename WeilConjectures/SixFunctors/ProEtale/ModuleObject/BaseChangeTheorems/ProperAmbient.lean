/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing

/-!

# The proper base change theorem along an arbitrary base change

For a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` a proper morphism of separated schemes of finite type over a field of characteristic
`p ≠ ℓ`, the base change map `Lg^* Rf_* ⟶ Rf'_* Lg'^*` on the ambient derived categories
(`ProEtale.CondensedRing.baseChangeMap`) is an isomorphism on bounded constructible
`ℚ̄_ℓ`-complexes, with no hypothesis on `g` (blueprint `sk-thm-sfb-proper-base-change`,
`ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isProper`). Unlike
`ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`, the schemes
`X'` and `Y'` need not be of finite type over the base field: this covers the base change to an
algebraic closure.

## Sorried input

- `ProEtale.CondensedRing.isIso_baseChangeMap_app_of_isProper`: the proper base change theorem,
  blueprint `sk-thm-sfb-proper-base-change` (section `sec-six-functors-basics`).

## References

- Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.7.
- Stacks Project, Section 59.91, *The proper base change theorem*,
  <https://stacks.math.columbia.edu/tag/095S>
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k] [Fact (ringChar k).Prime]
  [Fact (ringChar k ≠ ℓ)] {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom] [LocallyOfFiniteType Y.hom]
  [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y.left} {f' : X' ⟶ Y'} {g' : X' ⟶ X.left}

include ℓ in
/-- **The proper base change theorem** (blueprint `sk-thm-sfb-proper-base-change`) for bounded
constructible `ℚ̄_ℓ`-complexes, along an arbitrary base change: for a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` a proper morphism of separated schemes of finite type over a field of characteristic
`p ≠ ℓ`, and `K` a bounded constructible complex on `X`, the base change map
`Lg^* Rf_* K ⟶ Rf'_* Lg'^* K` is an isomorphism. No hypothesis is imposed on `g`. -/
theorem isIso_baseChangeMap_app_of_isProper [IsProper f.left]
    (sq : IsPullback g' f' f.left g)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left)))
    (hK : boundedConstructible (condensedRingObj (Profinite.padicAlgClRingObj ℓ) X.left) K) :
    IsIso ((baseChangeMap (Profinite.padicAlgClRingObj ℓ) sq.toCommSq).app K) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
