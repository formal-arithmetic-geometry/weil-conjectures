/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs

/-!

# The proper base change theorem for constructible `E`- and `ℚ̄_ℓ`-sheaves

Let `ℓ` be a prime and `E` a finite extension of `ℚ_ℓ`, with its normed field structure. Its
condensed ring is `E̲ = C(-, E)` (`Profinite.continuousMapRingObj E`, of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap`), and the coefficient ring
on `X_proét` is `E_X = p_X^* E̲`. Fix a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` **proper**, recorded as `sq : IsPullback g' f' f g`. This file states the proper base
change theorem for bounded constructible `E`-sheaves: the base-change morphism
`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.MorphismDefs` is an
isomorphism of functors `Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y')⟦E̲⟧`. No hypothesis is imposed on `g`. The same
holds for the condensed ring `ℚ̲̄_ℓ` of
`WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic`
(`Profinite.padicAlgClRingObj`), whose sections are continuous maps into finite
subextensions of `ℚ̄_ℓ`.

The proof reduces to the torsion case, the étale proper base change theorem
`AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`, by writing a constructible
`𝒪_E`-complex as the derived limit of its reductions modulo `ϖⁿ` and inverting `ℓ`
(Bhatt–Scholze, Section 6.7); the `ℚ̄_ℓ` case follows by passing to the colimit over the finite
subextensions `E`. Both are currently `sorry`.

As for the bounded constructible six functors
(`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`), all schemes are
separated and of finite type over a field `k` of characteristic `p > 0` with `p ≠ ℓ`, and all
morphisms are morphisms over `Spec k`.

## Main statements

- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper`: proper base
  change on bounded constructible `E`-sheaves.
- `ProEtale.CondensedRing.isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl`: proper
  base change on bounded constructible `ℚ̄_ℓ`-sheaves.

## References

- Bhatt–Scholze, *The pro-étale topology for schemes*, Section 6.7.
- Stacks Project, Section 59.91, *The proper base change theorem*,
  <https://stacks.math.columbia.edu/tag/095S>

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
  (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
  {X Y X' Y' : Scheme.{u}} [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
  [X'.Over (Spec (.of k))] [Y'.Over (Spec (.of k))]
  [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
  [IsSeparated (X ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
  [IsSeparated (Y ↘ Spec (.of k))]
  [LocallyOfFiniteType (X' ↘ Spec (.of k))] [QuasiCompact (X' ↘ Spec (.of k))]
  [IsSeparated (X' ↘ Spec (.of k))]
  [LocallyOfFiniteType (Y' ↘ Spec (.of k))] [QuasiCompact (Y' ↘ Spec (.of k))]
  [IsSeparated (Y' ↘ Spec (.of k))]
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} [f.IsOver (Spec (.of k))]
  [g.IsOver (Spec (.of k))] [f'.IsOver (Spec (.of k))] [g'.IsOver (Spec (.of k))]

include ℓ k in
/-- **The proper base change theorem** for bounded constructible `E`-sheaves, `E` a finite
extension of `ℚ_ℓ`: for a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the base-change morphism `BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is an
isomorphism of functors `Dᵇc(X)⟦E̲⟧ ⥤ Dᵇc(Y')⟦E̲⟧`. -/
theorem isIso_boundedConstructibleBaseChange_of_isProper [IsProper f]
    (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleBaseChange (Profinite.continuousMapRingObj E) ℓ k sq.toCommSq) :=
  sorry

/-- **The proper base change theorem** for bounded constructible `ℚ̄_ℓ`-sheaves: for a cartesian
square of schemes `sq : IsPullback g' f' f g` with `f` proper, the base-change morphism
`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*` is an isomorphism of functors
`Dᵇc(X)⟦ℚ̲̄_ℓ⟧ ⥤ Dᵇc(Y')⟦ℚ̲̄_ℓ⟧`, for the condensed ring
`ℚ̲̄_ℓ = Profinite.padicAlgClRingObj ℓ`. -/
theorem isIso_boundedConstructibleBaseChange_of_isProper_padicAlgCl [IsProper f]
    (sq : IsPullback g' f' f g) :
    IsIso (boundedConstructibleBaseChange
      (Profinite.padicAlgClRingObj ℓ) ℓ k sq.toCommSq) :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
