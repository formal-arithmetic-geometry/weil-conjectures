/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
public import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbModuleComparison

/-!

# The proper base change theorem

For a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper, the derived base-change morphism
`g^* Rf_* K ⟶ Rf'_* g'^* K` is an isomorphism for every bounded below complex of
abelian étale sheaves with torsion cohomology. No hypothesis is imposed on `g`.
The module version uses torsion of the underlying abelian groups of the geometric stalks.
In particular, over a ring torsion as an additive group, every complex satisfies the
cohomological torsion condition.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`: proper base change for a bounded
  below complex of abelian sheaves with torsion cohomology (Stacks 0DDE).
- `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_torsionHomology`: the retained
  module statement, for any commutative coefficient ring and torsion cohomology.
- `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`: over a ring
  torsion as an additive group, the entire bounded below base-change transformation is
  an isomorphism (Stacks 095T).

## References

- Stacks Project, Section 59.91, *The proper base change theorem*,
  <https://stacks.math.columbia.edu/tag/095S>
- Stacks Project, Lemma 59.91.12, the derived statement,
  <https://stacks.math.columbia.edu/tag/0DDE>
- [SGA 4, Exp. XII, Théorème 5.1]

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The proper base change theorem** in étale cohomology: for a cartesian square of
schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper and every bounded below complex `K ∈ D⁺(X_ét, Λ)` all of whose
cohomology sheaves are torsion, the derived base change map

`BC_sq(K) : g^*(Rf_* K) ⟶ Rf'_*(g'^* K)`

is an isomorphism in `D⁺(Y'_ét, Λ)`. No hypothesis is imposed on `g`. For `Λ = ℤ` this
is [SGA 4, Exp. XII, Thm 5.1] and Stacks Project, Tag 0DDE; the case of a general
coefficient ring follows by restriction of scalars. -/
@[stacks 0DDE]
theorem Etale.isIso_baseChange_of_isProper_of_torsionHomology [IsProper f]
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.moduleTorsionHomology Λ X K) :
    IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  Etale.hasTorsionBaseChange_of_isProper Λ f sq K hK

/-- **The proper base change theorem** in étale cohomology: for a cartesian square of
schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` proper and every bounded below complex `K` of abelian étale sheaves all of
whose cohomology sheaves are torsion, the derived base-change morphism
`g^* Rf_* K ⟶ Rf'_* g'^* K` is an isomorphism. No hypothesis is imposed on `g`.
This is [SGA 4, Exp. XII, Thm 5.1] and Stacks Project, Tag 0DDE. -/
@[stacks 0DDE]
theorem Etale.isIso_baseChange_of_isProper [IsProper f] (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology Ab.{u + 1}))
    (hK : Etale.DerivedCategory.Plus.torsionHomology X K) :
    IsIso ((Etale.baseChange Ab.{u + 1} sq.toCommSq).app K) :=
  Etale.isIso_baseChange_of_isProper_of_moduleComparison sq K hK

/-- **Proper base change as an isomorphism of functors**: if the coefficient ring `Λ` is
torsion as an additive group — in particular if `Λ` is finite, e.g. `Λ = ℤ/ℓⁿℤ` — then
for a cartesian square with `f` proper the base-change transformation

`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`

on the bounded below derived categories is an isomorphism: every complex of sheaves of
`Λ`-modules automatically has torsion cohomology. -/
@[stacks 095T]
theorem Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring (hΛ : IsAddTorsion Λ) [IsProper f]
    (sq : IsPullback g' f' f g) :
    IsIso (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq) := by
  rw [Etale.baseChange_eq_derivedBaseChangeMapPlus]
  have : ∀ K, IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
    fun K ↦ Etale.isIso_baseChange_of_isProper_of_torsionHomology Λ sq K
      (Etale.DerivedCategory.Plus.moduleTorsionHomology_of_isTorsion Λ X hΛ K)
  exact NatIso.isIso_of_isIso_app _

/-- **Proper base change on the unbounded derived categories**: if the coefficient ring `Λ` is
torsion as an additive group, then for a cartesian square with `f` proper the derived base
change map

`Ex_* : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`

on the unbounded derived categories `D(-_ét, Λ)` is an isomorphism. This is the unbounded
upgrade of `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`. It
holds because the question is local on `Y`, and over a quasi-compact open of `Y` the proper
map `f` has bounded fibre dimension, so `Rf_*` has finite cohomological dimension on torsion
sheaves and the bounded below statement passes to unbounded complexes. -/
theorem Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring (hΛ : IsAddTorsion Λ)
    [IsProper f] (sq : IsPullback g' f' f g) :
    IsIso (Etale.derivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
  sorry

end AlgebraicGeometry
