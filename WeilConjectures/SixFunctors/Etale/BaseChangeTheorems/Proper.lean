/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine

/-!

# The proper base change theorem

Fix a commutative ring `Λ` and a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `f` **proper**, recorded as `sq : IsPullback g' f' f g`. This file states the
general proper base change theorem in étale cohomology: for every object `K` of the
bounded below derived category `D⁺(X_ét, Λ)` all of whose cohomology sheaves are torsion
(`AlgebraicGeometry.Etale.DerivedCategory.Plus.torsionHomology`), the derived
base change map

`BC_sq(K) : g^*(Rf_* K) ⟶ Rf'_*(g'^* K)`

of `WeilConjectures.SixFunctors.BaseChange.Derived` is an isomorphism. No hypothesis is
imposed on `g`.

The theorem is deduced from the two halves of its proof, the projective-line computation
and the reduction to it, in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine`.

Torsion refers to the underlying abelian groups, so the statement contains the two
classical forms of the theorem at once:

- for `Λ = ℤ` it is proper base change for bounded below complexes of abelian sheaves
  with torsion cohomology, as in [SGA 4, Exp. XII, Thm 5.1] and Stacks Project,
  Tag 0DDE;
- for `Λ` torsion as an additive group — in particular for the finite rings
  `Λ = ℤ/ℓⁿℤ` of the `ℓ`-adic formalism — every sheaf of `Λ`-modules is torsion, the
  hypothesis is vacuous, and the base-change transformation itself is an isomorphism of
  functors (`Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`). The passage
  between coefficient rings is by restriction of scalars, which is exact, conservative,
  and compatible with the base change mates; see `reference.pdf` in this directory.

## Implementation notes

`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs` constructs a second
transformation `AlgebraicGeometry.Etale.baseChange` of the same type as
`AlgebraicGeometry.Etale.derivedBaseChangeMapPlus`. The two agree
(`AlgebraicGeometry.Etale.baseChange_eq_derivedBaseChangeMapPlus`). The base change machinery —
the pasting lemmas, the underived-to-derived bridge, and the finite case — is stated for
`derivedBaseChangeMapPlus`, which is also the blueprint's `def-weil-pbc-derived-exchange`, and
the statements below use it as well.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`: the general proper base change
  theorem, for a bounded below complex with torsion cohomology.
- `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring`: for a
  torsion coefficient ring, the base change transformation of a proper cartesian square
  is an isomorphism of functors.
- `AlgebraicGeometry.Etale.isIso_derivedBaseChangeMap_of_isProper_of_isAddTorsion_ring`: the
  same on the unbounded derived categories, for the base change map
  `AlgebraicGeometry.Etale.derivedBaseChangeMap`.

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
theorem Etale.isIso_baseChange_of_isProper [IsProper f] (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.torsionHomology Λ X K) :
    IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  Etale.hasTorsionBaseChange_of_isProper Λ f sq K hK

/-- **Proper base change as an isomorphism of functors**: if the coefficient ring `Λ` is
torsion as an additive group — in particular if `Λ` is finite, e.g. `Λ = ℤ/ℓⁿℤ` — then
for a cartesian square with `f` proper the base change transformation

`BC_sq : Rf_* ⋙ g^* ⟶ g'^* ⋙ Rf'_*`

on the bounded below derived categories is an isomorphism: every complex of sheaves of
`Λ`-modules automatically has torsion cohomology. Equivalently, a proper morphism satisfies
`AlgebraicGeometry.Etale.IsBaseChangeIso` for torsion coefficients. -/
@[stacks 095T]
theorem Etale.isIso_baseChange_of_isProper_of_isAddTorsion_ring (hΛ : IsAddTorsion Λ) [IsProper f]
    (sq : IsPullback g' f' f g) :
    IsIso (Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
  have : ∀ K, IsIso ((Etale.derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
    fun K ↦ Etale.isIso_baseChange_of_isProper Λ sq K
      (Etale.DerivedCategory.Plus.torsionHomology_of_isTorsion Λ X hΛ K)
  NatIso.isIso_of_isIso_app _

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
