/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf

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
base-change morphism

`BC_sq(K) : Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)`

of `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs` is an isomorphism. No
hypothesis is imposed on `g`.

Torsion refers to the underlying abelian groups, so the statement contains the two
classical forms of the theorem at once:

- for `Λ = ℤ` it is proper base change for bounded below complexes of abelian sheaves
  with torsion cohomology, as in [SGA 4, Exp. XII, Thm 5.1] and Stacks Project,
  Tag 0DDE;
- for `Λ` torsion as an additive group — in particular for the finite rings
  `Λ = ℤ/ℓⁿℤ` of the `ℓ`-adic formalism — every sheaf of `Λ`-modules is torsion, the
  hypothesis is vacuous, and the base-change transformation itself is an isomorphism of
  functors (`Etale.isIso_baseChange_of_isProper`). The passage between coefficient
  rings is by restriction of scalars, which is exact, conservative, and compatible with
  the base-change mates; see `reference.pdf` in this directory.

## Main statements

- `AlgebraicGeometry.Etale.properBaseChange`: the general proper base change theorem,
  for a bounded below complex with torsion cohomology.
- `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`: for a torsion coefficient
  ring, the base-change transformation of a proper cartesian square is an isomorphism
  of functors.

## References

- Stacks Project, Section 59.91, *The proper base change theorem*,
  <https://stacks.math.columbia.edu/tag/095S>
- Stacks Project, Lemma 59.91.12, the derived statement,
  <https://stacks.math.columbia.edu/tag/0DDE>
- [SGA 4, Exp. XII, Théorème 5.1]

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/- The K-flat resolution package on the coefficient category `ModuleCat.{u + 1} Λ`, as
in `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`. Most of it is
covered by mathlib and by instance search:

- `ModuleCat.{u + 1} Λ` is Grothendieck abelian and symmetric monoidal closed over the
  commutative ring `Λ`, hence in particular braided and preadditive; mathlib insists
  that the ring and the modules live in the same universe, which is why `Λ` is taken in
  `Type (u + 1)`;
- it has all colimits of size `u + 1`, hence — being `Category.{u + 1}` — of size `u` as
  well, by `WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize`;
- being symmetric monoidal *closed* is exactly what
  `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits` needs to
  make the étale sheaf categories monoidal closed by Day's reflection theorem, hence to
  make tensoring by a fixed sheaf preserve colimits; no tensor-colimit hypothesis on the
  coefficient category itself is required.

What remains is the functorial flat resolutions, recorded here with `sorry`. -/
instance : Abelian.HasFunctorialFlatResolution (ModuleCat.{u + 1} Λ) :=
  sorry

/-- `ℤ`-indexed colimits of `Λ`-modules are exact: `ℤ` is a filtered category, and
`ModuleCat.{u + 1} Λ` is Grothendieck abelian, hence satisfies `AB5` for shapes of size
`u + 1`; `AB5OfSize_of_univLE` brings that down to the shapes of size `0` in which `ℤ`
lives. It is not an instance in mathlib because in that generality instance search would
climb the universes. -/
instance : HasExactColimitsOfShape ℤ (ModuleCat.{u + 1} Λ) := by
  have : AB5OfSize.{0, 0} (ModuleCat.{u + 1} Λ) :=
    AB5OfSize_of_univLE.{0, 0, u + 1, u + 1} (ModuleCat.{u + 1} Λ)
  infer_instance

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
cohomology sheaves are torsion, the derived base-change morphism

`BC_sq(K) : Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)`

is an isomorphism in `D⁺(Y'_ét, Λ)`. No hypothesis is imposed on `g`. For `Λ = ℤ` this
is [SGA 4, Exp. XII, Thm 5.1] and Stacks Project, Tag 0DDE; the case of a general
coefficient ring follows by restriction of scalars. -/
theorem Etale.properBaseChange [IsProper g] (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.torsionHomology Λ X K) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  sorry

/-- **Proper base change as an isomorphism of functors**: if the coefficient ring `Λ` is
torsion as an additive group — in particular if `Λ` is finite, e.g. `Λ = ℤ/ℓⁿℤ` — then
for a cartesian square with `f` proper the base-change transformation

`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`

on the bounded below derived categories is an isomorphism: every complex of sheaves of
`Λ`-modules automatically has torsion cohomology. -/
theorem Etale.isIso_baseChange_of_isProper (hΛ : IsAddTorsion Λ) [IsProper g]
    (sq : IsPullback g' f' f g) :
    IsIso (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
  have : ∀ K, IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := fun K ↦
    Etale.properBaseChange Λ sq K
      (Etale.DerivedCategory.Plus.torsionHomology_of_isTorsion Λ X hΛ K)
  NatIso.isIso_of_isIso_app _

end AlgebraicGeometry
