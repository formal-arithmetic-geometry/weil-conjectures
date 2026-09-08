/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper

/-!

# The smooth base change theorem

Fix a commutative ring `Λ` and a cartesian square of schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `g` **smooth** and `f` **quasi-compact and quasi-separated**, recorded as
`sq : IsPullback g' f' f g`. This file states the general smooth base change theorem in
étale cohomology: for every object `K` of the bounded below derived category
`D⁺(X_ét, Λ)` whose cohomology sheaves are torsion of orders invertible on `Y`
(`AlgebraicGeometry.Etale.DerivedCategory.Plus.orderInvertibleOn`, stated for the right
vertical arrow `f : X ⟶ Y` of the square, whose target is the base `Y`), the derived
base-change morphism

`BC_sq(K) : Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)`

of `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs` is an isomorphism.

Note where the hypotheses sit: smoothness is asked of the *base-change* morphism `g`, and
`f` only has to be quasi-compact and quasi-separated. This is the opposite arrangement
from the proper base change theorem of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper`, where `f` is proper and
nothing at all is asked of `g`. Everything else is a condition on the coefficient complex
`K`.

Unlike proper base change, smooth base change is false for torsion that is not invertible
on the base — already for `Y` of characteristic `p` and `p`-torsion coefficients, by
Artin–Schreier. The hypothesis on `K` is therefore not bare torsion, as in `Proper.lean`,
but torsion whose orders are invertible on `Y`, taken in the concrete form: invertible in
the ring `Γ(Y, 𝒪_Y)` of global sections of `Y`. Both conditions are defined in
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf`.

Two statements are given, as in `Proper.lean`:

- for an **arbitrary** coefficient ring `Λ`, with the invertibility carried by the
  coefficient complex `K` (`Etale.smoothBaseChange`);
- for a coefficient ring `Λ` **all of whose torsion orders are invertible on `Y`**, in
  which case the hypothesis on `K` is vacuous and the base-change transformation itself is
  an isomorphism of functors (`Etale.isIso_baseChange_of_smooth`). Every torsion order
  occurring in a `Λ`-module divides the characteristic of `Λ`, so this condition on the
  ring is exactly `IsUnit ((ringChar Λ : ℕ) : Γ(Y, 𝒪_Y))`; for the finite rings
  `Λ = ℤ/ℓⁿℤ` of the `ℓ`-adic formalism it says that `ℓ` is invertible on `Y`.

## Main statements

- `AlgebraicGeometry.Etale.smoothBaseChange`: the general smooth base change theorem, for a
  bounded below complex whose cohomology is torsion of orders invertible on `Y`.
- `AlgebraicGeometry.Etale.isIso_baseChange_of_smooth`: for a coefficient ring whose
  characteristic is invertible on `Y`, the base-change transformation of a cartesian square
  with `g` smooth and `f` quasi-compact quasi-separated is an isomorphism of functors.

## Implementation notes

The file imports `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper` only for the
coefficient package on `ModuleCat.{u + 1} Λ` recorded there — the sorried
`Abelian.HasFunctorialFlatResolution` instance and the `ℤ`-indexed exactness instance —
which `Etale.baseChange` needs; smooth base change is not deduced from proper base change.
Should those instances move to a file shared by the base-change theorems, this import can
be narrowed to `...BaseChangeTheorems.MorphismDefs` and `...BaseChangeTheorems.TorsionSheaf`.

## References

- Stacks Project, Theorem 59.89.2, *Smooth base change*,
  <https://stacks.math.columbia.edu/tag/0EYU>
- Stacks Project, Section 59.89, <https://stacks.math.columbia.edu/tag/0EYQ>
- [SGA 4, Exp. XVI, Théorème 1.1]

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Abelian

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

variable {X Y X' Y' : Scheme.{u}}
  {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- **The smooth base change theorem** in étale cohomology: for a cartesian square of
schemes

```
X' --g'--> X
|          |
f'         f
v          v
Y' --g---> Y
```

with `g` smooth, `f` quasi-compact and quasi-separated, and every bounded below complex
`K ∈ D⁺(X_ét, Λ)` whose cohomology sheaves are torsion of orders invertible on the base `Y`
of the square, the derived base-change morphism

`BC_sq(K) : Lg^*(Rf_* K) ⟶ Rf'_*(Lg'^* K)`

is an isomorphism in `D⁺(Y'_ét, Λ)`.

For `Λ = ℤ` this is [Stacks 0EYU] and [SGA 4, Exp. XVI, Thm 1.1]; the case of a general
coefficient ring follows by restriction of scalars, which is exact, conservative, and
compatible with the base-change mates. -/
theorem Etale.smoothBaseChange [Smooth g] [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : Etale.DerivedCategory.Plus.orderInvertibleOn Λ f K) :
    IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) :=
  sorry

/-- **Smooth base change as an isomorphism of functors**: if the coefficient ring `Λ` is
torsion as an additive group and its characteristic is invertible in `Γ(Y, 𝒪_Y)`, the
global sections of the base `Y` of the square — for the finite rings `Λ = ℤ/ℓⁿℤ` of the
`ℓ`-adic formalism this says that `ℓ` is invertible on `Y` — then for a cartesian square
with `g` smooth and `f` quasi-compact quasi-separated the base-change transformation

`BC_sq : Rf_* ⋙ Lg^* ⟶ Lg'^* ⋙ Rf'_*`

on the bounded below derived categories is an isomorphism: every complex of sheaves of
`Λ`-modules automatically has torsion cohomology, of orders dividing `ringChar Λ` and
hence invertible on `Y`. -/
theorem Etale.isIso_baseChange_of_smooth (hΛ : IsAddTorsion Λ)
    (hY : IsUnit ((ringChar Λ : ℕ) : Γ(Y, ⊤))) [Smooth g] [QuasiCompact f]
    [QuasiSeparated f] (sq : IsPullback g' f' f g) :
    IsIso (Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq) :=
  have : ∀ K, IsIso ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app K) := fun K ↦
    Etale.smoothBaseChange Λ sq K
      (Etale.DerivedCategory.Plus.orderInvertibleOn_of_isUnit_ringChar Λ f hΛ hY K)
  NatIso.isIso_of_isIso_app _

end AlgebraicGeometry
