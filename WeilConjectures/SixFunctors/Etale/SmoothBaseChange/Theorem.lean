/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction

/-!
# The smooth base change theorem

Fix a Cartesian square of schemes

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `p` **smooth** and `g` quasi-compact quasi-separated. For every sheaf `F` of
`Λ`-modules on `T_ét` all of whose geometric stalks are torsion of orders invertible on `S`
— that is, `AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder` — the base-change map

`p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F`

of `AlgebraicGeometry.Etale.baseChangeHomologyMap` is an isomorphism in every degree `q`.

The proof is the second, shorter proof of the Stacks Project: degree zero is
`AlgebraicGeometry.Etale.baseChangeProperty_zero_of_smooth`; the general coefficient sheaf is
the filtered colimit of its `n`-torsion subsheaves; the assertion is étale local on `X` and
`S`, so by `AlgebraicGeometry.exists_etaleCover_factorization`, the étale-local normal form
`AlgebraicGeometry.Smooth.exists_etale_to_affineSpace` and the factorisation of
`X ⟶ 𝔸^d_S` into relative curves it suffices to treat relative dimension one. There
`AlgebraicGeometry.Etale.universalBaseChangeProperty_of_smoothOfRelativeDimension_one` gives
the base-change property after every base change, by strong induction on `q` on
`AlgebraicGeometry.Etale.UniversalBaseChangeProperty` with step
`AlgebraicGeometry.Etale.UniversalBaseChangeProperty.of_forall_lt`, starting from
`AlgebraicGeometry.Etale.universalBaseChangeProperty_of_neg` and
`AlgebraicGeometry.Etale.universalBaseChangeProperty_zero_of_smooth`. Since the induction
runs on the universal property, the preceding reductions (torsion, étale localisation,
factorisation into relative curves) are to be phrased universally as well, and the proof ends
by specialising along `𝟙 S` with
`AlgebraicGeometry.Etale.UniversalBaseChangeProperty.baseChangeProperty`.

Compare `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`, the proper base change
theorem, in which the roles of the two legs of the square are exchanged.

## Implementation notes

Two steps of that proof have no statement yet, and the theorem below is therefore not
reachable from the statements of this directory alone. Both concern the passage between the
theorem, whose coefficient sheaf is an arbitrary sheaf of `Λ`-modules with torsion geometric
stalks, and `AlgebraicGeometry.Etale.BaseChangeProperty`, which is indexed by a *fixed*
coefficient ring `Λ` and carries no torsion condition:

- the torsion reduction asserted inside the blueprint subsection `sk-def-smooth`: such an `F`
  is the filtered colimit of its `n`-torsion subsheaves over the `n` invertible on `S`, and
  inverse images and `R^q` of a quasi-compact quasi-separated morphism commute with that
  colimit. The second half, that `R^q g_*` commutes with filtered colimits for `g` qcqs, is
  independently useful and deserves a statement of its own;
- the change of rings `Λ ↝ Λ/nΛ` which the first step performs on the coefficients, and its
  compatibility with `AlgebraicGeometry.Etale.baseChangeHomologyMap`.

The compatibility of the base-change map with the composition of two Cartesian squares,
which the reduction to relative dimension one uses, is likewise missing; see the
implementation notes of
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs`.

## Main statements

- `AlgebraicGeometry.Etale.isIso_baseChangeHomologyMap_of_smooth`: the smooth base change
  theorem.

## References

- Stacks Project, Étale Cohomology, Theorem 59.89.2,
  <https://stacks.math.columbia.edu/tag/0EYU>
- [SGA 4, Exp. XVI]
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X S T Y : Scheme.{u}}

/-- Blueprint `sk-thm-smooth-base-change`: Smooth base change.

**The smooth base change theorem** in étale cohomology: for a Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `p` smooth and `g` quasi-compact quasi-separated, and for every sheaf `F` of
`Λ`-modules on `T_ét` all of whose geometric stalks are torsion of orders invertible on `S`,
the base-change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is an isomorphism in every degree. -/
@[stacks 0EYU]
theorem Etale.isIso_baseChangeHomologyMap_of_smooth (p : X ⟶ S) [Smooth p] (g : T ⟶ S)
    (e : Y ⟶ T) (h : Y ⟶ X) [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p)
    (q : ℤ) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    [Scheme.IsTorsionSheafOfInvertibleOrder S F] :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  sorry

end AlgebraicGeometry
