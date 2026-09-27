/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.DegreeZero
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Induction
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Injectivity
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.NormalForm

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
— that is, `AlgebraicGeometry.Scheme.IsAllowedTorsionSheaf` — the base-change map

`p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F`

of `AlgebraicGeometry.Etale.baseChangeHomologyMap` is an isomorphism in every degree `q`.

The proof is the second, shorter proof of the Stacks Project: degree zero is
`AlgebraicGeometry.Etale.baseChangeProperty_zero_of_smooth`; the general coefficient sheaf is
the filtered colimit of its `n`-torsion subsheaves; the assertion is étale local on `X` and
`S`, so by `AlgebraicGeometry.Smooth.exists_etaleCover_factorization` and the factorisation of
`X ⟶ 𝔸^d_S` into relative curves it suffices to treat relative dimension one; and there
`AlgebraicGeometry.Etale.baseChangeProperty_of_sub_one` carries out the induction on `q`.

Compare `AlgebraicGeometry.Etale.isIso_baseChange_of_isProper`, the proper base change
theorem, in which the roles of the two legs of the square are exchanged.

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

open CategoryTheory Limits

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
    (hF : Scheme.IsAllowedTorsionSheaf Λ S F) :
    IsIso (Etale.baseChangeHomologyMap Λ sq q F) :=
  sorry

end AlgebraicGeometry
