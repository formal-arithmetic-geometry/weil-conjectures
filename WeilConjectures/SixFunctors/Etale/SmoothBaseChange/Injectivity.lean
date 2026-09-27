/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.Defs

/-!
# Injectivity of the critical base-change map

Once the base-change property `BC(p, Λ, q - 1)` of
`AlgebraicGeometry.Etale.BaseChangeProperty` is known, the degree-`q` base-change map is
automatically injective: embedding the coefficient sheaf in an injective sheaf and comparing
the two long exact sequences, the degree-`(q - 1)` hypothesis makes two of the vertical arrows
isomorphisms and exhibits the source of the degree-`q` map as the image of the connecting map.

Consequently a failure of `BC(p, Λ, q)` is witnessed by a nonzero element of the cokernel in a
geometric stalk, which is the form in which the statement is used in
`AlgebraicGeometry.Etale.exists_notIsIso_baseChangeHomologyMap_over_field`.

## Main statements

- `AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`: the degree-`q` base-change map is a
  monomorphism as soon as `BC(p, Λ, q - 1)` holds.

## References

- Stacks Project, Lemma 59.88.2, <https://stacks.math.columbia.edu/tag/0F03>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} {p : X ⟶ S}

/-- Blueprint `sk-prop-injectivity`: Injectivity of the critical map.

Let `q ≥ 1` and assume `BC(p, Λ, q - 1)`. Then for every Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `g` quasi-compact quasi-separated and every sheaf `F` of `Λ`-modules on `T_ét`, the
degree-`q` base-change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is injective.

The two further assertions of the blueprint subsection are consequences of the same diagram
and are not separate statements: for `F ⊆ G` with `G` annihilated by `n`, the cokernel for `F`
is contained in the cokernel for `G`, and if `G` is moreover injective that cokernel is
contained in `R^q h_* e⁻¹ G`. -/
@[stacks 0F03]
theorem Etale.mono_baseChangeHomologyMap (q : ℤ) (hq : 1 ≤ q)
    (hp : Etale.BaseChangeProperty Λ p (q - 1)) {T Y : Scheme.{u}} (g : T ⟶ S) (e : Y ⟶ T)
    (h : Y ⟶ X) [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Mono (Etale.baseChangeHomologyMap Λ sq q F) :=
  sorry

end AlgebraicGeometry
