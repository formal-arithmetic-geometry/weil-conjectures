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

The same diagram gives two statements about the cokernel of the base-change map, which are
what verifies the closed–open splitting hypothesis of the minimal-counterexample lemma in
`WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField`: the cokernel for a
subsheaf `F ⊆ G` is contained in the cokernel for `G`, and if `G` is injective the cokernel
for `F` is contained in `R^q h_* e⁻¹ G`.

Consequently a failure of `BC(p, Λ, q)` is witnessed by a nonzero element of the cokernel in
a geometric stalk.

## Main statements

- `AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`: the degree-`q` base-change map is a
  monomorphism as soon as `BC(p, Λ, q - 1)` holds.
- `AlgebraicGeometry.Etale.mono_cokernelMap`: the cokernel of the base-change map for a
  subsheaf `F ⊆ G` is contained in the cokernel for `G`.
- `AlgebraicGeometry.Etale.mono_cokernelDesc`: for `G` injective, the cokernel of the
  base-change map for `F ⊆ G` is contained in `R^q h_* e⁻¹ G`.

## References

- Stacks Project, Lemma 59.88.2, <https://stacks.math.columbia.edu/tag/0F03>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} {p : X ⟶ S}
  {T Y : Scheme.{u}} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- Blueprint `sk-prop-injectivity` (1): Injectivity of the critical map.

Let `q ≥ 1` and assume `BC(p, Λ, q - 1)`. Then for every Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `g` quasi-compact quasi-separated and every sheaf `F` of `Λ`-modules on `T_ét`, the
degree-`q` base-change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is injective. -/
@[stacks 0F03]
theorem Etale.mono_baseChangeHomologyMap (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.BaseChangeProperty Λ p (q - 1)) [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Mono (Etale.baseChangeHomologyMap Λ sq q F) :=
  sorry

/-- Blueprint `sk-prop-injectivity` (2): the cokernel of the critical map grows with the
coefficient sheaf.

In the situation of `AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`, if `F` is a
subsheaf of `G`, then the map induced on the cokernels of the two base-change maps by the
naturality `AlgebraicGeometry.Etale.baseChangeHomologyMap_naturality` is injective. -/
@[stacks 0F03]
theorem Etale.mono_cokernelMap (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.BaseChangeProperty Λ p (q - 1)) [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (α : F ⟶ G) [Mono α] :
    Mono (cokernel.map (Etale.baseChangeHomologyMap Λ sq q F)
      (Etale.baseChangeHomologyMap Λ sq q G) ((Etale.baseChangeSourceFunctor Λ p g q).map α)
      ((Etale.baseChangeTargetFunctor Λ e h q).map α)
      (Etale.baseChangeHomologyMap_naturality Λ sq q α)) :=
  sorry

/-- Blueprint `sk-prop-injectivity` (3): the cokernel of the critical map sits inside the
higher direct image of an injective sheaf.

In the situation of `AlgebraicGeometry.Etale.mono_baseChangeHomologyMap`, if `F` is a
subsheaf of an injective sheaf `G`, then the map `R^q h_* e⁻¹ F ⟶ R^q h_* e⁻¹ G` kills the
image of the base-change map for `F` — the source of the base-change map for `G` vanishes,
`G` being injective and `q` positive — and the induced map from the cokernel is injective.
The hypothesis `hα` records the vanishing that makes the map out of the cokernel exist. -/
@[stacks 0F03]
theorem Etale.mono_cokernelDesc (q : ℤ) (hq : 1 ≤ q)
    (hprev : Etale.BaseChangeProperty Λ p (q - 1)) [QuasiCompact g] [QuasiSeparated g]
    (sq : IsPullback e h g p) {F G : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (α : F ⟶ G) [Mono α] [Injective G]
    (hα : Etale.baseChangeHomologyMap Λ sq q F ≫
      (Etale.baseChangeTargetFunctor Λ e h q).map α = 0) :
    Mono (cokernel.desc (Etale.baseChangeHomologyMap Λ sq q F)
      ((Etale.baseChangeTargetFunctor Λ e h q).map α) hα) :=
  sorry

end AlgebraicGeometry
