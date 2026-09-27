/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper

/-!
# The recorded base-change property and the allowed coefficients

This file records the two definitions on which the smooth base change theorem is phrased.

Fix a morphism `p : X ⟶ S` — the morphism along which one pulls back, smooth in the
theorem — a coefficient ring `Λ` and a degree `q`. For a Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

with `g` quasi-compact quasi-separated, and a sheaf `F` of `Λ`-modules on `T_ét`, the
base-change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` is the degree-`q` homology of the derived
base-change morphism `AlgebraicGeometry.Etale.baseChange` of
`WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs`, evaluated at `F`
placed in degree `0`; it is `AlgebraicGeometry.Etale.baseChangeHomologyMap`. The property
`BC(p, Λ, q)` of the blueprint is that this map is an isomorphism for every such square and
every `F`.

The coefficients allowed in the theorem are the sheaves all of whose geometric stalks are
torsion of orders invertible on the base, `AlgebraicGeometry.Scheme.IsAllowedTorsionSheaf`.
A natural number `n` is *invertible on `S`* when `IsUnit (n : Γ(S, ⊤))`; no definition is
introduced for that, it is written out where it is used.

## Main definitions

- `AlgebraicGeometry.Scheme.IsAllowedTorsionSheaf`: the coefficient condition.
- `AlgebraicGeometry.Etale.baseChangeHomologyMap`: the degree-`q` base-change map.
- `AlgebraicGeometry.Etale.BaseChangeProperty`: the recorded property `BC(p, Λ, q)`.

## References

- Stacks Project, Section 59.88, <https://stacks.math.columbia.edu/tag/0F02>
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `sk-def-smooth`: Smooth and allowed coefficients.

A morphism is *smooth* in the sense of the blueprint exactly when it is
`AlgebraicGeometry.Smooth`: flat, locally of finite presentation, with smooth geometric
fibres; that notion is Mathlib's and is not repeated here.

A sheaf `F` of `Λ`-modules on the small étale site of `T` has *allowed torsion relative to
the base `S`* if every element of every geometric stalk of `F` is killed by a positive
integer which is invertible on `S`. These are the coefficient sheaves for which smooth base
change holds; for `Λ = ℤ/nℤ` with `n` invertible on `S` every sheaf is allowed, and a
general allowed sheaf is the filtered union of its `n`-torsion subsheaves over the `n`
invertible on `S`. -/
def Scheme.IsAllowedTorsionSheaf (S : Scheme.{u}) {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Prop :=
  ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T)
    (x : ↥((pointSmallEtale s).sheafFiber.obj F)),
    ∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧ n • x = 0

variable {X S T Y : Scheme.{u}} {p : X ⟶ S} {g : T ⟶ S} {e : Y ⟶ T} {h : Y ⟶ X}

/-- The degree-`q` base-change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` attached to a Cartesian
square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

and a sheaf `F` of `Λ`-modules on `T_ét`: the degree-`q` homology of the derived
base-change morphism `AlgebraicGeometry.Etale.baseChange` evaluated at `F` placed in degree
`0`. The pullback `p⁻¹` is exact and `R g_*` is the derived pushforward, so the source and
target are the sheaves named above. -/
noncomputable def Etale.baseChangeHomologyMap (sq : IsPullback e h g p) (q : ℤ)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (DerivedCategory.Plus.homologyFunctor _ q).map
    ((Etale.baseChange (ModuleCat.{u + 1} Λ) sq.toCommSq).app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))

variable (p) in
/-- Blueprint `sk-def-bc`: The recorded base-change property.

`BC(p, Λ, q)` holds when, for every quasi-compact quasi-separated `g : T ⟶ S`, every sheaf
`F` of `Λ`-modules on `T_ét` and every Cartesian square

```
Y --e--> T
|        |
h        g
v        v
X --p--> S
```

the base-change map `p⁻¹ R^q g_* F ⟶ R^q h_* e⁻¹ F` of
`AlgebraicGeometry.Etale.baseChangeHomologyMap` is an isomorphism. The coefficient ring `Λ`
plays the role of `ℤ/nℤ` in the blueprint; the hypothesis that `n` be invertible on `S` is
not part of the property and is carried separately by the statements that need it. -/
def Etale.BaseChangeProperty (q : ℤ) : Prop :=
  ∀ {T Y : Scheme.{u}} (g : T ⟶ S) (e : Y ⟶ T) (h : Y ⟶ X)
    [QuasiCompact g] [QuasiSeparated g] (sq : IsPullback e h g p)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
    IsIso (Etale.baseChangeHomologyMap Λ sq q F)

end AlgebraicGeometry
