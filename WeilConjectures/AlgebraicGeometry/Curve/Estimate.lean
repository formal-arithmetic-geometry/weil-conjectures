/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve.Defs
public import WeilConjectures.AlgebraicGeometry.Sites.ConstantZMod
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance

/-!
# The curve estimate

For a smooth proper connected curve `C` of genus `g` over an algebraically closed field `k`
and `n` prime to the characteristic, the cohomology of the constant sheaf `ℤ/n` on `C_ét` is

`H⁰ = ℤ/n`, `H¹ = (ℤ/n)^{2g}`, `H² = ℤ/n`, `H^q = 0` for `q ≥ 3`.

The four parts are four separate statements, and two of them are not about curves: `H⁰` is
`AlgebraicGeometry.Scheme.bijective_toSheafHConstantZMod`, the statement that the canonical
map `ℤ/n → H⁰(X_ét, ℤ/n)` is bijective for any connected scheme, and the vanishing for
`q ≥ 3` is `AlgebraicGeometry.subsingleton_sheafH_of_three_le` applied to `C.constantZMod n`,
which is killed by `n`. Only `H¹` and `H²` are recorded here.

The genus belongs to the abelian-varieties block, so it is not defined here: the rank of `H¹`
is recorded as an existentially quantified `g`, which is what the estimate is used for, and
the identification of that `g` with the genus is left to the block that owns it. The `H¹` and
`H²` isomorphisms are stated as `Nonempty (· ≃+ ·)` because they depend on the choice of a
primitive `n`-th root of unity, that is, of an isomorphism `μₙ ≅ ℤ/n` of étale sheaves.

The same computation is invariant under an extension of algebraically closed base fields, in
the strong sense that the canonical pullback map on cohomology is an isomorphism.

Curves appear through the class `AlgebraicGeometry.IsConnectedCurveOver`; see the module
docstring of `WeilConjectures.AlgebraicGeometry.Curve.Defs`.

## Main statements

- `AlgebraicGeometry.exists_nonempty_addEquiv_sheafH_constantZMod_one`:
  `H¹(C, ℤ/n) ≅ (ℤ/n)^{2g}`.
- `AlgebraicGeometry.nonempty_addEquiv_sheafH_constantZMod_two`: `H²(C, ℤ/n) ≅ ℤ/n`.
- `AlgebraicGeometry.bijective_cohomologyMap_constantZMod`: invariance of the estimate under
  extension of algebraically closed base fields.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} [C.Over (Spec (.of k))]

/-- **The curve estimate in degree one.** Let `C` be a smooth proper connected curve of genus
`g` over an algebraically closed field `k` and let `n ≥ 1` be prime to `char k`. Then

`H¹(C_ét, ℤ/n) ≅ (ℤ/n)^{2g}`.

The genus is quantified existentially, since it is defined in another blueprint block. The
proof is `sorry`; it goes through `H¹(C, μₙ) ≅ Pic(C)[n]`
(`AlgebraicGeometry.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one`) and the fact that the
`n`-torsion of the Picard group of a curve of genus `g` is `(ℤ/n)^{2g}`.
(blueprint: `thm-sc-proper-cohomology`) -/
theorem exists_nonempty_addEquiv_sheafH_constantZMod_one [IsConnectedCurveOver k C]
    [Smooth (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))] (n : ℕ) (hn : (n : k) ≠ 0) :
    ∃ g : ℕ, Nonempty (Sheaf.H (C.constantZMod n) 1 ≃+ (Fin (2 * g) → ZMod n)) :=
  sorry

/-- **The curve estimate in degree two.** Let `C` be a smooth proper connected curve over an
algebraically closed field `k` and let `n ≥ 1` be prime to `char k`. Then

`H²(C_ét, ℤ/n) ≅ ℤ/n`.

The proof is `sorry`; it goes through `H²(C, μₙ) ≅ Pic(C)/n·Pic(C)`
(`AlgebraicGeometry.exists_surjective_sheafH_rootsOfUnitySheaf_two`) and the degree map, which
identifies `Pic(C)/n·Pic(C)` with `ℤ/n` for a proper connected curve.
(blueprint: `thm-sc-proper-cohomology`) -/
theorem nonempty_addEquiv_sheafH_constantZMod_two [IsConnectedCurveOver k C]
    [Smooth (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.constantZMod n) 2 ≃+ ZMod n) :=
  sorry

/-- **Invariance under extension of algebraically closed fields.** Let `k ⊆ k'` be an
extension of algebraically closed fields, let `C` be a smooth connected curve over `k` and let
`n ≥ 1` be prime to `char k`. Form the base change

```
   C ×_{Spec k} Spec k' ──pullback.fst──▶ C
            │                             │ C ↘ Spec k
            │ pullback.snd                ▼
            ▼                          Spec k
        Spec k' ──Spec.map (algebraMap k k')──▶ Spec k
```

Then for every `q ≥ 0` the pullback map along the first projection

`ρ^q : H^q(C_ét, ℤ/n) ⟶ H^q((C_{k'})_ét, ℤ/n)`

is an isomorphism. In particular the curve estimate is compatible with algebraically closed
extension of the base field: the isomorphisms recorded over `k` and over `k'` are matched by
`ρ^q`, not merely abstractly isomorphic.

The map is `AlgebraicGeometry.Etale.cohomologyMap`; its target is the cohomology of the
pullback of the constant sheaf, which is the constant sheaf on `C_{k'}` by
`AlgebraicGeometry.Scheme.upperStarConstantSheafIso`. The proof is `sorry`.
(blueprint: `thm-sc-constant-invariance`) -/
theorem bijective_cohomologyMap_constantZMod {k' : Type u} [Field k'] [IsAlgClosed k']
    [Algebra k k'] [IsConnectedCurveOver k C] [Smooth (C ↘ Spec (.of k))] (n : ℕ)
    (hn : (n : k) ≠ 0) (q : ℕ) :
    Function.Bijective (Etale.cohomologyMap
      (pullback.fst (C ↘ Spec (.of k)) (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
      (C.constantZMod n) q) :=
  sorry

end AlgebraicGeometry
