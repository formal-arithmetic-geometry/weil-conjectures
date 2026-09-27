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
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# `H¹` and `H²` of a curve via the Kummer sequence

For a curve `C` over an algebraically closed field `k` and `n` prime to the characteristic,
the long exact cohomology sequence of the Kummer sequence

```
  𝒪_C(C)ˣ ──n·──▶ 𝒪_C(C)ˣ ──▶ H¹(C, μₙ) ──▶ H¹(C, 𝔾ₘ) ──n·──▶ H¹(C, 𝔾ₘ) ──▶ H²(C, μₙ) ──▶
    H²(C, 𝔾ₘ)
```

computes the first two cohomology groups of `μₙ` in terms of `H¹(C, 𝔾ₘ) = Pic(C)`. When
`𝒪_C(C)ˣ` is `n`-divisible — for instance for a smooth proper connected curve, where it is
`kˣ` — the sequence degenerates to `H¹(C, μₙ) ≅ Pic(C)[n]`; and when `H²(C, 𝔾ₘ) = 0` it ends
with a surjection `Pic(C) ↠ H²(C, μₙ)` with kernel `n · Pic(C)`.

Curves appear through the classes `AlgebraicGeometry.IsCurveOver` and
`AlgebraicGeometry.IsConnectedCurveOver`; see the module docstring of
`WeilConjectures.AlgebraicGeometry.Curve.Defs`.

## Main statements

- `AlgebraicGeometry.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one`: `H¹(C, μₙ) ≅ Pic(C)[n]`
  for a smooth proper connected curve.
- `AlgebraicGeometry.exists_surjective_sheafH_rootsOfUnitySheaf_two`:
  `H²(C, μₙ) ≅ Pic(C)/n·Pic(C)`.

## TODO

Both statements should name the maps of the Kummer long exact sequence: the isomorphism of the
first is induced by the boundary `H¹(C, μₙ) ⟶ H¹(C, 𝔾ₘ)`, and the surjection `γ` of the second
is the coboundary `Pic(C) = H¹(C, 𝔾ₘ) ⟶ H²(C, μₙ)`. The long exact sequence of a short exact
sequence of sheaves is `CategoryTheory.Abelian.Ext.covariantSequence_exact`; connecting its
maps to `CategoryTheory.Sheaf.H` is not yet available, so the first isomorphism is only
asserted to exist and the second surjection is existentially quantified.

## Blueprint references

The labels quoted below are labels of the *sketch* blueprint, which lives in the separate
repository `formal-arithmetic-geometry/weil-conjectures-blueprint`, not of `blueprint/src` in
this repository.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} [C.Over (Spec (.of k))]

/-- **`H¹` via the Kummer sequence.** For a smooth proper connected curve `C` over an
algebraically closed field `k` and every `n ≥ 1` prime to `char k`,

`H¹(C, μₙ) ≅ Pic(C)[n]`.

In general the Kummer long exact sequence only gives a short exact sequence

`0 ⟶ 𝒪_C(C)ˣ/(𝒪_C(C)ˣ)ⁿ ⟶ H¹(C, μₙ) ⟶ Pic(C)[n] ⟶ 0`;

it degenerates as stated because `𝒪_C(C)ˣ = k ˣ` for a proper connected reduced curve and
`kˣ` is `n`-divisible, `k` being algebraically closed. The proof is `sorry`.
(blueprint: `lem-sc-kummer-les`) -/
theorem nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one [IsConnectedCurveOver k C]
    [Smooth (C ↘ Spec (.of k))] [IsProper (C ↘ Spec (.of k))] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.rootsOfUnitySheaf n) 1 ≃+
      (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (n : ℤ)).ker) :=
  sorry

/-- **`H²` via the Kummer sequence.** For a curve `C` over an algebraically closed field `k`
with vanishing Brauer group and every `n ≥ 1` prime to `char k`,

`H²(C, μₙ) ≅ Pic(C)/n·Pic(C)`,

recorded as the existence of a surjection `γ : Pic(C) ↠ H²(C, μₙ)` whose kernel is
`n · Pic(C)`. The hypothesis `hbr` is what makes the Kummer long exact sequence stop here; it
holds for a smooth curve by `AlgebraicGeometry.subsingleton_cohomologicalBrauerGroup`, and in
fact for every curve, but that is a separate blueprint statement
(`lem-sc-brauer-zero-all-curves`) which is not formalised here. The proof is `sorry`.
(blueprint: `lem-sc-second-kummer-divisors`) -/
theorem exists_surjective_sheafH_rootsOfUnitySheaf_two [IsCurveOver k C]
    (hbr : Subsingleton C.CohomologicalBrauerGroup) (n : ℕ) (hn : (n : k) ≠ 0) :
    ∃ γ : C.CohomologicalPicardGroup →+ Sheaf.H (C.rootsOfUnitySheaf n) 2,
      Function.Surjective γ ∧
        Function.Exact (zsmulAddGroupHom (α := C.CohomologicalPicardGroup) (n : ℤ)) γ :=
  sorry

end AlgebraicGeometry
