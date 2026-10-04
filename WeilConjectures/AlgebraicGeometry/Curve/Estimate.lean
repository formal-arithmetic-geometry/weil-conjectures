/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer

/-!
# The curve estimate

For a smooth proper connected curve `C` of genus `g` over an algebraically closed field `k`
and `n` prime to the characteristic, the cohomology of the constant sheaf `ℤ/n` on `C_ét` is

`H⁰ = ℤ/n`, `H¹ = (ℤ/n)^{2g}`, `H² = ℤ/n`, `H^q = 0` for `q ≥ 3`.

A smooth proper connected curve is recorded by the class `AlgebraicGeometry.IsConnectedCurve`
together with `Smooth` and `IsProper`. Dimension exactly one is needed in degree two: `Spec k`
is a smooth proper connected scheme of dimension zero with `H² = 0`. Degree one holds for every
smooth proper curve, connected or not. Degree zero holds for every connected scheme and is
`AlgebraicGeometry.Scheme.nonempty_addEquiv_sheafH_zero_constantZMod`. The vanishing for
`q ≥ 3` is `AlgebraicGeometry.IsCurve.subsingleton_sheafH_of_three_le` applied to
`C.constantZMod n`.

## Main statements

- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_one`:
  `H¹(C, ℤ/n) ≅ (ℤ/n)^{2g}`.
- `AlgebraicGeometry.IsConnectedCurve.nonempty_addEquiv_sheafH_constantZMod_two`:
  `H²(C, ℤ/n) ≅ ℤ/n`.

## TODO

The genus is `AlgebraicGeometry.Scheme.Hom.genus`, the dimension of the global sections of the
sheaf of relative differentials `AlgebraicGeometry.Scheme.Hom.relativeDifferentials`. Proving
the `H¹` statement needs the comparison of this genus with the étale cohomology of `C`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}}

/-- **The curve estimate in degree one.** Let `C` be a smooth proper curve of genus `g` over an
algebraically closed field `k`, and let `n ≥ 1` be prime to `char k`. Then
`H¹(C_ét, ℤ/n) ≅ (ℤ/n)^{2g}`. The curve need not be connected: both sides are additive over
the connected components, and a zero-dimensional component contributes nothing to either.

The genus is `f.genus = dim_k H⁰(C, Ω¹_{C/k})`, the definition of the blueprint
(`sk-def-curve`). For a smooth proper connected curve it agrees, by Serre duality, with the
arithmetic genus `AlgebraicGeometry.Scheme.arithmeticGenus = dim_k H¹(C, 𝒪_C)` of the
Riemann–Roch block; the two definitions are not yet identified in Lean.
(blueprint: `sk-thm-curveestimate`) -/
theorem IsCurve.nonempty_addEquiv_sheafH_constantZMod_one (f : C ⟶ Spec (.of k)) [IsCurve f]
    [Smooth f] [IsProper f] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.constantZMod n) 1 ≃+ (Fin (2 * f.genus) → ZMod n)) :=
  -- Proof sketch: after choosing a primitive `n`-th root of unity, `ℤ/n ≅ μₙ`, and
  -- `H¹(C, μₙ) ≅ Pic(C)[n]` by
  -- `AlgebraicGeometry.Scheme.exists_exact_sheafH_rootsOfUnitySheaf_one`, since
  -- `Γ(C, 𝒪)ˣ = (kˣ)^{π₀(C)}` is `n`-divisible. Both `Pic(C)[n]` and the genus split over the
  -- connected components `Cᵢ` of `C`. On a component of dimension one the degree map gives
  -- `Pic(Cᵢ)[n] = Pic⁰(Cᵢ)[n]`, and `Pic⁰(Cᵢ)` is the group of `k`-points of the Jacobian, an
  -- abelian variety of dimension `gᵢ`, whose `n`-torsion is `(ℤ/n)^{2gᵢ}`. A component that is
  -- a point has `Pic = 0` and `gᵢ = 0`.
  sorry

/-- **The curve estimate in degree two.** Let `C` be a smooth proper connected curve over an
algebraically closed field `k`, and let `n ≥ 1` be prime to `char k`. Then
`H²(C_ét, ℤ/n) ≅ ℤ/n`.

The isomorphism depends on the choice of a primitive `n`-th root of unity, that is, of an
isomorphism `μₙ ≅ ℤ/n` of étale sheaves, so it is only asserted to exist. A connected curve has
dimension exactly one (`AlgebraicGeometry.IsConnectedCurve.krullDim_eq_one`); without this
`Spec k` would be a smooth proper connected curve with `H² = 0`.
(blueprint: `sk-thm-curveestimate`) -/
theorem IsConnectedCurve.nonempty_addEquiv_sheafH_constantZMod_two (f : C ⟶ Spec (.of k))
    [IsConnectedCurve f] [Smooth f] [IsProper f] (n : ℕ) (hn : (n : k) ≠ 0) :
    Nonempty (Sheaf.H (C.constantZMod n) 2 ≃+ ZMod n) :=
  -- Proof sketch: after choosing a primitive `n`-th root of unity, `ℤ/n ≅ μₙ`, and
  -- `H²(C, μₙ) ≅ Pic(C)/n` by
  -- `AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_rootsOfUnitySheaf_two`.
  -- The degree `Pic(C) → ℤ` is surjective with `n`-divisible kernel `Pic⁰(C)`, so
  -- `Pic(C)/n ≅ ℤ/n`.
  sorry

end AlgebraicGeometry
