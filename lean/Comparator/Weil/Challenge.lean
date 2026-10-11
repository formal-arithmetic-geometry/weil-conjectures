/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Weil.Definitions

@[expose] public section

/-!
# Challenge: the Weil conjectures

This is a `leanprover/comparator` challenge file. It is stated using only mathlib and the
shared definitions file `Weil/Definitions.lean` (which itself only imports mathlib).

Let `X` be a smooth, proper, geometrically integral scheme of dimension `d` over a finite
field `k` with `q` elements and let `Z(X, t) ∈ ℚ⟦t⟧` be its zeta function
(`AlgebraicGeometry.Scheme.Hom.zetaSeries`, defined in `Weil/Definitions.lean` as
`exp (∑ N_n t ^ n / n)` with `N_n = #X(𝔽_(q ^ n))`). The Weil conjectures [weil1949]
assert:

1. *Rationality* (Dwork, 1960): `Z(X, t)` is a rational function. More precisely
   `Z(X, t) = (P₁ ⋯ P_{2d-1}) / (P₀ ⋯ P_{2d})` for polynomials `Pᵢ ∈ ℤ[t]` with
   `Pᵢ(0) = 1`, `P₀ = 1 - t` and `P_{2d} = 1 - qᵈ t`. Rationality alone holds for
   arbitrary schemes of finite type over `k`, which is the first challenge theorem
   `zetaSeries_rational`.
2. *Functional equation* (Grothendieck, 1965): `Z(X, 1 / (qᵈ t)) = ± q^{dχ/2} tᵡ Z(X, t)`
   where `χ = ∑ (-1)ⁱ deg Pᵢ`. Equivalently — and this is how it is stated — the map
   `α ↦ qᵈ / α` sends the inverse roots of `Pᵢ` bijectively (with multiplicity) to the
   inverse roots of `P_{2d - i}`.
3. *Riemann hypothesis* (Deligne, 1974): the inverse roots of `Pᵢ` are algebraic numbers
   of absolute value `q^{i/2}` under every complex embedding. Since each `Pᵢ` has integer
   coefficients and constant coefficient `1`, its inverse roots are automatically
   algebraic integers, so only the norms of its complex roots have to be constrained.

The three conjectures are stated in terms of the complex roots of the `Pᵢ` (a root `z` of
`Pᵢ` is the inverse of an inverse root `α`), packaged into the predicates
`AlgebraicGeometry.IsWeilFactorization`, `AlgebraicGeometry.WeilFunctionalEquation` and
`AlgebraicGeometry.WeilRiemannHypothesis` of `Weil/Definitions.lean`. They form the second
challenge theorem `weil_conjectures`.

Weil's fourth conjecture — if `X` lifts to a smooth proper scheme over a number ring, then
`deg Pᵢ` is the `i`-th Betti number of the associated complex manifold — needs singular
cohomology of the analytification and is not part of the challenge.

## References

- [A. Weil, *Numbers of solutions of equations in finite fields*][weil1949]
- [P. Deligne, *La conjecture de Weil. I*][deligne1974]
-/

universe u

open AlgebraicGeometry CategoryTheory Polynomial

namespace WeilConjectures

variable {k : Type u} [Field k] [Finite k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **Dwork's theorem**: the zeta function of a scheme of finite type over a finite field
is a rational function with integer coefficients. This is the first Weil conjecture, which
holds without any smoothness or properness hypotheses. -/
theorem zetaSeries_rational [LocallyOfFiniteType f] [QuasiCompact f] :
    ∃ P Q : Polynomial ℤ, Q.coeff 0 = 1 ∧
      f.zetaSeries * (Q.map (Int.castRingHom ℚ) : PowerSeries ℚ) =
        (P.map (Int.castRingHom ℚ) : PowerSeries ℚ) :=
  sorry

/-- **The Weil conjectures** (Dwork, Grothendieck, Deligne): the zeta function of a
smooth, proper, geometrically integral scheme `X` of dimension `d` over a finite field
`k` with `q` elements factors as `Z(X, t) = (P₁ ⋯ P_{2d-1}) / (P₀ ⋯ P_{2d})` with
`Pᵢ ∈ ℤ[t]`, `Pᵢ(0) = 1`, `P₀ = 1 - t`, `P_{2d} = 1 - qᵈ t`, satisfying the functional
equation and the Riemann hypothesis: all inverse roots of `Pᵢ` have absolute value
`q^{i/2}`, and `α ↦ qᵈ / α` matches the inverse roots of `Pᵢ` with those of `P_{2d-i}`. -/
theorem weil_conjectures (d : ℕ) [SmoothOfRelativeDimension d f] [IsProper f]
    [GeometricallyIntegral f] :
    ∃ P : Fin (2 * d + 1) → Polynomial ℤ,
      IsWeilFactorization (Nat.card k) d f.zetaSeries P ∧
      WeilFunctionalEquation (Nat.card k) d P ∧
      WeilRiemannHypothesis (Nat.card k) d P :=
  sorry

end WeilConjectures
