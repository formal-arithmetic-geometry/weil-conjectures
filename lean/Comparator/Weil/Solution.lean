/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.Statement

@[expose] public section

/-!
# Solution: the Weil conjectures

This is the solution to the `leanprover/comparator` challenge in `Weil/Challenge.lean`. The
challenge statements are about the zeta function defined in the shared mathlib-only
definitions file `Weil/Definitions.lean`; they are proved in `WeilConjectures/Statement.lean`
using this repository.
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
  Scheme.zetaSeries_rational f

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
  Scheme.weil_conjectures f d

end WeilConjectures
