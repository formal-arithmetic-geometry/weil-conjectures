/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Weil.Definitions

/-!
# The Hasse–Weil bound

Let `X` be a smooth proper geometrically integral scheme of dimension `d ≥ 1` over a finite
field `k` with `q` elements, and let `P 0, …, P_{2d} ∈ ℤ[T]` be integral Frobenius factors of
its zeta function satisfying the Riemann hypothesis. The number of rational points of `X` is
the alternating sum of the traces of Frobenius, the two endpoint factors `P 0 = 1 - T` and
`P (2 * d) = 1 - qᵈ T` contribute `1` and `qᵈ`, and each of the `deg (P i)` reciprocal roots
in an intermediate degree `i` has absolute value `q^{i/2}`. The triangle inequality then
bounds the deviation of the point count from `qᵈ + 1`.

For a smooth projective curve of genus `g` this is the classical Hasse–Weil bound
`|N₁ - (q + 1)| ≤ 2 g √q`, since there `d = 1` and `deg (P 1) = 2 g`.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.abs_pointCount_sub_le`: the Hasse–Weil bound.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}

/-- Blueprint `sk-cor-hasse`: Hasse–Weil bound.

If the zeta function of `X` has integral Frobenius factors `P i` satisfying the Riemann
hypothesis, then the number of `k`-rational points of `X` differs from `qᵈ + 1` by at most
`∑_{0 < i < 2d} deg (P i) · q^{i/2}`. -/
theorem Hom.abs_pointCount_sub_le {d : ℕ} (hd : 1 ≤ d) (f : X.Hom (Spec (.of k)))
    {P : Fin (2 * d + 1) → Polynomial ℤ}
    (hfact : IsWeilFactorization (Nat.card k) d f.zetaSeries P)
    (hrh : WeilRiemannHypothesis (Nat.card k) d P) :
    |(f.pointCount 1 : ℝ) - ((Nat.card k : ℝ) ^ d + 1)| ≤
      ∑ i ∈ Finset.univ.filter (fun i : Fin (2 * d + 1) ↦ 0 < i.1 ∧ i.1 < 2 * d),
        ((P i).natDegree : ℝ) * (Nat.card k : ℝ) ^ ((i.1 : ℝ) / 2) :=
  sorry

end AlgebraicGeometry.Scheme

end
