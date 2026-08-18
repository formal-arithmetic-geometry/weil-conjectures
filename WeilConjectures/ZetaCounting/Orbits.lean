/-
Copyright (c) 2026 mathhzstx. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathhzstx
-/
module

public import WeilConjectures.Mathlib.Dynamics.PeriodicPts.OrbitCount
public import WeilConjectures.ZetaCounting.EulerProducts

@[expose] public section

/-!
# The zeta series of a self-map counted by its periodic orbits

For a self-map `f : α → α` with finitely many points of each positive period, the zeta
series of the counting function `n ↦ #{x | fⁿ x = x}` is the Euler product over the
orbits of `f`, one factor `(1 - X ^ m)⁻¹` for each orbit of minimal period `m`. This is
the combinatorial form of the Euler product of a variety over a finite field, with `f`
the geometric Frobenius and the orbits the closed points.

## Main results

- `Function.countingZetaSeries_ncard_ptsOfPeriod`
- `Function.coeff_countingZetaSeries_ncard_ptsOfPeriod_mem_range`
-/

open PowerSeries

namespace Function

variable {α : Type*} (f : α → α)

open scoped PowerSeries.WithPiTopology in
/-- **The orbit Euler product.** The zeta series of the periodic point counts of a
self-map with finite sets of periodic points is the product of the factors
`(1 - X ^ m)⁻¹`, one for each orbit of minimal period `m`.
(blueprint: `thm:weil-orbit-euler-product`) -/
theorem countingZetaSeries_ncard_ptsOfPeriod
    (hfin : ∀ n, n ≠ 0 → (ptsOfPeriod f n).Finite) :
    countingZetaSeries (fun n ↦ (ptsOfPeriod f n).ncard) =
      ∏' m : ℕ, ((1 - X ^ m)⁻¹ : ℚ⟦X⟧) ^ orbitCount f m :=
  countingZetaSeries_eq_tprod_pow (orbitCount_zero f) fun n hn ↦
    ncard_ptsOfPeriod_eq_sum_divisors_mul_orbitCount (Nat.pos_of_ne_zero hn) (hfin n hn)

/-- The zeta series of the periodic point counts of a self-map has integer coefficients.
(blueprint: `cor:weil-orbit-zeta-integral`) -/
theorem coeff_countingZetaSeries_ncard_ptsOfPeriod_mem_range
    (hfin : ∀ n, n ≠ 0 → (ptsOfPeriod f n).Finite) (n : ℕ) :
    coeff n (countingZetaSeries fun k ↦ (ptsOfPeriod f k).ncard) ∈
      (Int.castRingHom ℚ).range :=
  coeff_countingZetaSeries_mem_range_of_multiplicity (orbitCount_zero f)
    (fun k hk ↦ ncard_ptsOfPeriod_eq_sum_divisors_mul_orbitCount (Nat.pos_of_ne_zero hk)
      (hfin k hk)) n

end Function

end
