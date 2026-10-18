/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.Valuation.ValuationSubring

import Mathlib.Algebra.CharP.Defs

/-!
# Divisibility of the value group of a separably closed valued field

Source: Temkin, *Stable Modification*, finite-height argument, Step 4 (PDF lines
1565–1571), and Proposition 4.3.1 (blueprint: lem-trf-separably-closed-value-group-divisible).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace ValuationSubring

/-- The nonzero value classes of a valuation subring of a separably closed field
are divisible.  The unit group of `V.ValueGroup` is the quotient of `Kˣ` by
the units of `V` appearing as the value group in the statement.

Source: Temkin, *Stable Modification*, finite-height argument, Step 4 (PDF lines
1565–1571), and Proposition 4.3.1 (blueprint: lem-trf-separably-closed-value-group-divisible).
Proof plan (the elementary details are agent-written, as in the DAG):
1. The units of `V` form a subgroup of `Kˣ`. Quotienting gives an ordered abelian group;
   in additive valuation notation, `v(a) ≤ v(b)` means `b / a ∈ V`. This is independent
   of representatives since multiplication by a unit preserves membership in `V`.
   Reflexivity and transitivity follow from `1 ∈ V` and closure under products;
   antisymmetry follows because both ratios in `V` make their class a unit.
   Totality follows from the inverse alternative and cancelling a common factor gives
   translation invariance. Also `v(ab) = v(a) + v(b)`, `v(-a) = v(a)` because `-1` is
   a unit, and `v(a) ≥ 0` exactly when `a ∈ V`. Every class has a representative `a ≠ 0`.
   Mathlib uses the opposite multiplicative order.
2. If `v(x) ≤ v(y)` and `x + y ≠ 0`, then `1 + y / x ∈ V` implies
   `v(x + y) ≥ v(x)`. If `v(r) < v(s)`, cancellation prevents `r + s = 0`.
   Strict inequality `v(r + s) > v(r)` would contradict the same inequality applied
   to `(r + s) + (-s) = r`; hence `v(r + s) = v(r)`.
3. In characteristic zero, `IsSepClosed.exists_pow_nat_eq`
   (`lem-trf-separably-closed-prime-to-char-root`) gives an actual `n`-th root of `a`.
   In characteristic `p > 0`, write `n = p ^ r * m` with `p` not dividing `m`, using
   `CharP` / `ringChar` (`def-pc-field-characteristic`). The same root theorem handles `m`.
4. The characteristic `p` is prime, hence at least two. For `v(a) = 0`, take the identity
   class. For `v(a) < 0`, the Artin–Schreier root theorem
   (`lem-trf-separably-closed-artin-schreier-root`, Mathlib's
   `IsSepClosed.exists_root_C_mul_X_pow_add_C_mul_X_add_C'`) supplies `z ^ p - z = a`.
   The element `z` is nonzero and not in `V`, for otherwise `a ∈ V`. Thus
   `p * v(z) < v(z) = v(-z)`; Step 2 gives `v(a) = p * v(z)`.
   For `v(a) > 0`, apply this to `a⁻¹` and invert the resulting class.
5. Iterate `p`-division `r` times and then extract the prime-to-characteristic `m`-th
   root. Multiplying the equalities gives `n * v(b) = v(a)`.
6. Every class has such a representative, so returning to multiplicative notation
   yields `δ ^ n = γ` for every class and every positive `n`.
-/
theorem valueGroup_divisible (K : Type u) [Field K] [IsSepClosed K]
    (V : ValuationSubring K) :
    ∀ (γ : V.ValueGroupˣ) (n : ℕ), 1 ≤ n → ∃ δ : V.ValueGroupˣ, δ ^ n = γ := by
  sorry

end ValuationSubring

