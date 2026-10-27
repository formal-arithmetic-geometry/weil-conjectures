/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q50
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import WeilConjectures.RingTheory.AssociatedGradedRing

/-!
# Binomial colength bounds for parameter ideals

Source: Stacks Project, Algebra, Tag 00KQ, proof of `proposition-dimension`,
the paragraph beginning "Assume d'(R) = d", with the empty-generator case separated
(blueprint: lem-trf-parameter-ideal-colength-bound).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace IsLocalRing

/-- Degree-`i` parameter monomials give the binomial-sized surjection onto `J^i/J^(i+1)`,
and the lengths of the power quotients satisfy the resulting binomial bounds.
For zero generators the maximal ideal is nilpotent and the lengths stabilize at `L`.

The finite product in the source of `q` is the finite direct sum in the statement.
The equivalence `e` enumerates all formal exponent tuples, including repetitions in their
values in `R`. The lifts `b` specify their values in `J^i`; the final formula specifies
multiplication by each monomial on every representative `r` of `R/J`.

Source: Stacks Project, Algebra, Tag 00KQ, proof of `proposition-dimension`,
the paragraph beginning "Assume d'(R) = d"
(blueprint: lem-trf-parameter-ideal-colength-bound).

Proof plan:
1. If `d = 0`, the empty span is zero, so `m^a = 0` and `R/J = R` has length `L`.
   For `n >= a`, factor `m^n = m^a * m^(n-a) = 0`, giving the stabilization assertion.
2. If `d >= 1`, the degree-`i` exponent tuples are counted by stars and bars: place
   `d-1` bars among `i+d-1` positions, with the intervening star counts as exponents.
   This gives the equivalence `e`; for `i = 0` its unique monomial is one.
3. Induct on `i` to show that these monomials generate `J^i`: distribute products
   in `J^(i+1) = J^i * J`, and remove one positive exponent for the converse.
   Choose their lifts `b` in `J^i`. Send a family of residue classes to the sum of
   its representatives times these monomials modulo `J^(i+1)`. Changing representatives
   changes that sum by an element of `J * J^i`. Thus the map is well-defined and linear,
   has the displayed component formula, and is surjective by the generating assertion.
4. By `lem-weil-pbc-length-additive-short-exact`, induction on the number of coordinates
   gives length `c_i * L` for the source, where `c_i = choose(i+d-1,d-1)`.
   Apply the same additivity to the kernel sequence of `q` to bound the finite length
   of `J^i/J^(i+1)` by `L * c_i`.
5. Apply that additivity to `0 -> J^i/J^(i+1) -> R/J^(i+1) -> R/J^i -> 0`.
   Starting from `R/J^0 = 0`, telescope to bound the finite length of `R/J^n`
   by `L` times the sum of the `c_i` for `i < n`.
6. The sum is `choose(n+d-1,d)`: start with `n = 1` and use Pascal's identity,
   obtained by separating subsets according to whether they contain the last element.
7. Each `x_j` lies in `m`, hence `J^n <= m^n`. The canonical surjection
   `R/J^n -> R/m^n` and its kernel sequence, using the same length additivity,
   give finiteness and the remaining inequality.
-/
theorem parameterIdeal_colength_bound (R : Type u) [CommRing R] [IsNoetherianRing R]
    [IsLocalRing R] (d : ℕ) (x : Fin d → R)
    (hx : ∀ j : Fin d, x j ∈ maximalIdeal R)
    (J : Ideal R) (hJ : J = Ideal.span (Set.range x))
    (a : ℕ) (ha : 1 ≤ a) (haJ : (maximalIdeal R) ^ a ≤ J)
    (L : ℕ∞) (hL : Module.length R (R ⧸ J) = L) (hLfin : L < ⊤) :
    (1 ≤ d →
      (∀ i : ℕ,
        ∃ (e : Fin (Nat.choose (i + d - 1) (d - 1)) ≃
              {f : Fin d → ℕ // ∑ j : Fin d, f j = i})
          (b : Fin (Nat.choose (i + d - 1) (d - 1)) → ↥(J ^ i))
          (q : (Fin (Nat.choose (i + d - 1) (d - 1)) → R ⧸ J) →ₗ[R]
            Ideal.associatedGradedPiece J i),
          Function.Surjective q ∧
          (∀ k, (b k : R) = ∏ j : Fin d, x j ^ (e k).val j) ∧
          ∀ (k : Fin (Nat.choose (i + d - 1) (d - 1))) (r : R),
            q (Pi.single k (Ideal.Quotient.mk J r)) =
              r • (Submodule.Quotient.mk (b k) : Ideal.associatedGradedPiece J i)) ∧
      ∀ n : ℕ, 1 ≤ n →
        Module.length R (R ⧸ (maximalIdeal R) ^ n) < ⊤ ∧
        Module.length R (R ⧸ J ^ n) < ⊤ ∧
        Module.length R (R ⧸ (maximalIdeal R) ^ n) ≤ Module.length R (R ⧸ J ^ n) ∧
        Module.length R (R ⧸ J ^ n) ≤ L * (Nat.choose (n + d - 1) d : ℕ∞)) ∧
    (d = 0 →
      J = ⊥ ∧ (maximalIdeal R) ^ a = ⊥ ∧
      Module.length R R < ⊤ ∧ Module.length R R = L ∧
      ∀ n : ℕ, a ≤ n → Module.length R (R ⧸ (maximalIdeal R) ^ n) = L) := by
  sorry

end IsLocalRing
