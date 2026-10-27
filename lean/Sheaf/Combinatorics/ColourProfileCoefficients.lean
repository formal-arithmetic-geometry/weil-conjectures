module

public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Algebra.Field.Rat
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Two-colour profile coefficients

Source: Stacks Project, `dpa.tex`, Tag 07GP, proof of (5) for `x + y`;
explicit arithmetic refinement of its universal coefficient comparison
(blueprint: lem-sfb-pd-colour-profile-coefficients).

The finite set of profiles is Mathlib's `Finset.Nat.antidiagonalTuple (m + 1) n`,
filtered by the red-weight equation. No new notion of a profile is introduced.
-/

@[expose] public section

set_option autoImplicit false

open scoped BigOperators

namespace Nat

/-- Every two-colour block-profile coefficient is a nonnegative integer, and their
sum is the uniform partition coefficient. All divisions take place in `ℚ`.

Source: Stacks Project, `dpa.tex`, Tag 07GP, proof of (5) for `x + y`;
explicit counting refinement (blueprint: lem-sfb-pd-colour-profile-coefficients).

Proof: (1) If `n = 0`, then `a = b = 0`; the only profile is zero and both sides
are one. Otherwise partition a labelled disjoint union of `a` red and `b` blue
elements into `n` unordered blocks of size `m`. Counting blocks and red elements
gives the two profile equations; the profile set is finite since each entry is at
most `n`. (2) For a fixed profile `r`, form `r i` slots with `i` red and `m - i`
blue positions. A red list and a blue list cut into these slots give such a
partition. There are `a! * b!` list pairs, by `Fintype.card_perm`
(`lem-sfb-finite-permutation-cardinality`). (3) Over a fixed partition, assign
the blocks of each type to its slots in `(r i)!` ways and order each red and blue
part in `i!` and `(m - i)!` ways. Assignment and ordering are inverse to cutting
and forgetting orders. The fibre size is exactly the displayed positive
denominator, again by the permutation count; empty colour parts have one order.
(4) Apply `Finset.card_eq_sum_card_fiberwise`
(`lem-sfb-finite-fibre-cardinality-sum`) to obtain that the coefficient is the
natural cardinality of partitions with profile `r`. (5) Cutting a list of all
`n * m` labels into `n` chunks of size `m` gives all uniform partitions. Each
fibre has `n! * (m!)^n` elements by ordering blocks and their elements, so the same
fibre-cardinality identity gives the right-hand quotient as their cardinality.
(6) Apply that identity once more to the map sending a partition to its profile.
Its fibres have the cardinalities in (4), so summing yields (5). In particular
the sum, being a finite sum of natural-number casts, is a nonnegative integer.
-/
theorem colourProfile_coefficients (n m a b : ℕ) (hm : 1 ≤ m) (hab : a + b = n * m) :
    (∀ r ∈ (Finset.Nat.antidiagonalTuple (m + 1) n).filter
        (fun r ↦ ∑ i : Fin (m + 1), (i : ℕ) * r i = a),
      ∃ c : ℕ,
        ((a.factorial * b.factorial : ℕ) : ℚ) /
          ((∏ i : Fin (m + 1),
            (r i).factorial * (i : ℕ).factorial ^ r i *
              (m - (i : ℕ)).factorial ^ r i : ℕ) : ℚ) = (c : ℚ)) ∧
    (∑ r ∈ (Finset.Nat.antidiagonalTuple (m + 1) n).filter
        (fun r ↦ ∑ i : Fin (m + 1), (i : ℕ) * r i = a),
      ((a.factorial * b.factorial : ℕ) : ℚ) /
        ((∏ i : Fin (m + 1),
          (r i).factorial * (i : ℕ).factorial ^ r i *
            (m - (i : ℕ)).factorial ^ r i : ℕ) : ℚ)) =
      (((n * m).factorial : ℕ) : ℚ) /
        ((n.factorial * m.factorial ^ n : ℕ) : ℚ) := by
  sorry

end Nat
