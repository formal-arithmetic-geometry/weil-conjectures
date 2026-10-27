module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finite.Defs
import Mathlib.CategoryTheory.CofilteredSystem
import Mathlib.Order.WellQuasiOrder

/-!
# Uniform length bounds for controlled bad exponent sequences

Source: the agent-supplied controlled-Dickson argument supporting Dube, Theorem 8.2,
printed p.773; the theorem is surrounding context, not the source of this lemma.
The proof uses Stacks Project, Tag 086J, and Dickson's lemma in Mathlib.
(blueprint: lem-sfb-controlled-exponent-sequence-length)
-/

@[expose] public section

set_option autoImplicit false

namespace Order

/-- For each dimension and each prescribed bound on the sum of the coordinates at position
`i`, the lengths of finite bad exponent sequences have a uniform bound. No monotonicity of
`h` is assumed, and dimension zero and the empty sequence are included.

Source: the agent-supplied controlled-Dickson argument supporting Dube, Theorem 8.2,
printed p.773 (surrounding context only), using Stacks Project, Tag 086J, and Mathlib's
`Pi.wellQuasiOrderedLE`.
(blueprint: lem-sfb-controlled-exponent-sequence-length)

Proof:
1. Fix `r` and `h`. The set `E m` of permitted prefixes of length `m` is finite in the sense
   of `Set.Finite` (def-sfb-finite-infinite-set): each coordinate of entry `i` is at most
   `h i`, so it embeds in a finite product of intervals. `E 0` contains the empty prefix.
2. If lengths were unbounded, every `E m` would be nonempty by restriction of a longer
   permitted sequence. Prefix restrictions preserve the inequalities with their original
   indices, are identities at equal lengths, and compose. Thus they define a diagram on
   the small cofiltered category of natural numbers with arrows from larger to smaller
   indices; a common predecessor is given by the maximum, and parallel arrows agree.
3. Apply `nonempty_sections_of_finite_cofiltered_system`
   (lem-trf-cofiltered-finite-sets-section) to obtain compatible permitted prefixes `s m`.
   Put `beta i` equal to entry `i` of `s (i + 1)`. Compatibility identifies both `beta i`
   and `beta j`, for `i < j`, with the corresponding entries of `s (j + 1)`, so there is a
   coordinate at which `beta i` is strictly greater than `beta j`. No surjectivity of the
   restriction maps is needed.
4. Dickson's lemma, `wellQuasiOrdered_le` on `Fin r → ℕ` using
   `Pi.wellQuasiOrderedLE` (lem-trf-dickson-exponent-sequences), gives `i < j` with
   `beta i ≤ beta j`, a contradiction. Hence the lengths are bounded by some `L`.
   For `r = 0`, no pair can have a strictly decreasing coordinate, so `L = 1` works.
   If `h 0 = 0`, the first exponent vector is zero and again length is at most one.
   Zeros at later positions do not affect the argument, and the empty sequence has
   length zero, at most any natural bound. -/
theorem exists_bound_length_of_controlled_bad_exponent_sequence (r : ℕ) (h : ℕ → ℕ) :
    ∃ L : ℕ, ∀ (n : ℕ) (α : Fin n → Fin r → ℕ),
      (∀ i : Fin n, (∑ a : Fin r, α i a) ≤ h i.val) →
      (∀ i j : Fin n, i < j → ∃ a : Fin r, α j a < α i a) →
      n ≤ L := by
  sorry

end Order
