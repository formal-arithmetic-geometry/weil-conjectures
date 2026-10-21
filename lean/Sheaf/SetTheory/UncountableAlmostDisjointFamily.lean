module

public import Mathlib.Data.Countable.Defs
public import Mathlib.Data.Finite.Defs
import Mathlib.Logic.Function.Basic

/-!
# An uncountable almost-disjoint family of infinite subsets of the natural numbers

Source: the agent-written combinatorial auxiliary in the DAG node below, supporting
literature/blueprint/main-20261015/blueprint/sec-six-functors-basics/
sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3).
The blueprint paragraph supplies the coefficient application, not this combinatorial assertion;
an exact literature reference is still wanted, as recorded by the node.
(blueprint: lem-sfb-uncountable-almost-disjoint-family)
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Set

/-- There is an uncountable family of infinite subsets of `ℕ` with finite intersections
between distinct members.

Source: the agent-written binary-prefix proof in the DAG node, an auxiliary supporting
paragraph (3) of sk-thm-sf-ctf-stability-direct-images.proof.md in the main-20261015 blueprint.

Proof: take the index type to be `Set ℕ`, lifted to universe `u` if necessary. Cantor's
no-injection theorem `Function.cantor_injective` makes this index type uncountable.
Encode finite binary words by `c([]) = 1` and `c(b :: w) = 2 * c(w) + b`, with digits
zero and one. The codes are positive. The code is injective: an empty word has code one,
whereas a nonempty word has code at least two; for two nonempty words with equal codes,
parity identifies the heads, and cancellation identifies the tail codes. Induction then
identifies the tails and the words.

For a subset `S` of `ℕ`, let `w_S(n)` be its membership word in positions zero through
`n - 1`, and take `A_S` to be the range of `n ↦ c(w_S(n))`. Equal codes give equal words
and therefore equal lengths, so this map is injective and its range is infinite. More
explicitly, a finite range of size `r` cannot contain the `r + 1` distinct codes with
lengths zero through `r`.

For distinct subsets `S` and `T`, choose a coordinate `k` at which membership differs.
A shared code must come from prefixes of the same length `n`. If `k < n`, equality of
those words contradicts the differing digits at `k`. Thus `n ≤ k`, and the intersection
is contained in the finite set of prefix codes of `S` of lengths zero through `k`.
These sets give all three required properties, preserved under lifting the index type.
(blueprint: lem-sfb-uncountable-almost-disjoint-family) -/
theorem exists_uncountable_almostDisjoint_family :
    ∃ (I : Type u) (A : I → Set ℕ),
      ¬ Countable I ∧ (∀ i : I, (A i).Infinite) ∧
        ∀ i j : I, i ≠ j → (A i ∩ A j).Finite := by
  sorry

end Set
