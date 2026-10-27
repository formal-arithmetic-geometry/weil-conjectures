module

public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.IndexNormal

/-!
# A normal subgroup of prime index in a finite p-group

Source: Stacks Project, more-algebra.tex, Tag 09F8, lemma-special-case, third proof
paragraph after Tag 09EE, lemma-galois-inertia. This is the agent-supplied group-theoretic
refinement supporting the filtration there, rather than a lemma stated in Stacks.
(blueprint: lem-sfb-finite-p-group-normal-index-p)
-/

@[expose] public section

universe u

namespace Subgroup

/-- A finite group of order `p ^ a`, with `p` prime and `a ≥ 1`, has a normal subgroup
of index `p`.

Source: Stacks Project, more-algebra.tex, Tag 09F8, lemma-special-case, third proof
paragraph after Tag 09EE, lemma-galois-inertia; agent-supplied group-theoretic refinement.
(blueprint: lem-sfb-finite-p-group-normal-index-p)

Proof: Write `a = b + 1`. By `lem-sfb-finite-subgroup-prime-power-order`
(`Sylow.exists_subgroup_card_pow_prime`), choose a subgroup `H` of order `p ^ b`.
Apply `lem-sfb-surjective-subgroup-image-index` to the identity surjection and `H`:
its order-index formula (`Subgroup.card_mul_index`) gives
`p ^ b * H.index = p ^ (b + 1) = p ^ b * p`. Since `p` is prime, `p ^ b > 0`,
so cancellation gives `H.index = p`. Every prime divisor of `p ^ (b + 1)` equals
`p`, by the prime-divides-product rule, while `p` itself divides this number.
Thus `p` is its least prime divisor and the group has more than one element.
Apply `lem-sfb-least-prime-index-normal`
(`Subgroup.normal_of_index_eq_minFac_card`) to conclude `H.Normal`.
Normality means conjugation preserves `H`; applying this also with the inverse
conjugating element gives the equality `g H g⁻¹ = H` for every `g`.
-/
theorem exists_normal_index_prime_of_card_eq_prime_pow
    (P : Type u) [Group P] [Finite P] (p a : ℕ) (hp : p.Prime)
    (ha : 1 ≤ a) (hcard : Nat.card P = p ^ a) :
    ∃ H : Subgroup P, H.Normal ∧ H.index = p := by
  sorry

end Subgroup
