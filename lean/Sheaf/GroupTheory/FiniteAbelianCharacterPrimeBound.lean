module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Hom.Instances
public import Mathlib.Data.Nat.Factorization.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Prime-to-characteristic bound for finite abelian characters

Source: Gabber--Ramero, Almost Ring Theory, Section 6.2.8, pairing (6.2.9), and
Proposition 6.2.12, first paragraph; the general finite-character bound is an
agent-written auxiliary. Root counting follows Stacks Project, Fields, Tag 09HW.
(blueprint: lem-trf-finite-abelian-character-prime-bound)
-/

@[expose] public section

universe u v

namespace CommGroup

/-- The characters of a finite abelian group over an arbitrary field form a finite
group, with order at most the prime-to-characteristic part of the source's order.
Here `ordCompl[p] n` is `n / p ^ n.factorization p`; when `p = 0`, it equals `n`.
The group `A →* kˣ` has Mathlib's pointwise multiplication.

Source: Gabber--Ramero, Almost Ring Theory, Section 6.2.8, pairing (6.2.9), and
Proposition 6.2.12, first paragraph; general auxiliary extracted by the agent.
(blueprint: lem-trf-finite-abelian-character-prime-bound)

Proof plan:
1. By `lem-trf-finite-abelian-cyclic-product`, write A as a finite product of cyclic
   groups of orders d_i > 1. Their standard generators generate A, and |A| = product d_i.
2. In characteristic zero set m_i = d_i. Otherwise the characteristic p is prime,
   since a field is nontrivial and has no zero divisors (`def-weil-field`). Write
   d_i = p ^ a_i * m_i with m_i coprime to p. Then product m_i is the largest
   divisor of |A| coprime to p, namely the displayed `ordCompl`.
3. Every character sends the i-th generator to a d_i-th root of unity. By
   `lem-trf-roots-of-unity-remove-characteristic-power`, it is an m_i-th root.
   Evaluation on these generators injects the characters into the product of
   the groups of m_i-th roots: agreement on generators implies agreement on A.
4. By `lem-exc-field-roots-cyclic-bound` (Stacks Tag 09HW), each factor is finite
   of order at most m_i. The product has order at most product m_i, proving both
   claims. The empty product is a singleton, covering the trivial source group.
-/
theorem finite_monoidHom_units_and_card_le_ordCompl
    (A : Type u) [CommGroup A] [Finite A] (k : Type v) [Field k] :
    Finite (A →* kˣ) ∧ Nat.card (A →* kˣ) ≤ ordCompl[ringChar k] (Nat.card A) := by
  sorry

end CommGroup
