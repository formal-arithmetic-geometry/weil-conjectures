module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Localization.Ideal

/-!
# Endpoints of full-dimensional local prime chains

Source: Stacks Project, Algebra, Tags 00E3 and 00KE; Morphisms, Tag 02JX,
proof of the equality clause (blueprint: lem-trf-full-dimension-local-chain-contraction).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Ideal

/-- If a domain and its localization at a maximal ideal both have dimension `r`,
there exists a strict prime chain of length `r` in that localization, and every
such chain contracts strictly from the zero ideal to the given maximal ideal.

Source: Stacks Project, Algebra, Tag 00E3 (lemma-spec-localization) and
Tag 00KE (definition-Krull), expanding the maximal local chain argument in
Morphisms, Tag 02JX (lemma-alteration-dimension), proof of the equality clause.
(blueprint: lem-trf-full-dimension-local-chain-contraction).

Proof:
1. Krull dimension is the supremum of the integer lengths of strict prime chains.
   A finite value `r` is attained: otherwise all lengths are at most `r - 1`.
   For `r = 0`, absence of a chain would give dimension negative infinity.
   The equality for `A` also bounds every prime-chain length in `A` by `r`.
2. The maximal ideal `m` is prime. The order-preserving prime correspondence
   of lem-weil-pbc-primes-of-localization contracts each prime to a prime below
   `m`; injectivity of this correspondence preserves strictness.
3. The zero ideal of the nonzero domain `A` is prime. If the first contracted
   prime were nonzero, prepending zero would give a chain of length `r + 1`
   in `A`, contradicting its dimension. Thus the first contracted prime is zero.
4. If the last contracted prime were strictly below `m`, appending `m` would
   similarly contradict the dimension of `A`. Thus it equals `m`. These same
   arguments apply to a singleton chain when `r = 0`, giving both endpoints.
-/
theorem full_dimension_local_chain_contraction
    {A : Type u} [CommRing A] [IsDomain A] (m : Ideal A) [m.IsMaximal]
    (r : ℕ) (hA : ringKrullDim A = (r : WithBot ℕ∞))
    (hB : ringKrullDim (Localization.AtPrime m) = (r : WithBot ℕ∞)) :
    (∃ q : Fin (r + 1) → Ideal (Localization.AtPrime m),
      (∀ i : Fin (r + 1), (q i).IsPrime) ∧ StrictMono q) ∧
    (∀ q : Fin (r + 1) → Ideal (Localization.AtPrime m),
      (∀ i : Fin (r + 1), (q i).IsPrime) → StrictMono q →
      (∀ i : Fin (r + 1),
        (Ideal.comap (algebraMap A (Localization.AtPrime m)) (q i)).IsPrime) ∧
      StrictMono (fun i ↦ Ideal.comap (algebraMap A (Localization.AtPrime m)) (q i)) ∧
      (∀ i : Fin (r + 1),
        Ideal.comap (algebraMap A (Localization.AtPrime m)) (q i) ≤ m) ∧
      Ideal.comap (algebraMap A (Localization.AtPrime m)) (q 0) = ⊥ ∧
      Ideal.comap (algebraMap A (Localization.AtPrime m)) (q (Fin.last r)) = m) := sorry

end Ideal
