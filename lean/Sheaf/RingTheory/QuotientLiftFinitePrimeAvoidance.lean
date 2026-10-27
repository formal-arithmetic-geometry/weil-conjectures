module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Operations

/-!
# Lifting a residue class while avoiding finitely many primes

Source: Stacks Project, Varieties, Tag 09NK, Lemma `lemma-extra-silly`
(blueprint: lem-trf-quotient-lift-finite-prime-avoidance).
-/

@[expose] public section

universe u

namespace Ideal

/-- Every residue class modulo an ideal not contained in any of finitely many prime ideals
has a representative outside all of them. The points of `Spec A` are the prime ideals of `A`.
The family may be empty, repeated or comparable, and `A` may be the zero ring.

Source: Stacks Project, Varieties, Tag 09NK, Lemma `lemma-extra-silly`
(blueprint: lem-trf-quotient-lift-finite-prime-avoidance).

Proof:
1. Discard repeated primes and primes strictly contained in another listed prime. Finiteness
   ensures every discarded prime lies in a retained one, so avoiding the remaining pairwise
   incomparable primes suffices. Choose a representative `a` of `fbar`. If no primes remain,
   take `a`; this includes the zero ring.
2. Let `S` index retained primes containing `a` and let `T` be the remaining indices. If `S`
   is empty, take `a`. Otherwise set `J` to the intersection of `I` with the primes in `T`,
   with the empty intersection equal to the whole ring.
3. For each `s` in `S`, choose `u_s` in `I` outside `p_s`. For each `i` in `T`, choose
   `v_{i,s}` in `p_i` outside `p_s`, using incomparability. The element
   `u_s * product (v_{i,s})` lies in `J` and is outside `p_s` by primality. Thus `J` is not
   contained in any prime indexed by `S`, including when `T` is empty.
4. Apply prime avoidance (`lem-weil-pbc-prime-avoidance`, `Ideal.subset_union_prime`) to `J`
   and the nonempty family indexed by `S`, obtaining `g` in `J` outside every such prime.
5. Take `f = a + g`. Since `g` lies in `I`, this has residue class `fbar`. If `s` is in `S`,
   membership of `f` in `p_s` would force `g = f - a` into `p_s`. If `i` is in `T`, membership
   of `f` in `p_i` would force `a = f - g` into `p_i`. Both are contradictions. Step 1 then
   gives avoidance of every original prime. -/
theorem exists_quotient_representative_notMem_primes {A : Type u} [CommRing A]
    (I : Ideal A) {r : ℕ} (p : Fin r → AlgebraicGeometry.Spec (CommRingCat.of A))
    (hI : ∀ i : Fin r, ¬ I ≤ (p i).asIdeal) (fbar : A ⧸ I) :
    ∃ f : A, Ideal.Quotient.mk I f = fbar ∧ ∀ i : Fin r, f ∉ (p i).asIdeal := by
  sorry

end Ideal
