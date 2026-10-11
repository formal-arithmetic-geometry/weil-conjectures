/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.QuotSMulTop

/-!
# Associated primes of quotients by powers of an element

Source: Stacks Project, Algebra, Lemma 0CN5 (lemma-inherit-minimal-primes)
(blueprint: lem-weil-pbc-associated-prime-power-quotient).
-/

universe u v

namespace Module

/-- Source: Stacks Project, Algebra, Lemma 0CN5
(blueprint: lem-weil-pbc-associated-prime-power-quotient).
A prime minimal over `p + (x)`, with `p` associated to `M`, is associated to
`M / x^n M` for some positive `n`.

Proof:
1. Choose `z` with annihilator `p`; its cyclic submodule `N = Rz` is isomorphic to `R/p`,
   and `N/xN` is isomorphic to `R/(p + (x))`.
2. Apply Artin--Rees (lem-weil-pbc-artin-rees) to `(x)` and `N` inside `M`.
   If its constant is `c`, take `n = c + 1`, giving `N ∩ x^n M ⊆ xN`.
3. Let `Nbar` be the image of `N` in `M/x^n M`. It is finite and isomorphic to
   `N/(N ∩ x^n M)`. By lem-weil-pbc-associated-prime-submodule it suffices to
   show that `q` is associated to `Nbar`.
4. The inclusion in step 2 gives a surjection `Nbar → R/(p + (x))`, so
   `Ann(Nbar) ⊆ p + (x) ⊆ q`. By lem-weil-pbc-finite-module-support-annihilator,
   `q` belongs to the support of `Nbar`.
5. Both `p` and `x^n` annihilate `Nbar`. Any prime in its support contained in `q`
   therefore contains `p` and `x`, hence equals `q` by minimality over `p + (x)`.
   Thus `q` is minimal in the support, using the support-annihilator lemma again.
6. By lem-weil-pbc-minimal-support-prime-associated, `q` is associated to `Nbar`;
   the submodule lemma then puts it in the associated primes of `M/x^n M`. -/
theorem exists_mem_associatedPrimes_quotient_pow
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hx : x ∈ IsLocalRing.maximalIdeal R)
    (p q : Ideal R) (hp : p ∈ associatedPrimes R M)
    (hq : q ∈ (p ⊔ Ideal.span {x}).minimalPrimes) :
    ∃ n : ℕ, 1 ≤ n ∧ q ∈ associatedPrimes R (QuotSMulTop (x ^ n) M) := by
  sorry

end Module
