/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
import Sheaf.RingTheory.AnnihilatorAssociatedPrimes
import Mathlib.Algebra.Exact.Basic

/-!
# Associated primes in a short exact sequence over an arbitrary ring

Source: Stacks Project, Algebra, Lemma 02M3 (lemma-ass), first two assertions
(blueprint: lem-weil-pbc-associated-primes-exact-sequence).
-/

universe uR uSub uMid uQuot

namespace RingTheory

/-- In a short exact sequence, associated primes of the submodule are associated to the
middle module, whose associated primes belong to those of either outer module.
An injective linear map also preserves every element annihilator.
Source: Stacks Project, Algebra, Lemma 02M3, first two assertions and their proof
(blueprint: lem-weil-pbc-associated-primes-exact-sequence).

Proof (the three elementary steps of the node):
1. Linearity gives `a • f z' = f (a • z')`; injectivity makes this zero exactly when
   `a • z' = 0`. Thus annihilators are equal and the first inclusion follows.
2. Let `q = Ann(z)` be prime. If some `s ∉ q` has `s • z` in the image of `f`, write
   it as `f z'`. Primality gives `a * s ∈ q` iff `a ∈ q`, so `Ann(s • z) = q`.
   Step 1 gives `Ann(z') = q`, placing `q` among the submodule's associated primes.
3. Otherwise every `s ∉ q` has `s • g z ≠ 0`, by exactness. Elements of `q` kill
   `g z` by linearity, and no element outside `q` does. Thus `Ann(g z) = q` and
   `q` is associated to the quotient. The two cases prove the second inclusion.
No Noetherian assumption is used; surjectivity is retained as part of short exactness. -/
theorem annihilatorAssociatedPrimes_of_shortExact
    {R : Type uR} [CommRing R]
    {M' : Type uSub} [AddCommGroup M'] [Module R M']
    {M : Type uMid} [AddCommGroup M] [Module R M]
    {M'' : Type uQuot} [AddCommGroup M''] [Module R M'']
    (f : M' →ₗ[R] M) (g : M →ₗ[R] M'')
    (hf : Function.Injective f) (hfg : Function.Exact f g)
    (hg : Function.Surjective g) :
    (annihilatorAssociatedPrimes R M' ⊆ annihilatorAssociatedPrimes R M) ∧
    (∀ z' : M', (⊥ : Submodule R M).colon {f z'} =
      (⊥ : Submodule R M').colon {z'}) ∧
    (annihilatorAssociatedPrimes R M ⊆
      annihilatorAssociatedPrimes R M' ∪ annihilatorAssociatedPrimes R M'') := by
  sorry

end RingTheory
