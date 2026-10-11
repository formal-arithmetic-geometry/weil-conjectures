/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Sheaf.RingTheory.AnnihilatorAssociatedPrimes
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Algebra.Module.LocalizedModule.AtPrime

/-!
# Localization at an associated prime

Source: Stacks Project, Algebra, Lemma 0310 (1), `lemma-associated-primes-localize`
(blueprint: lem-weil-pbc-associated-prime-localize-at-prime).
-/

universe u v

namespace Module

/-- Localization preserves an annihilator-defined associated prime.
Source: Stacks Project, Algebra, Lemma 0310 (1), lines 15393-15410.
(blueprint: lem-weil-pbc-associated-prime-localize-at-prime)

If `Ann_T(z) = q`, localization at the prime `q` has annihilator `q T_q` for `z/1`.
The node's proof proceeds as follows.

1. Choose `z` with annihilator `q`. The map `T → P`, `a ↦ a • z`, has kernel `q`,
   so it induces an injection `T/q → P`.
2. Localize at `T \ q`. Exactness (`lem-weil-pbc-localization-module-exact`) preserves
   this injection; the localized zero module is zero. Fractions and their maps use
   `def-weil-pbc-module-localization`.
3. For a fraction `a/s`, injectivity says `(a/s) • (z/1) = 0` exactly when `a/s = 0`
   in the localized quotient. This holds exactly when some `t ∉ q` has `t*a ∈ q`,
   hence, by primality, exactly when `a ∈ q`. These fractions form the extended ideal:
   each is `(a/1)*(1/s)`, and finite sums of generators have numerator in `q`.
4. By `def-weil-pbc-localization-at-prime`, the extended ideal is maximal, hence prime.
   Step 3 identifies it with the annihilator of `z/1`, proving association and the
   stated annihilator equality for every witness `z`. -/
theorem associated_prime_localize_at_prime
    {T : Type u} [CommRing T] {P : Type v} [AddCommGroup P] [Module T P]
    {q : Ideal T} [hq : q.IsPrime]
    (hqmem : q ∈ RingTheory.annihilatorAssociatedPrimes T P) :
    q.map (algebraMap T (Localization.AtPrime q)) ∈
      RingTheory.annihilatorAssociatedPrimes (Localization.AtPrime q)
        (LocalizedModule.AtPrime q P) ∧
    ∀ z : P, (⊥ : Submodule T P).colon {z} = q →
      (⊥ : Submodule (Localization.AtPrime q) (LocalizedModule.AtPrime q P)).colon
          {LocalizedModule.mk z 1} = q.map (algebraMap T (Localization.AtPrime q)) := by
  sorry

end Module
