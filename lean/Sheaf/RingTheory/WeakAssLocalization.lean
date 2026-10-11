/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.Algebra.Module.LocalizedModule.AtPrime
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.Colon

/-!
# Weak association detected by localization at a prime

Source: Stacks Project, Algebra, Lemma 10.66.2, Tag 0566
(blueprint: lem-sc-weakass-localization).
-/

universe u v

namespace Module

/-- Weak association of `p` to `M`, weak association of its extension to `Mₚ`, and existence
of an element of `Mₚ` whose annihilator has radical `p Rₚ` are equivalent.
Source: Stacks Project, Algebra, Lemma 10.66.2, Tag 0566
(blueprint: lem-sc-weakass-localization).

Proof:
1. Suppose `p` is minimal over `Ann_R(m) = I`. The annihilator of `m/1` is `I Rₚ`:
   if `(r/s)(m/1) = 0`, some `t ∉ p` satisfies `trm = 0`, and `r/s = (tr)/(ts)`
   belongs to the extended ideal; the other inclusion follows from scalar multiplication.
   The prime correspondence of `lem-weil-pbc-primes-of-localization` identifies primes
   of `Rₚ` with primes of `R` contained in `p`. Thus the only prime containing `I Rₚ`
   is `p Rₚ`, and the intersection-of-primes description of the radical gives clause (3).
2. If an element's annihilator has radical `p Rₚ`, every prime containing that
   annihilator contains its radical. Since `p Rₚ` is prime, it is minimal over the
   annihilator, giving clause (2).
3. Conversely, write a witness for clause (2) as `m/s`. Multiplication by the unit `s`
   preserves its annihilator, so `p Rₚ` is minimal over `Ann_R(m) Rₚ`, by the same
   denominator calculation as in step 1. The prime correspondence of
   `lem-weil-pbc-primes-of-localization` contracts `p Rₚ` to `p`, which therefore
   contains `Ann_R(m)`. A strictly smaller prime containing `Ann_R(m)` would extend
   to a strictly smaller prime containing the localized annihilator, contradicting
   minimality. This gives clause (1). -/
theorem weakly_associated_atPrime_iff
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    (p : Ideal R) [p.IsPrime] :
    ((∃ m : M, p ∈ ((⊥ : Submodule R M).colon {m}).minimalPrimes) ↔
      (∃ x : LocalizedModule.AtPrime p M,
        p.map (algebraMap R (Localization.AtPrime p)) ∈
          ((⊥ : Submodule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).colon
            {x}).minimalPrimes)) ∧
    ((∃ x : LocalizedModule.AtPrime p M,
        p.map (algebraMap R (Localization.AtPrime p)) ∈
          ((⊥ : Submodule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).colon
            {x}).minimalPrimes) ↔
      (∃ x : LocalizedModule.AtPrime p M,
        ((⊥ : Submodule (Localization.AtPrime p) (LocalizedModule.AtPrime p M)).colon
          {x}).radical = p.map (algebraMap R (Localization.AtPrime p)))) := by
  sorry

end Module
