/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import WeilConjectures.RingTheory.DepthLeDimAssociatedPrime
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors

/-!
# Associated primes of a Cohen–Macaulay local ring are minimal

In a Noetherian local ring of finite dimension `e` and depth at least `e` (for instance a
Cohen–Macaulay local ring), every associated prime is minimal.

## Implementation details

An associated prime `p` satisfies `dim(T/p) ≥ depth(T) ≥ e` [Stacks, Tag 0BK4]. A prime strictly
below `p` could be prepended to a chain of length `e` above `p`, contradicting `dim T = e`.

## References

* [Stacks, Tag 0BUS] (Algebra, Lemma 10.103.7), for the ring as a module over itself
* [Stacks, Tag 00N8] (Algebra, Definition 10.104.1)
* [Stacks, Tag 0BK4]
-/

@[expose] public section

universe u

namespace Ideal

/-- In a Noetherian local ring of finite dimension `e` and depth at least `e`, every
associated prime is minimal. -/
theorem mem_minimalPrimes_of_depth_ge {T : Type u} [CommRing T] [IsNoetherianRing T]
    [IsLocalRing T] (e : ℕ) (hdim : ringKrullDim T = (e : WithBot ℕ∞))
    (hdepth : (e : ℕ∞) ≤ IsLocalRing.depth (R := T) T) (p : Ideal T)
    (hp : p ∈ associatedPrimes T T) :
    p ∈ minimalPrimes T := by
  have hquot : (e : WithBot ℕ∞) ≤ ringKrullDim (T ⧸ p) := by
    exact (WithBot.coe_le_coe.mpr hdepth).trans
      (IsLocalRing.depth_le_ringKrullDim_quotient_of_mem_associatedPrimes p hp)
  rw [minimalPrimes_eq_minimals]
  refine ⟨hp.isPrime, ?_⟩
  intro q hq hqp
  by_contra hpq
  obtain ⟨x, hxp, hxq⟩ := IsConcreteLE.not_le_iff_exists.mp hpq
  let : q.IsPrime := hq
  have hdrop : ringKrullDim (T ⧸ p) + 1 ≤ ringKrullDim (T ⧸ q) := by
    apply ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hqp)
      (Ideal.Quotient.factor_surjective hqp) (r := Ideal.Quotient.mk q x)
    · exact mem_nonZeroDivisors_iff_ne_zero.mpr
        (fun heq ↦ hxq (Ideal.Quotient.eq_zero_iff_mem.mp heq))
    · simpa only [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem] using hxp
  have hbad : (e : WithBot ℕ∞) + 1 ≤ (e : WithBot ℕ∞) := by
    calc
      (e : WithBot ℕ∞) + 1 ≤ ringKrullDim (T ⧸ p) + 1 := by
        simpa only [add_comm] using add_le_add_right hquot 1
      _ ≤ ringKrullDim (T ⧸ q) := hdrop
      _ ≤ ringKrullDim T := ringKrullDim_quotient_le q
      _ = (e : WithBot ℕ∞) := hdim
  have : ((e + 1 : ℕ) : WithBot ℕ∞) ≤ (e : WithBot ℕ∞) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hbad
  exact Nat.not_succ_le_self e (by exact_mod_cast this)

end Ideal
