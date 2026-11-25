/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.SerreConditions
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import WeilConjectures.RingTheory.SerreS2RegularQuotientAssociatedHeight

/-!
# Membership in a reduced S2 ring detected in codimension one

The argument of [Stacks, Tag 031T] uses only condition S2 and applies to nonzerodivisor
denominators in a reduced ring.

## References

* [Stacks, Tag 031T]
-/

@[expose] public section

universe u

/-- A total fraction of a reduced Noetherian S2 ring lies in the ring if it does so
at every prime of height at most one, expressed by clearing a local denominator. -/
theorem Ring.exists_algebraMap_eq_of_serreS_two
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsReduced R]
    (hS : Ring.IsSerreS R 2) (x : FractionRing R)
    (hlocal : ∀ (p : Ideal R) [p.IsPrime], p.height ≤ (1 : ℕ∞) →
      ∃ s : R, s ∉ p ∧ ∃ a : R,
        algebraMap R (FractionRing R) s * x = algebraMap R (FractionRing R) a) :
    ∃ a : R, algebraMap R (FractionRing R) a = x  := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors R) x
  by_cases ha : a ∈ Ideal.span {(b : R)}
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ha
    refine ⟨c, ?_⟩
    apply (IsLocalization.map_units (FractionRing R) b).mul_left_cancel
    calc
      algebraMap R (FractionRing R) b * algebraMap R (FractionRing R) c =
          algebraMap R (FractionRing R) a := by rw [← map_mul, mul_comm, hc]
      _ = algebraMap R (FractionRing R) b * x := by rw [← hab, mul_comm]
  · have hclass : Ideal.Quotient.mk (Ideal.span {(b : R)}) a ≠ 0 := by
      simpa only [ne_eq, Ideal.Quotient.eq_zero_iff_mem] using ha
    obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hclass
    let := hp.isPrime
    have hheight := Ideal.height_le_one_of_mem_associatedPrimes_regular_quotient hS
      b b.prop p hp
    obtain ⟨s, hs, c, hsc⟩ := hlocal p hheight
    have hsa : s * a = c * b := by
      apply IsFractionRing.injective R (FractionRing R)
      simp only [map_mul]
      calc
        algebraMap R (FractionRing R) s * algebraMap R (FractionRing R) a =
            algebraMap R (FractionRing R) s *
              (x * algebraMap R (FractionRing R) b) := by rw [hab]
        _ = (algebraMap R (FractionRing R) s * x) *
            algebraMap R (FractionRing R) b := by ring
        _ = algebraMap R (FractionRing R) c * algebraMap R (FractionRing R) b := by
          rw [hsc]
    apply False.elim (hs (hle ?_))
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot]
    change Ideal.Quotient.mk (Ideal.span {(b : R)}) (s * a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem, hsa]
    exact Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩

