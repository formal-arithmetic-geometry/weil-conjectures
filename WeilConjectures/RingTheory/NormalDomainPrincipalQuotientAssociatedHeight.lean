/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.Ideal.Height
import WeilConjectures.RingTheory.SerreCriterionNormal
import WeilConjectures.RingTheory.SerreS2RegularQuotientAssociatedHeight

/-!
# Associated primes of principal quotients of normal domains

Every associated prime of a nonzero principal quotient `A / aA` of a Noetherian normal domain
has height one.

## Implementation details

The prime `p` contains `a`, so has height at least one. By Serre's criterion `A_p` satisfies
`(S₂)`; if `dim A_p ≥ 2`, the depth inequality for `0 → A → A → A / aA → 0` would give
`(A / aA)_p` positive depth, contradicting that `p A_p` is an associated prime of it.

## References

* [Stacks, Tag 031T]
-/

@[expose] public section

universe u

namespace Ideal

/-- Every associated prime of a nonzero principal quotient of a Noetherian normal domain
has height one. -/
theorem height_eq_one_of_mem_associatedPrimes_quotient_span
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    {a : A} (ha : a ≠ 0) {p : Ideal A}
    (hp : p ∈ associatedPrimes A (A ⧸ Ideal.span {a})) :
    p.height = 1 := by
  let : p.IsPrime := hp.isPrime
  have hS : Ring.IsSerreS A 2 :=
    (Ring.forall_isIntegrallyClosed_localization_iff_isSerreR_and_isSerreS A).mp (by
    intro q hq
    exact ⟨inferInstance,
      isIntegrallyClosed_of_isLocalization (Localization.AtPrime q) q.primeCompl
        q.primeCompl_le_nonZeroDivisors⟩) |>.2
  have hupper : p.height ≤ 1 :=
    height_le_one_of_mem_associatedPrimes_regular_quotient hS a
      (mem_nonZeroDivisors_iff_ne_zero.mpr ha) p hp
  have hamem : a ∈ p := by
    apply hp.annihilator_le
    rw [Submodule.mem_annihilator]
    intro y hy
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.mk (Ideal.span {a}) (a * b) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right b _ (Ideal.mem_span_singleton_self a)
  have hpbot : p ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hamem
    exact ha hamem
  exact le_antisymm hupper
    (Order.one_le_iff_ne_zero.mpr (Ideal.height_eq_zero_iff_eq_bot.not.mpr hpbot))

end Ideal
