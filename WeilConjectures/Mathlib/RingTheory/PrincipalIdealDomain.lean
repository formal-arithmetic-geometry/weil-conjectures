/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Quotients of principal ideal domains by prime powers

The quotient of a principal ideal domain by a power of an irreducible element is a local ring
(`isLocalRing_quotient_span_singleton_pow`).
-/

@[expose] public section

/-- The quotient of a principal ideal domain by a power of an irreducible element is a
local ring. -/
theorem isLocalRing_quotient_span_singleton_pow {A : Type*} [CommRing A] [IsDomain A]
    [IsPrincipalIdealRing A] {p : A} (hp : Irreducible p) {n : ℕ} (hn : n ≠ 0) :
    IsLocalRing (A ⧸ Ideal.span {p ^ n}) := by
  have hnt : Nontrivial (A ⧸ Ideal.span {p ^ n}) := by
    refine Ideal.Quotient.nontrivial_iff.mpr ?_
    rw [ne_eq, Ideal.span_singleton_eq_top, isUnit_pow_iff hn]
    exact hp.not_isUnit
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a ↦ ?_
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective a
  rcases hp.isCoprime_or_dvd g with hc | hd
  · obtain ⟨u, v, huv⟩ := (hc.pow_left : IsCoprime (p ^ n) g)
    refine .inl (IsUnit.of_mul_eq_one (Ideal.Quotient.mk _ v) ?_)
    have : Ideal.Quotient.mk (Ideal.span {p ^ n}) (u * p ^ n + v * g) = 1 := by rw [huv, map_one]
    simpa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, mul_comm] using this
  · refine .inr (IsNilpotent.isUnit_one_sub ⟨n, ?_⟩)
    obtain ⟨c, rfl⟩ := hd
    rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, mul_pow]
    exact Dvd.intro _ rfl
