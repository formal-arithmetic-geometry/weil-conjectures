/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section

namespace IsLocalRing

/-- An element outside the square of a principal maximal ideal spans that ideal. -/
theorem maximalIdeal_le_span_of_isPrincipal_of_not_mem_square
    {C : Type*} [CommRing C] [IsLocalRing C] (tau : C)
    (hm : Submodule.IsPrincipal (maximalIdeal C))
    (htau : tau ∉ maximalIdeal C * maximalIdeal C) :
    maximalIdeal C ≤ Ideal.span {tau} := by
  classical
  by_cases hu : IsUnit tau
  · rw [Ideal.span_singleton_eq_top.mpr hu]
    exact le_top
  let := hm
  let r := Submodule.IsPrincipal.generator (maximalIdeal C)
  have hr : r ∈ maximalIdeal C := Submodule.IsPrincipal.generator_mem _
  have hspan : Ideal.span {r} = maximalIdeal C := Ideal.span_singleton_generator _
  have hmem : tau ∈ maximalIdeal C := (mem_maximalIdeal tau).mpr hu
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hspan.symm ▸ hmem)
  have hcu : IsUnit c := by
    by_contra h
    apply htau
    rw [← hc]
    exact Ideal.mul_mem_mul ((mem_maximalIdeal c).mpr h) hr
  rw [← hc, Ideal.span_singleton_mul_left_unit hcu, hspan]

end IsLocalRing
