/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Field.ULift

/-!
# Finite modules over an infinite field

## Main results

- `ModuleCat.isZero_ulift_of_finite`: a finite module over (a universe lift of) an infinite
  field is zero.
-/

@[expose] public section

universe u v w

open CategoryTheory Limits

/-- A finite module over (a universe lift of) an infinite field is zero: a nonzero vector `v`
would give an injection `c ↦ c • v` of the field into the module. The ring structure on
`ULift K` is `ULift.ring`, the one appearing in `ModuleCat (ULift K)`, which is not reducibly
the one underlying `ULift.field`. -/
theorem ModuleCat.isZero_ulift_of_finite {K : Type v} [Field K] [Infinite K]
    (M : ModuleCat.{w} (ULift.{u} K)) [Finite M] : IsZero M := by
  have : Subsingleton M := by
    refine subsingleton_of_forall_eq 0 fun v ↦ by_contra fun hv ↦ ?_
    refine not_finite_iff_infinite.2 inferInstance
      (Finite.of_injective (fun c : ULift.{u} K ↦ c • v) fun c d (h : c • v = d • v) ↦ ?_)
    refine by_contra fun hcd ↦ hv ?_
    rw [← one_smul (ULift.{u} K) v, ← inv_mul_cancel₀ (sub_ne_zero.2 hcd), mul_smul,
      sub_smul, h, sub_self, smul_zero]
  exact ModuleCat.isZero_of_subsingleton M
