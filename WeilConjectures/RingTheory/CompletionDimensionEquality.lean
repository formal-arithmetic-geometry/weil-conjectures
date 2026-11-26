/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import WeilConjectures.RingTheory.AdicCompletionNoetherian
set_option autoImplicit false
@[expose] public section
universe u
namespace RingTheory
/-!
# Krull dimension of the completion of a Noetherian local ring

The completion of a Noetherian local ring at its maximal ideal has the same Krull dimension.

## Implementation details

The proof applies the flat height formula to the flat map from `A` to its completion, which is
local with the extended maximal ideal and whose closed fibre is the residue field.
-/
/-- The maximal-ideal adic completion of a Noetherian local ring has the same Krull dimension
as the ring. -/
theorem completion_dimension_eq (A : Type u) [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] :
    ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal A) A) = ringKrullDim A := by
  let B := AdicCompletion (IsLocalRing.maximalIdeal A) A
  set_option linter.style.haveILetI false in
  letI : IsNoetherianRing B := AdicCompletion.isNoetherianRing _
  set_option linter.style.haveILetI false in
  letI : IsLocalRing B := inferInstance
  set_option linter.style.haveILetI false in
  letI : IsLocalHom (algebraMap A B) := inferInstance
  set_option linter.style.haveILetI false in
  letI : (IsLocalRing.maximalIdeal B).LiesOver (IsLocalRing.maximalIdeal A) :=
    ⟨(IsLocalRing.maximalIdeal_comap (algebraMap A B)).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal B)
  rw [← AdicCompletion.maximalIdeal_eq_map] at h
  rw [Ideal.map_quotient_self] at h
  simp only [Ideal.height_bot, add_zero] at h
  have h' := congrArg (fun n : ℕ∞ => (n : WithBot ℕ∞)) h
  change ringKrullDim B = ringKrullDim A
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim,
    ← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact h'

end RingTheory
