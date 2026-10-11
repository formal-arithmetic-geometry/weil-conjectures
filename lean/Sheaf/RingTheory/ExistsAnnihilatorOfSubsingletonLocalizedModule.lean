/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.Finiteness.Defs

/-!
# A uniform annihilator for a finite module with zero localization

Source: Stacks Project, Exercise 076A and the proof of Lemma 07FC
(blueprint: lem-weil-pbc-finite-module-localization-zero-annihilator).
-/

universe u v

namespace Module

/-- A finitely generated module whose localization at a multiplicative subset is zero
is annihilated by one element of that subset. Source: Stacks Project, Exercise 076A,
and the uniform-annihilator form used in the proof of Lemma 07FC.
(blueprint: lem-weil-pbc-finite-module-localization-zero-annihilator)

Proof:
1. Choose finitely many generators `m₁, …, mₙ` using
   `def-weil-finitely-generated-module`; every element is a linear combination of them.
2. Each generator maps to zero in the localization. The kernel description in
   `def-weil-pbc-module-localization` supplies `tᵢ ∈ S` with `tᵢ • mᵢ = 0`.
3. Let `s` be the product of the `tᵢ`, with empty product `1`. Multiplicativity gives
   `s ∈ S`. Commutativity shows that `s` kills every generator, and linearity then
   shows that it kills every linear combination, hence every element of `M`. -/
theorem exists_annihilator_of_subsingleton_localizedModule
    {A : Type u} [CommRing A] (S : Submonoid A)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (hzero : Subsingleton (LocalizedModule S M)) :
    ∃ s ∈ S, ∀ m : M, s • m = 0 := by
  sorry

end Module
