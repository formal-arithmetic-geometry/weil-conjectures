/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.QuotSMulTop

/-!
# Global finite length for a fraction-field submodule

Source: Stacks Project, Algebra, Tag 00PF, `lemma-finite-length-global`
(blueprint: lem-sc-finite-length-global-submodule).
-/

universe u v

namespace Submodule

/-- For a Noetherian domain of dimension one, every submodule of a finite power of its
fraction field has finite length after reduction modulo a nonzero scalar.
Source: Stacks Project, Algebra, Tag 00PF, `lemma-finite-length-global`
(blueprint: lem-sc-finite-length-global-submodule).

Proof (the node's four steps):
1. If `x` is a unit, then `xM = M`, and the quotient is zero, of length zero
   (`def-weil-pbc-module-length`).
2. Otherwise `lem-sc-finite-maximals-over-element` supplies the finite set `S` of maximal
   ideals containing `x`. At each of these ideals the localized ring is a Noetherian local
   domain of dimension one with fraction field `K`; the localized module remains a submodule
   of `K^r`. Apply `lem-weil-pbc-dim-one-submodule-quotient-finite-length` to obtain finite
   length of each localized quotient.
3. Write `Q = M/xM`. Since `x` kills `Q`, its localizations outside `S` vanish. A nonzero
   subquotient has a nonzero element whose proper annihilator lies in a maximal ideal.
   This ideal contains `x`, so belongs to `S`; localization there preserves nonzeroness.
   Thus every strict submodule inclusion in `Q` remains strict at some ideal in `S`.
4. Assign each step of a strict chain in `Q` to one such ideal. At a fixed ideal, the number
   of assigned steps is bounded by the finite local length from step 2. Summing these bounds
   over `S` bounds every chain length, so `Module.length R Q` is finite
   (`def-weil-pbc-module-length`). -/
theorem length_quotSMulTop_lt_top_of_ringKrullDim_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]
    (r : ℕ) (M : Submodule R (Fin r → K)) (hdim : ringKrullDim R = 1)
    (x : R) (hx : x ≠ 0) : Module.length R (QuotSMulTop x M) < ⊤ := by
  sorry

end Submodule
