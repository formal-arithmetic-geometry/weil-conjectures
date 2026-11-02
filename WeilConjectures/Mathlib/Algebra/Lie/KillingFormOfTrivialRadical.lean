/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Lie.TraceForm
import WeilConjectures.Mathlib.Algebra.Lie.CartanCriterion

/-!
# The Killing form when the radical vanishes

Source: `literature/blueprint/latest/blueprint/part-appendices/`
`sec-algebraic-groups-lie-algebras/sec-reductive-lie-algebras/sk-lem-walg-killing/_section.md`
and `sk-lem-walg-killing.proof.md` there.
(blueprint: sk-lem-walg-killing)

The Killing form of a finite-dimensional characteristic-zero Lie algebra with zero solvable
radical is nondegenerate, and the algebra equals its derived algebra.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace LieAlgebra

open LieModule

/-- The Killing form is nondegenerate and the derived algebra is the whole algebra when the
solvable radical vanishes.

Source: `literature/blueprint/latest/blueprint/part-appendices/`
`sec-algebraic-groups-lie-algebras/sec-reductive-lie-algebras/sk-lem-walg-killing/_section.md`,
proof in `sk-lem-walg-killing.proof.md` there.
(blueprint: sk-lem-walg-killing)

Proof: instantiate `HasTrivialRadical` from `hrad`; the source Cartan criterion theorem
`HasTrivialRadical.killingForm_nondegenerate` gives nondegeneracy. For the derived ideal
`D = derivedSeries k g 1`, Mathlib's invariant Killing-form complement theorem gives
`IsCompl D D.killingCompl`. If `z ∈ D.killingCompl`, every bracket `⁅x,z⁆` lies both in D
and in its complement, hence is zero; therefore z is central. Since the center is contained
in the radical and `hrad` identifies the radical with zero, `D.killingCompl = 0`. The
complement equation then yields `D = ⊤`. -/
theorem killingForm_nondegenerate_and_derived_eq_top_of_radical_eq_bot
    (k : Type u) (g : Type v) [Field k] [CharZero k] [LieRing g] [LieAlgebra k g]
    [FiniteDimensional k g] (hrad : radical k g = ⊥) :
    (killingForm k g).Nondegenerate ∧ derivedSeries k g 1 = ⊤ := by
  let _ : HasTrivialRadical k g := ⟨hrad⟩
  let _ : HasCentralRadical k g := ⟨by
    apply le_antisymm
    · rw [hrad]
      exact bot_le
    · exact center_le_radical k g⟩
  refine ⟨HasTrivialRadical.killingForm_nondegenerate k g, ?_⟩
  let D := derivedSeries k g 1
  have hc := D.isCompl_killingCompl
  have hD : D.killingCompl ≤ center k g := by
    intro z hz
    apply (mem_maxTrivSubmodule k g g z).mpr
    intro x
    have hD' : D = ⁅(⊤ : LieIdeal k g), ⊤⁆ := by
      simp only [D, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero]
    have hx : ⁅x, z⁆ ∈ D := by
      rw [hD']
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) (LieSubmodule.mem_top z)
    have h : ⁅x, z⁆ ∈ D ⊓ D.killingCompl :=
      ⟨hx, lie_mem_right k g D.killingCompl x z hz⟩
    rw [hc.inf_eq_bot, LieSubmodule.mem_bot] at h
    exact h
  have hcenter : center k g = ⊥ := by
    apply le_antisymm
    · rw [← hrad]
      exact center_le_radical k g
    · exact bot_le
  have hDperp : D.killingCompl = ⊥ := le_bot_iff.mp (hD.trans hcenter.le)
  have htop := hc.sup_eq_top
  rw [hDperp, sup_bot_eq] at htop
  exact htop

end LieAlgebra
