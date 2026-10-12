/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Length

/-!
# Filtrations with simple quotients of finite-length modules

A module of finite length `Module.length R M < ⊤` admits a finite chain of submodules
`0 = M₀ < M₁ < ⋯ < M_r = M` whose successive quotients `M_i / M_{i-1}` are simple. This is a
restatement of `isFiniteLength_iff_exists_compositionSeries` together with
`covBy_iff_quot_is_simple`.
-/

@[expose] public section

namespace Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **A finite-length module has a filtration with simple quotients.** If
`Module.length R M < ⊤`, there are `r : ℕ` and submodules `0 = N 0 < N 1 < ⋯ < N r = M` such
that each quotient `N (i + 1) / N i` (realised as `N (i + 1) ⧸ (N i).comap (N (i + 1)).subtype`)
is a simple module. This follows from the existence of a composition series
(`isFiniteLength_iff_exists_compositionSeries`) and `covBy_iff_quot_is_simple`.
(blueprint: `lem-weil-pbc-finite-length-module-simple-filtration`) -/
theorem exists_simple_filtration_of_length_lt_top (h : Module.length R M < ⊤) :
    ∃ (r : ℕ) (N : Fin (r + 1) → Submodule R M), N 0 = ⊥ ∧ N (Fin.last r) = ⊤ ∧
      ∀ i : Fin r, N i.castSucc < N i.succ ∧
        IsSimpleModule R (N i.succ ⧸ (N i.castSucc).comap (N i.succ).subtype) := by
  obtain ⟨s, hs₁, hs₂⟩ :=
    isFiniteLength_iff_exists_compositionSeries.mp (length_ne_top_iff.mp h.ne)
  refine ⟨s.length, s.toFun, hs₁, hs₂, fun i ↦ ⟨(s.step i).lt, ?_⟩⟩
  exact (covBy_iff_quot_is_simple (s.step i).le).mp (s.step i)

end Module
