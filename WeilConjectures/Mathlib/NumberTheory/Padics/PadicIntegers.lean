/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Transcendental `p`-adic integers

## Main statements

- `PadicInt.exists_transcendental`: there is a `p`-adic integer which is transcendental over `ℤ`.
-/

@[expose] public section

open Cardinal

namespace PadicInt

variable (p : ℕ) [Fact p.Prime]

/-- There is a `p`-adic integer which is transcendental over `ℤ`: otherwise `ℤ_[p]`, and hence
its fraction field `ℚ_[p]`, would be countable, whereas `ℚ_[p]` has the cardinality of the
continuum. -/
theorem exists_transcendental : ∃ t : ℤ_[p], Transcendental ℤ t := by
  by_contra! h
  have : Algebra.IsAlgebraic ℤ ℤ_[p] := ⟨fun t ↦ not_not.mp (h t)⟩
  have hZ : #ℤ_[p] ≤ ℵ₀ := (Algebra.IsAlgebraic.cardinalMk_le_max ℤ ℤ_[p]).trans (by simp)
  have hQ : #ℚ_[p] ≤ ℵ₀ := by
    refine (mk_le_of_surjective (f := fun x : ℤ_[p] × ℤ_[p] ↦ (x.1 : ℚ_[p]) / x.2) ?_).trans ?_
    · intro z
      obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := ℤ_[p]) z
      exact ⟨(a, b), rfl⟩
    · simpa using mul_le_mul' hZ hZ
  exact (aleph0_lt_continuum.trans_le
    (continuum_le_cardinal_of_nontriviallyNormedField ℚ_[p])).not_ge hQ

end PadicInt
