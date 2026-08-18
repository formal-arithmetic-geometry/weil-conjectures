/-
Copyright (c) 2026 Tingxiao Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tingxiao Shi
-/
module

public import Mathlib.Dynamics.PeriodicPts.Defs

@[expose] public section

/-!
# Complements on periodic orbits

Mathlib defines the orbit of a periodic point `x` of a self-map `f : α → α` as the cycle
`Function.periodicOrbit f x`, and characterises its members as the iterates `f^[j] x`. What
is missing is the recognition principle in the other direction: two points carry the same
periodic orbit exactly when one lies on the orbit of the other.

## Main results

- `Function.mem_periodicOrbit_iff_exists_lt_minimalPeriod` — the members of `periodicOrbit f x`
  are the iterates `f^[j] x` with `j < minimalPeriod f x`, with no periodicity hypothesis.
- `Function.periodicOrbit_eq_iff_mem_periodicOrbit` — periodic orbits are equal or disjoint.
- `Function.IsPeriodicPt.of_mem_periodicOrbit` — being of period `n` is an orbit invariant.
- `Function.ptsOfPeriod_subset_of_dvd` — the sets of points of period `n` are monotone
  along divisibility.
-/

namespace Function

variable {α : Type*} {f : α → α} {m n : ℕ} {x y : α}

/-- Points of period `m` are points of period `n` whenever `m ∣ n`.
(blueprint: `lemma:weil-frobenius-fixed-point-set-monotone`) -/
theorem ptsOfPeriod_subset_of_dvd (f : α → α) (h : m ∣ n) :
    ptsOfPeriod f m ⊆ ptsOfPeriod f n := fun _ hx ↦
  isPeriodicPt_iff_minimalPeriod_dvd.mpr ((isPeriodicPt_iff_minimalPeriod_dvd.mp hx).trans h)

/-- The members of `periodicOrbit f x` are exactly the iterates `f^[j] x` for
`j < minimalPeriod f x`. No periodicity hypothesis is needed: for a non-periodic `x` both
sides are false. (blueprint: `lemma:weil-frobenius-orbit-members`) -/
theorem mem_periodicOrbit_iff_exists_lt_minimalPeriod :
    y ∈ periodicOrbit f x ↔ ∃ j < minimalPeriod f x, f^[j] x = y := by
  simp [periodicOrbit, Cycle.mem_coe_iff, List.mem_map, List.mem_range]

/-- Two points carry the same periodic orbit exactly when one lies on the orbit of the other;
in particular distinct periodic orbits are disjoint.
(blueprint: `lemma:weil-frobenius-orbits-equal-or-disjoint`) -/
theorem periodicOrbit_eq_iff_mem_periodicOrbit (hx : x ∈ periodicPts f) :
    periodicOrbit f y = periodicOrbit f x ↔ y ∈ periodicOrbit f x := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_cases hy : y ∈ periodicPts f
    · exact h ▸ self_mem_periodicOrbit hy
    · rw [periodicOrbit_eq_nil_of_not_periodic_pt hy] at h
      exact absurd (periodicOrbit_eq_nil_iff_not_periodic_pt.mp h.symm) (not_not.mpr hx)
  · obtain ⟨j, -, rfl⟩ := mem_periodicOrbit_iff_exists_lt_minimalPeriod.mp h
    exact periodicOrbit_apply_iterate_eq hx j

/-- Having period `n` is an invariant of the periodic orbit.
(blueprint: `lemma:weil-frobenius-orbit-period-invariant`) -/
theorem IsPeriodicPt.of_mem_periodicOrbit (hx : IsPeriodicPt f n x)
    (hy : y ∈ periodicOrbit f x) : IsPeriodicPt f n y := by
  obtain ⟨j, -, rfl⟩ := mem_periodicOrbit_iff_exists_lt_minimalPeriod.mp hy
  exact hx.apply_iterate j

end Function
