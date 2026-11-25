/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.GlobalDimension
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.RingTheory.BoundedResolutionUnitEntryCancellation

/-! # One cancellation step for a bounded finite free resolution

A bounded finite free resolution over a Noetherian local ring which is not minimal admits one
cancellation that strictly decreases the sum of the ranks.

## Implementation details

A differential coefficient outside the maximal ideal is a unit, and
`ChainComplex.exists_splitting_of_isUnit_entry` splits off a contractible two-term complex. The
complement is again a resolution with the ranks in two degrees decreased by one. This is a
single cancellation, not the iteration or the assertion that the result is minimal.

## References

* [Stacks, Tag 00MT], as used in the proof of [Stacks, Tag 00OA]
-/
@[expose] public section
universe u v
open CategoryTheory CategoryTheory.Limits
namespace ModuleCat

/-- A nonminimal bounded finite free resolution admits one rank-decreasing cancellation.
The resulting resolution `P'` has finite free terms whose ranks sum to strictly less. -/
theorem bounded_resolution_cancellation_decreases_rank {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (M : ModuleCat.{max u v} R)
    (d : ℕ) (P : ProjectiveResolution M)
    (hzero : ∀ i : ℕ, d < i → IsZero (P.complex.X i))
    (hfree : ∀ i : ℕ, Module.Finite R (P.complex.X i) ∧ Module.Free R (P.complex.X i))
    (hnot : ¬ ∀ i : ℕ, i < d →
      LinearMap.range (P.complex.d (i + 1) i).hom ≤
        IsLocalRing.maximalIdeal R • (⊤ : Submodule R (P.complex.X i))) :
    ∃ P' : ProjectiveResolution M,
      (∀ i : ℕ, d < i → IsZero (P'.complex.X i)) ∧
      (∀ i : ℕ, Module.Finite R (P'.complex.X i) ∧ Module.Free R (P'.complex.X i)) ∧
      (∑ i : Fin (d + 1), Module.finrank R (P'.complex.X i.val)) <
        ∑ i : Fin (d + 1), Module.finrank R (P.complex.X i.val) := by
  classical
  have : ∀ i : ℕ, Module.Finite R (P.complex.X i) := fun i => (hfree i).1
  have : ∀ i : ℕ, Module.Free R (P.complex.X i) := fun i => (hfree i).2
  let b := fun i : ℕ => Module.finBasis R (P.complex.X i)
  obtain ⟨j, hjd, p, q, hu⟩ :
      ∃ j : ℕ, j < d ∧ ∃ (p : Fin (Module.finrank R (P.complex.X (j + 1))))
        (q : Fin (Module.finrank R (P.complex.X j))),
        IsUnit (LinearMap.toMatrix (b (j + 1)) (b j)
          (P.complex.d (j + 1) j).hom q p) := by
    by_contra h
    apply hnot
    intro j hjd x hx
    obtain ⟨y, rfl⟩ := hx
    rw [← (b (j + 1)).sum_repr y, map_sum]
    apply Submodule.sum_mem
    intro p hp
    rw [map_smul]
    apply Submodule.smul_mem
    rw [← (b j).sum_repr ((P.complex.d (j + 1) j).hom (b (j + 1) p))]
    apply Submodule.sum_mem
    intro q hq
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    have hc : LinearMap.toMatrix (b (j + 1)) (b j)
        (P.complex.d (j + 1) j).hom q p ∈ IsLocalRing.maximalIdeal R := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact h ⟨j, hjd, p, q, hu⟩
    simpa only [LinearMap.toMatrix_apply] using hc
  obtain ⟨P', hzero', hfree', hle, hlt⟩ :=
    exists_bounded_resolution_unit_entry_cancellation M d P hzero
      (fun i => Module.finrank R (P.complex.X i)) b j hjd p q hu
  refine ⟨P', hzero', hfree', ?_⟩
  apply Finset.sum_lt_sum (s := (Finset.univ : Finset (Fin (d + 1))))
  · intro i hi
    exact hle i
  · exact ⟨⟨j, by omega⟩, Finset.mem_univ _, hlt⟩

end ModuleCat
