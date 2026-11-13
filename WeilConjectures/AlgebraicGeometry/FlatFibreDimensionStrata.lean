/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.FlatFibreDimensionStrataCore
import WeilConjectures.AlgebraicGeometry.FlatFibreDimensionStrataCover

/-! # Constant relative dimension opens for a flat finitely presented morphism

## References

* Stacks Project, Tags 054T and 054U
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A flat locally finitely presented map over an open admits constant-dimension
opens covering every generic point of every fibre component over that open
(Stacks, Tags 054T and 054U). -/
theorem exists_fibre_dimension_strata_of_flat_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)] :
    ∃ V : ℕ → X.Opens,
      (∀ x : X, f x ∈ U →
        f.asFiber x ∈ genericPoints (f.fiber (f x)) → ∃ n : ℕ, x ∈ V n) ∧
      (∀ (n : ℕ) (x : X), x ∈ V n →
        topologicalKrullDimAt (f.asFiber x) = (n : WithBot ℕ∞)) := by
  obtain ⟨V, hdense, hdim⟩ := exists_fibre_dimension_opens_of_flat_restrict f U
  refine ⟨V, ?_, hdim⟩
  intro x hx hcomponent
  have hopen : IsOpen {z : f.fiber (f x) | ∃ n : ℕ, f.fiberι (f x) z ∈ V n} := by
    have heq : {z : f.fiber (f x) | ∃ n : ℕ, f.fiberι (f x) z ∈ V n} =
        ⋃ n : ℕ, (f.fiberι (f x)) ⁻¹' (V n : Set X) := by
      ext z
      simp
    rw [heq]
    exact isOpen_iUnion fun n ↦ (V n).isOpen.preimage (f.fiberι (f x)).continuous
  obtain ⟨n, hn⟩ := generic_points_mem_dense_open_fibre_of_flat_restrict
    f U (f x) hx _ hopen (hdense (f x) hx) hcomponent
  exact ⟨n, by simpa only [Scheme.Hom.fiberι_asFiber] using hn⟩

end AlgebraicGeometry
