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
import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.FlatFibreDimensionNearZeroDimensionalStalk

/-! # Fibrewise dense constant dimension opens

## References

* [Stacks Project, Tag 054T](https://stacks.math.columbia.edu/tag/054T)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

private theorem ringKrullDim_stalk_eq_zero_of_generic (Y : Scheme.{u})
    (z : Y) (hz : z ∈ genericPoints Y) :
    ringKrullDim (Y.presheaf.stalk z) = (0 : WithBot ℕ∞) := by
  let : PartialOrder Y := specializationOrder Y
  have hmax : IsMax z := by
    intro y hzy
    change y ⤳ z at hzy
    have hsub := hz.2 isIrreducible_singleton.closure hzy.closure_subset
    change z ⤳ y
    exact specializes_iff_closure_subset.mpr hsub
  rw [ringKrullDim_stalk_eq_coheight, Order.IsMax.coheight_eq_zero hmax]
  rfl

/-- Fibrewise dense constant dimension opens (Stacks, Tags 054T and 054U). -/
theorem exists_fibre_dimension_opens_of_flat_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)] :
    ∃ V : ℕ → X.Opens,
      (∀ t : T, t ∈ U → Dense {z : f.fiber t | ∃ n : ℕ, f.fiberι t z ∈ V n}) ∧
      (∀ (n : ℕ) (x : X), x ∈ V n →
        topologicalKrullDimAt (f.asFiber x) = (n : WithBot ℕ∞)) := by
  let V : ℕ → X.Opens := fun n =>
    ⟨interior {x : X | f x ∈ U ∧
      topologicalKrullDimAt (f.asFiber x) = (n : WithBot ℕ∞)}, isOpen_interior⟩
  refine ⟨V, ?_, ?_⟩
  · intro t ht
    have hdense : Dense (genericPoints (f.fiber t)) :=
      dense_iff_closure_eq.mpr genericPoints.closure
    refine hdense.mono ?_
    intro z hz
    have hzt : f (f.fiberι t z) = t := by
      have h := (f.fiberHomeo t z).property
      simpa using h
    generalize hx : f.fiberι t z = x at hzt ⊢
    subst t
    have hz' : f.asFiber x = z := by
      apply (f.fiberι _).isEmbedding.injective
      simpa using hx.symm
    have hdim := ringKrullDim_stalk_eq_zero_of_generic _ z hz
    rw [← hz'] at hdim
    obtain ⟨n, W, hzW, hW⟩ :=
      exists_constant_fibre_dimension_neighbourhood_of_stalk_dimension_zero f U
        x ht hdim
    refine ⟨n, ?_⟩
    rw [hx]
    exact W.isOpen.subset_interior_iff.mpr hW hzW
  · intro n x hx
    exact (interior_subset hx).2

end AlgebraicGeometry
