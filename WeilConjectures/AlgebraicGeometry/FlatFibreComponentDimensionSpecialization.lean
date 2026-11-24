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

import WeilConjectures.AlgebraicGeometry.FlatFibreDimensionStrata

/-! # FlatFibreComponentDimensionSpecialization

## References

* [Stacks Project, Tag 054U](https://stacks.math.columbia.edu/tag/054U)
-/

@[expose] public section

universe u
open CategoryTheory Topology
namespace AlgebraicGeometry

/-- A component point admits a neighbourhood on which the fibre dimension is constant
(Stacks, Tag 054T). -/
theorem exists_fibre_dimension_open_of_flat_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    (x : X) (hx : f x ∈ U)
    (hcomponent : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    ∃ V : X.Opens, x ∈ V ∧
      ∀ y ∈ V, topologicalKrullDimAt (f.asFiber y) =
        topologicalKrullDimAt (f.asFiber x) := by
  obtain ⟨V, hcover, hdim⟩ := exists_fibre_dimension_strata_of_flat_restrict f U
  obtain ⟨n, hxn⟩ := hcover x hx hcomponent
  refine ⟨V n, hxn, ?_⟩
  intro y hy
  exact (hdim n y hy).trans (hdim n x hxn).symm

/-- Local fibre dimension is constant along a generalization of a fibre component point
(Stacks, Tag 054U). -/
theorem fibre_dimension_eq_of_specializes_component_restrict
    {X T : Scheme.{u}} (f : X ⟶ T) (U : T.Opens)
    [Flat (f ∣_ U)] [LocallyOfFinitePresentation (f ∣_ U)]
    (x x' : X) (hx : f x ∈ U) (hsp : x' ⤳ x)
    (hcomponent : f.asFiber x ∈ genericPoints (f.fiber (f x))) :
    topologicalKrullDimAt (f.asFiber x') = topologicalKrullDimAt (f.asFiber x) := by
  obtain ⟨V, hxV, hV⟩ := exists_fibre_dimension_open_of_flat_restrict
    f U x hx hcomponent
  exact hV x' (hsp.mem_open V.isOpen hxV)

end AlgebraicGeometry
