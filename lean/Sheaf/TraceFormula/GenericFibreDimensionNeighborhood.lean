/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober
public import Mathlib.Topology.Irreducible
import Sheaf.AlgebraicGeometry.LocalFibreDimensionOpen
import WeilConjectures.AlgebraicGeometry.GenericFibreClosedAvoidance
import Sheaf.AlgebraicGeometry.GenericClosedSubsetFibreNonempty
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.Topology.DimensionSupremumLocalDimensions

/-!
# Generic fibre dimension persists on a nonempty open

Source: Stacks Project, More on Morphisms, Lemma Tag 05F7
(lemma-dimension-in-neighbourhood), statement and proof lines 8411--8432
(blueprint: lem-trf-generic-fibre-dimension-neighborhood).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- For a finite-type morphism over an irreducible scheme, the dimension of the generic
fibre is the dimension of every fibre on a nonempty open subset of the base.

Source: Stacks Project, More on Morphisms, Lemma Tag 05F7
(lemma-dimension-in-neighbourhood), statement and proof lines 8411--8432
(blueprint: lem-trf-generic-fibre-dimension-neighborhood).

Proof:
1. Let `Z` be the closed locus where the local fibre dimension is greater than `n`.
   Openness of the bounded local-fibre-dimension locus makes `Z` closed. The generic
   fibre has dimension `n`, so it is disjoint from `Z`. Finite type gives the locally
   finite type and quasi-compact hypotheses needed by the generic-fibre closed-avoidance
   lemma. Since the generic point is dense in the irreducible base, shrink to a nonempty
   open `V₁` on which all fibres avoid `Z`, and hence have dimension at most `n` by the
   supremum-of-local-dimensions theorem (`lem-weil-pbc-local-fibre-dimension-open`,
   `lem-sbc-generic-fibre-closed-avoidance`,
   `lem-weil-pbc-dimension-supremum-local-dimensions`).
2. If `n = 0`, the generic fibre is nonempty and the generic closed-subset spreading
   lemma applied to the whole source gives a nonempty open `V₂` on which every fibre is
   nonempty. If `n > 0`, use the closed locus where local fibre dimension is greater than
   `n - 1`. The supremum description of the generic fibre dimension shows that this locus
   meets the generic fibre, so the same spreading lemma gives a nonempty open `V₂` on
   which every fibre meets that locus (`lem-sbc-generic-closed-subset-fibre-nonempty`,
   `lem-weil-pbc-dimension-supremum-local-dimensions`).
3. On `V₁ ∩ V₂`, the upper bound from the first step and the lower bound from the second
   step give dimension exactly `n`, including the separate nonemptiness argument when
   `n = 0`.
-/
theorem exists_nonempty_open_fibre_dimension_eq_of_generic_fibre_dimension_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [IrreducibleSpace Y] (η : Y) (hη : IsGenericPoint η (Set.univ : Set Y))
    (n : ℕ) (hηdim : topologicalKrullDim (f.fiber η) = (n : WithBot ℕ∞)) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, topologicalKrullDim (f.fiber y) = (n : WithBot ℕ∞) := by
  sorry

end AlgebraicGeometry
