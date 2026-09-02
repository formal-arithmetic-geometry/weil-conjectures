/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Topology.Sets.Opens
public import WeilConjectures.Mathlib.Topology.LocallyClosed
public import WeilConjectures.Topology.Stratification.Basic

/-!
# The interiors of the strata of a stratification are dense

For a finite stratification `(Xᵢ)` of a topological space `X`, the union of the interiors of
the strata is dense (`Topology.Stratification.dense_iUnion_interior_stratum`): its complement
lies in the union of the nowhere dense sets `Xᵢ \ interior Xᵢ`, see
`dense_iUnion_interior_of_isLocallyClosed`. No Noetherian hypothesis is needed. Disjointness
of the strata plays no role.

`Topology.Stratification.iSupInteriorStratum` packages this union as an open subset of `X`.
-/

@[expose] public section

open TopologicalSpace

namespace Topology.Stratification

variable {X : Type*} [TopologicalSpace X] (S : Stratification X)

/-- **The union of the interiors of the strata of a stratification is dense**: its complement
is contained in the union of the nowhere dense sets `Xᵢ \ interior Xᵢ`. -/
theorem dense_iUnion_interior_stratum : Dense (⋃ i, interior (S.stratum i)) :=
  dense_iUnion_interior_of_isLocallyClosed S.isLocallyClosed_stratum S.iUnion_stratum_eq_univ

/-- The interior of a stratum, as an open subset of `X`. -/
def interiorStratum (i : Fin S.n) : Opens X :=
  ⟨interior (S.stratum i), isOpen_interior⟩

/-- The union of the interiors of the strata, as an open subset of `X`. -/
def iSupInteriorStratum : Opens X :=
  ⨆ i, S.interiorStratum i

@[simp]
lemma coe_iSupInteriorStratum :
    (S.iSupInteriorStratum : Set X) = ⋃ i, interior (S.stratum i) := by
  rw [iSupInteriorStratum, Opens.coe_iSup]
  rfl

/-- The union of the interiors of the strata is dense. -/
lemma dense_iSupInteriorStratum : Dense (S.iSupInteriorStratum : Set X) := by
  rw [coe_iSupInteriorStratum]
  exact S.dense_iUnion_interior_stratum

end Topology.Stratification
