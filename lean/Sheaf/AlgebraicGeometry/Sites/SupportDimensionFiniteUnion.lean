/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf
import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing
import WeilConjectures.AlgebraicGeometry.Sites.EtaleVanishingLocus
import Sheaf.AlgebraicGeometry.ClosedIrreducibleDimensionTrdeg

/-! The finite-union Krull dimension bound that the upstream sync to e9ba49ac4 removed from
`WeilConjectures.AlgebraicGeometry.Sites.SupportDimension` (where it was private); two
Sheaf modules use it. -/

@[expose] public section

universe u

namespace AlgebraicGeometry.Etale

/-- A finite union of closed sets of Krull dimension at most `a` has Krull dimension at most `a`. -/
theorem dim_finite_union_le {X : Type u} [TopologicalSpace X] [QuasiSober X]
    [T0Space X] {ι : Type*} (I : Finset ι) (C : ι → Set X)
    (hC : ∀ i ∈ I, IsClosed (C i)) (a : WithBot ℕ∞)
    (hCa : ∀ i ∈ I, topologicalKrullDim (C i) ≤ a) :
    topologicalKrullDim (⋃ i ∈ I, C i) ≤ a := by
  have : QuasiSober (⋃ i ∈ I, C i) :=
    (isClosed_biUnion_finset hC).isClosedEmbedding_subtypeVal.quasiSober
  let := specializationOrder (⋃ i ∈ I, C i)
  rw [topologicalKrullDim_eq_krullDim_specializationOrder, Order.krullDim_eq_iSup_height]
  refine iSup_le fun z ↦ ?_
  rw [← topologicalKrullDim_closure_singleton]
  obtain ⟨i, hi, hz⟩ := Set.mem_iUnion₂.mp z.property
  have hc : closure ({z} : Set (⋃ i ∈ I, C i)) ⊆ Subtype.val ⁻¹' C i :=
    closure_minimal (Set.singleton_subset_iff.mpr hz)
      ((hC i hi).preimage continuous_subtype_val)
  let f : closure ({z} : Set (⋃ i ∈ I, C i)) → C i :=
    fun x ↦ ⟨x.val.val, hc x.property⟩
  have hf : Topology.IsInducing f := by
    apply (Topology.IsInducing.subtypeVal :
      Topology.IsInducing (Subtype.val : C i → X)).of_comp_iff.mp
    change Topology.IsInducing (fun x : closure ({z} : Set (⋃ i ∈ I, C i)) ↦ x.val.val)
    exact Topology.IsInducing.subtypeVal.comp Topology.IsInducing.subtypeVal
  exact hf.topologicalKrullDim_le.trans (hCa i hi)

end AlgebraicGeometry.Etale
