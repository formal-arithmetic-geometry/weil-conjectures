/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Topology.Constructible
import WeilConjectures.Topology.ConstructibleIsRetrocompact
import Mathlib.Topology.Spectral.Prespectral

/-!
# Constructible intersections in a constructible subspace

## References

* Stacks Project, Tag 09YI.
-/

@[expose] public section

universe u

open Set TopologicalSpace

namespace Topology

/--
Let `X` be a topological space with a basis of quasi-compact open subsets, and let
`E` and `E'` be constructible subsets of `X`. Their intersection, regarded as a
subset of the subspace `E`, is constructible in `E`.
-/
theorem isConstructible_inter_subtype
    {X : Type u} [TopologicalSpace X]
    (hBasis : IsTopologicalBasis {U : Set X | IsOpen U ∧ IsCompact U})
    {E E' : Set X}
    (hE : IsConstructible E) (hE' : IsConstructible E') :
    IsConstructible ((Subtype.val : E → X) ⁻¹' E') := by
  let : PrespectralSpace X := ⟨hBasis⟩
  apply hE'.preimage continuous_subtype_val
  intro V hVo hVr W hWc hWo
  obtain ⟨O, hOo, hOW⟩ := IsEmbedding.subtypeVal.isInducing.isOpen_iff.mp hWo
  obtain ⟨U, hUc, hUo, hWU, hUO⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between
      (hWc.image continuous_subtype_val) hOo (by
        rintro _ ⟨x, hx, rfl⟩
        change x ∈ Subtype.val ⁻¹' O
        rwa [hOW])
  have hUW : (Subtype.val : E → X) ⁻¹' U = W := by
    apply Subset.antisymm
    · intro x hx
      rw [← hOW]
      exact hUO hx
    · intro x hx
      exact hWU ⟨x, hx, rfl⟩
  rw [← hUW, ← preimage_inter, IsEmbedding.subtypeVal.isCompact_iff]
  simpa only [Subtype.image_preimage_coe, inter_comm] using
    hE.isRetrocompact (hVr hUc hUo) (hVo.inter hUo)

end Topology
