/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Dense universally closed open subschemes

An open subscheme `V` of a scheme `Z` that is topologically dense in a larger open `W` and
whose inclusion into `W` is universally closed is all of `W`
(`AlgebraicGeometry.Scheme.Opens.eq_of_universallyClosed_of_dense`).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable {Z : Scheme.{u}}

/-- If `V ≤ W` are opens of a scheme `Z` such that the inclusion `V ⟶ W` is universally
closed and `V` is topologically dense in `W`, then `V = W`. -/
theorem Scheme.Opens.eq_of_universallyClosed_of_dense {V W : Z.Opens} (h : V ≤ W)
    [UniversallyClosed (Z.homOfLE h)] (hd : (W : Set Z) ⊆ closure (V : Set Z)) :
    V = W := by
  -- a universally closed morphism is closed, so its dense range is everything
  have hrange : Set.range (Z.homOfLE h).base = W.ι.base ⁻¹' (V : Set Z) := by
    rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
    rfl
  have hdr : DenseRange (Z.homOfLE h).base := by
    rw [DenseRange, dense_iff_closure_eq, ← Set.univ_subset_iff, hrange,
      ← W.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage W.ι.continuous]
    exact fun x _ ↦ hd x.2
  have : IsDominant (Z.homOfLE h) := ⟨hdr⟩
  refine le_antisymm h fun x hx ↦ ?_
  obtain ⟨y, hy⟩ := (Z.homOfLE h).surjective ⟨x, hx⟩
  have hx' : (⟨x, hx⟩ : W.toScheme) ∈ Set.range (Z.homOfLE h).base := ⟨y, hy⟩
  rwa [hrange] at hx'

end AlgebraicGeometry
