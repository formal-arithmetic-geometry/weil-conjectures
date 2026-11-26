/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.Depth
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
import WeilConjectures.RingTheory.IsRegularOfDimensionDrop
import WeilConjectures.RingTheory.FlatOverRegular

/-!
# Miracle flatness

A local homomorphism from a regular local ring to a Cohen–Macaulay local ring is flat when the
target dimension is the source dimension plus the closed fibre dimension.

## Implementation details

A minimal generating list `x` of the source maximal ideal has length the source dimension. The
dimension formula says that quotienting by `x.map φ` drops the target dimension by its length,
so `x.map φ` is regular (Stacks 00N6), and flatness over regular parameters (Stacks 07DY)
applies.

## References

* [Stacks, Tag 00R4]
* [Stacks, Tags 00N6, 07DY]
-/

@[expose] public section

universe u v

namespace RingHom

/-- A local homomorphism from a regular Noetherian local ring to a Cohen–Macaulay
Noetherian local ring is flat when target dimension is source dimension plus closed
fibre dimension. The finite dimension `e` records Cohen–Macaulayness by the depth bound.
-/
theorem flat_of_regular_of_depth_ge {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    (φ : R →+* S) [IsLocalHom φ] (e : ℕ)
    (hdim : ringKrullDim S = (e : WithBot ℕ∞))
    (hdepth : (e : ℕ∞) ≤ IsLocalRing.depth (R := S) S)
    (hdim_add : ringKrullDim S =
      ringKrullDim R + ringKrullDim (S ⧸ (IsLocalRing.maximalIdeal R).map φ)) :
    φ.Flat := by
  classical
  obtain ⟨s, hs, hspan⟩ :=
    (IsNoetherian.noetherian (IsLocalRing.maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  let d := s.card
  let x := s.toList
  have hd : ringKrullDim R = (d : WithBot ℕ∞) := by
    rw [← IsRegularLocalRing.spanFinrank_maximalIdeal, ← hs]
  have hx : x.length = d := by simp [x, d]
  have hgen : Ideal.ofList x = IsLocalRing.maximalIdeal R := by
    simpa [x, Ideal.ofList] using hspan
  have hmap : Ideal.ofList (x.map φ) = (IsLocalRing.maximalIdeal R).map φ := by
    rw [← hgen, Ideal.map_ofList]
  have hmem : ∀ g ∈ x.map φ, g ∈ IsLocalRing.maximalIdeal S := by
    intro g hg
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hg
    exact map_nonunit φ r (hgen ▸ Ideal.subset_span hr)
  have hdrop : ringKrullDim (S ⧸ Ideal.ofList (x.map φ)) +
      ((x.map φ).length : WithBot ℕ∞) = (e : WithBot ℕ∞) := by
    rw [hmap, List.length_map, hx, ← hd, add_comm, ← hdim_add, hdim]
  have hreg := RingTheory.Sequence.isRegular_of_dimension_drop e hdim hdepth
    (x.map φ) hmem hdrop
  exact flat_of_regular_parameters φ d x hd hx hgen hreg

end RingHom
