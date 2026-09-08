/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Finite products of proper schemes, and dense proper open subschemes

## Finite products

A finite product of proper `S`-schemes is proper over `S`
(`AlgebraicGeometry.isProper_pi_hom`). This is an instance of the general fact that the
structure morphism of a finite product in an over category satisfies any multiplicative
morphism property that is stable under base change.

## Dense proper open subschemes

An open subscheme `V` of a scheme `Z` that is topologically dense in a larger open `W` and
whose inclusion into `W` is universally closed is all of `W`
(`AlgebraicGeometry.Scheme.Opens.eq_of_universallyClosed_of_dense`). Since properness of a
composite `V ⟶ W ⟶ T` with `W ⟶ T` separated forces the inclusion `V ⟶ W` to be
universally closed, this gives the form used in practice,
`AlgebraicGeometry.Scheme.Opens.eq_of_isProper_of_dense`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The structure morphism of a finite product of proper `S`-schemes is proper. -/
theorem isProper_pi_hom {S : Scheme.{u}} {ι : Type*} [Finite ι] (F : ι → Over S)
    [HasProduct F] [∀ i, IsProper (F i).hom] : IsProper (∏ᶜ F).hom :=
  MorphismProperty.pi_hom _ F fun _ ↦ inferInstance

variable {Z T : Scheme.{u}}

/-- If `V ≤ W` are opens of a scheme `Z` such that the inclusion `V ⟶ W` is universally
closed and `V` is topologically dense in `W`, then `V = W`. -/
theorem Scheme.Opens.eq_of_universallyClosed_of_dense {V W : Z.Opens} (h : V ≤ W)
    [UniversallyClosed (Z.homOfLE h)] (hd : (W : Set Z) ⊆ closure (V : Set Z)) :
    V = W := by
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
  rw [hrange] at hx'
  exact hx'

/-- An open subscheme `V ≤ W` that is proper over a base `T` over which `W` is separated and
that is topologically dense in `W` is all of `W`. -/
theorem Scheme.Opens.eq_of_isProper_of_dense {V W : Z.Opens} (h : V ≤ W) (q : W.toScheme ⟶ T)
    [IsProper (Z.homOfLE h ≫ q)] [IsSeparated q]
    (hd : (W : Set Z) ⊆ closure (V : Set Z)) :
    V = W :=
  have : UniversallyClosed (Z.homOfLE h) :=
    UniversallyClosed.of_comp_of_isSeparated (f := Z.homOfLE h) (g := q)
  eq_of_universallyClosed_of_dense h hd

end AlgebraicGeometry
