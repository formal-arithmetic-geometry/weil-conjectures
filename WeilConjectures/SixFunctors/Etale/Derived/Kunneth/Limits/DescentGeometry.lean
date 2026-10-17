/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleLimitDescent
public import Mathlib.CategoryTheory.Filtered.Final

/-!
# Descent of pointed étale neighbourhoods along a limit of schemes

Let `X = lim Xᵢ` be a cofiltered limit of quasi-compact quasi-separated schemes with affine
transition maps, with projections `pᵢ : X ⟶ Xᵢ`, and let `x̄ : Spec Ω ⟶ X` be a point.

- `AlgebraicGeometry.exists_etale_descent_of_isLimit`: every pointed étale neighbourhood
  `(W, w)` of `x̄` is refined by the base change `(V ×_{Xᵢ} X, (v, x̄))` of a pointed étale
  neighbourhood `(V, v)` of `pᵢ x̄` at some stage.
- `AlgebraicGeometry.exists_etale_hom_descent_of_isLimit`: given moreover a morphism
  `φ : W ⟶ V ×_{Xᵢ} X` over `X`, the pointed neighbourhood `(W, w)` is refined by the base
  change of a pointed étale neighbourhood `(V', v')` of `pⱼ x̄` at a later stage `j ⟶ i`, in
  such a way that the composite with `φ` comes from a morphism `V' ⟶ V ×_{Xᵢ} Xⱼ` over `Xⱼ`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A pointed scheme `(W, w)` over `S` has an affine open neighbourhood `W'` of `w` mapping into
an affine open `N` of `S`. -/
lemma exists_isAffineOpen_range_subset {Ω : Type u} [Field Ω] {S W : Scheme.{u}} (a : W ⟶ S)
    (w : Spec (.of Ω) ⟶ W) :
    ∃ (W' : W.Opens) (N : S.Opens), IsAffineOpen W' ∧ IsAffineOpen N ∧
      Set.range (W'.ι ≫ a) ⊆ (N : Set S) ∧ Set.range w ⊆ (W' : Set W) := by
  let p : Spec (.of Ω) := default
  obtain ⟨N, hN, hpN, -⟩ := exists_isAffineOpen_mem_and_subset (x := a (w p))
    (U := ⊤) trivial
  obtain ⟨W', hW', hpW', hsub⟩ := exists_isAffineOpen_mem_and_subset (x := w p)
    (U := a ⁻¹ᵁ N) hpN
  refine ⟨W', N, hW', hN, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    refine hsub ?_
    rw [← Scheme.Opens.range_ι]
    exact ⟨y, rfl⟩
  · rintro _ ⟨y, rfl⟩
    rwa [Subsingleton.elim y p]

end AlgebraicGeometry
