/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Properties

/-!
# Shrinking the base of a pair of quasi-compact opens

If `U ≤ V` are opens of a scheme `X` with `U` quasi-compact, a quasi-compact subset of `X`
disjoint from `closure (V ∖ U)` is contained in a quasi-compact open which meets `V` exactly
in `U`. This is the second opening reduction of Conrad's Theorem 2.4, Case 3 (blueprint:
`lemma:nagata-conrad-case3-smaller-base`).

The underlying topology is that the carrier of a scheme is a prespectral space, so a
quasi-compact subset of an open subset is contained in a quasi-compact open subset of it
(`PrespectralSpace.exists_isCompact_and_isOpen_between`).

## Main results

* `AlgebraicGeometry.exists_isCompact_opens_inf_eq_of_disjoint_closure_sdiff`: the
  quasi-compact open meeting `V` in `U`.

-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- **A quasi-compact open meeting `V` exactly in `U`.** If `U ≤ V` are opens of a scheme
`X` with `U` quasi-compact and `S` is a quasi-compact subset of `X` disjoint from
`closure (V ∖ U)`, then there is a quasi-compact open `X₀` containing `S` and `U` with
`X₀ ⊓ V = U`.
(Blueprint: `lemma:nagata-conrad-case3-smaller-base`.) -/
theorem exists_isCompact_opens_inf_eq_of_disjoint_closure_sdiff
    {X : Scheme.{u}} {U V : X.Opens} (hUV : U ≤ V) (hU : IsCompact (U : Set X))
    {S : Set X} (hS : IsCompact S)
    (hS' : Disjoint S (closure ((V : Set X) \ (U : Set X)))) :
    ∃ X₀ : X.Opens, IsCompact (X₀ : Set X) ∧ S ⊆ (X₀ : Set X) ∧ U ≤ X₀ ∧ X₀ ⊓ V = U := by
  -- `V ∖ U` is closed in `V`, so its closure misses `U`
  have hcl : closure ((V : Set X) \ (U : Set X)) ⊆ (U : Set X)ᶜ :=
    closure_minimal (fun _ hx ↦ hx.2) U.isOpen.isClosed_compl
  have hUW : (U : Set X) ⊆ (closure ((V : Set X) \ (U : Set X)))ᶜ := fun x hx hx' ↦ hcl hx' hx
  obtain ⟨W, hWc, hWo, hSW, hWU⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between (hS.union hU)
      isClosed_closure.isOpen_compl
      (Set.union_subset hS'.subset_compl_right hUW)
  refine ⟨⟨W, hWo⟩, hWc, Set.subset_union_left.trans hSW, fun x hx ↦ hSW (Or.inr hx), ?_⟩
  refine TopologicalSpace.Opens.ext (Set.Subset.antisymm ?_ ?_)
  · rintro x ⟨hxW, hxV⟩
    by_contra hxU
    exact hWU hxW (subset_closure ⟨hxV, hxU⟩)
  · exact fun x hx ↦ ⟨hSW (Or.inr hx), hUV hx⟩

end AlgebraicGeometry

