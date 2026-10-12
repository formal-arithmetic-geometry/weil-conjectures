/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# A projective coordinate complement is finite

Let `p : Y ⟶ S` be proper over an integral locally noetherian scheme, covered by finitely many
opens `Y_α`, each embedded as a closed subscheme of an affine space `𝔸^{σ_α}_S`. Choose for every
coordinate `t_{α r} : Y_α ⟶ 𝔸¹_S` a nonempty (equivalently, dense) open `V_{α r} ⊆ 𝔸¹_S`. Over a
nonempty open of `S`, the complement `Z` of the union of the `t_{α r}⁻¹ V_{α r}` is finite over
`S`. This is the first step of Deligne's generic constructibility theorem
(`thm-fin-deligne-generic-open`).

## Main statements

- `AlgebraicGeometry.exists_isFinite_morphismRestrict_of_range_subset`
  (`lem-fin-projective-coordinate-boundary`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- Blueprint `lem-fin-projective-coordinate-boundary`: A projective coordinate complement is
finite.

Let `S` be integral and locally noetherian (the blueprint takes `S = Spec A` affine) and let
`p : Y ⟶ S` be proper (the blueprint takes `p` projective). Let `Y = ⋃_α Y_α` be a finite open
cover with closed immersions `e_α : Y_α ⟶ 𝔸^{σ_α}_S` over `S`, and for each coordinate
`t_{α r} : Y_α ⟶ 𝔸¹_S` let `V_{α r} ⊆ 𝔸¹_S` be a nonempty open. Then there is a nonempty open
`W ⊆ S` over which every closed subscheme `Z` of `Y` supported in the complement of
`⋃_{α, r} t_{α r}⁻¹(V_{α r})` (for instance the reduced one) is finite over `W`. -/
theorem exists_isFinite_morphismRestrict_of_range_subset {S Y : Scheme.{u}} [IsIntegral S]
    [IsLocallyNoetherian S] (p : Y ⟶ S) [IsProper p] {ι : Type u} [Finite ι]
    (U : ι → Y.Opens) (hU : ⨆ α, U α = ⊤) (σ : ι → Type u) [∀ α, Finite (σ α)]
    (e : ∀ α, (U α).toScheme ⟶ 𝔸(σ α; S)) [∀ α, IsClosedImmersion (e α)]
    (he : ∀ α, e α ≫ 𝔸(σ α; S) ↘ S = (U α).ι ≫ p)
    (V : ∀ α, σ α → 𝔸(PUnit; S).Opens) (hV : ∀ α r, (V α r : Set 𝔸(PUnit; S)).Nonempty) :
    ∃ W : S.Opens, (W : Set S).Nonempty ∧
      ∀ (Z : Scheme.{u}) (i : Z ⟶ Y) [IsClosedImmersion i],
        Set.range i ⊆ (⋃ (α : ι) (r : σ α), (U α).ι ''
          ((e α ≫ AffineSpace.reindex (fun _ : PUnit ↦ r) S) ⁻¹' (V α r : Set 𝔸(PUnit; S))))ᶜ →
        IsFinite ((i ≫ p) ∣_ W) :=
  sorry

end AlgebraicGeometry
