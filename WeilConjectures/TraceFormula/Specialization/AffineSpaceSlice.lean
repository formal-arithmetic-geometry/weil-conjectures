/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSlice

/-!

# Coordinate generic slices of affine spaces over the trait

Let `k'` be a field, `S = Spec k'⟦t⟧`, and let `K` be a field over `k'` with an element `x`
(for the slices, `K = k'(x)^alg` with `x` transcendental: `AlgebraicGeometry.traitSliceField`
and `AlgebraicGeometry.traitSliceCoord`).
For a coordinate `i : Fin (n + 1)` of `𝔸ⁿ⁺¹_S`, the morphism `hᵢ : 𝔸ⁿ_{K⟦t⟧} ⟶ 𝔸ⁿ⁺¹_S`
(`AlgebraicGeometry.affineSpaceSlice`) over the trait map `Spec K⟦t⟧ ⟶ S` sends the `i`-th
coordinate to the constant `x` and the other coordinates to the coordinates of `𝔸ⁿ_{K⟦t⟧}` in
order. Mathematically (this is not formalised here), it identifies `𝔸ⁿ_{K⟦t⟧}` with the base
change `𝔸ⁿ⁺¹_S ×_{𝔸¹_S} Spec K⟦t⟧` of `𝔸ⁿ⁺¹_S` along the generic slice `Spec K⟦t⟧ ⟶ 𝔸¹_S` of
the `i`-th coordinate (`AlgebraicGeometry.traitSlice`), the completion of the strict localization
of `𝔸¹_S` at the generic point of its special fibre up to a purely inseparable extension of the
residue field.

On special fibres, `hᵢ` induces `hᵢ,ₛ : 𝔸ⁿ_K ⟶ 𝔸ⁿ⁺¹_{k'}`
(`AlgebraicGeometry.affineSpaceSliceSpecial`), the canonical morphism from the geometric generic
fibre `𝔸ⁿ⁺¹_{k'} ×_{𝔸¹_{k'}} Spec K` of the `i`-th coordinate projection. These are the slices
along which Deligne proves the finiteness of nearby cycles by induction on the relative dimension
(SGA 4½, [Th. finitude], proof of Thm. 3.2 and Lemme 3.3).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] {K : Type u} [Field K] [Algebra k' K] (n : ℕ) (i : Fin (n + 1))
  (x : K)

end AlgebraicGeometry
