/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import WeilConjectures.TraceFormula.Specialization.NearbyKunnethGlobal
public import WeilConjectures.TraceFormula.Specialization.SliceSupport
public import WeilConjectures.TraceFormula.Specialization.TraitSlice

/-!

# The generic slices of the finite-support step of Gabber's Künneth formula

Let `S = Spec k'⟦t⟧` and let `K = k'(x)^alg` (`AlgebraicGeometry.traitSliceField`), with
`x = X ∈ k'(X)` transcendental (`AlgebraicGeometry.traitSliceCoord`). For a model `M` over `S` with
a coordinate `b : 𝒳 ⟶ 𝔸¹_S`, the special fibre `b_s : 𝒳_s ⟶ 𝔸¹_{k'}` of `b`
(`ProEtale.CondensedRing.NearbyCyclesModel.specialCoordinate`) and the generic slice
`σ : Spec K⟦t⟧ ⟶ 𝔸¹_S` (`AlgebraicGeometry.traitSlice`), every point of `𝒳_s` lying over the
generic point of the special-fibre line `𝔸¹_{k'}` is in the image of the special fibre
`(𝒳 ×_{𝔸¹_S} Spec K⟦t⟧)_s ⟶ 𝒳_s` of the slice
(`NearbyCyclesModel.mem_range_sliceSpecialMap`). This is how the vanishing of the cone of the
Künneth map over the slices is turned into its vanishing over the generic point of the coordinate
line (blueprint `sk-prop-tf-nearby-external-kunneth`, "Finite support").

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k' : Type u) [Field k']

namespace ProEtale.CondensedRing.NearbyCyclesModel

variable {k'} {K : Type u} [Field K] [Algebra k' K]
  {X : Scheme.{u}} {X' : Over (Spec (.of k'))} {M : NearbyCyclesModel X X'.left}
  {q : M.total ⟶ trait k'} {g : M.generic ⟶ Spec (.of (traitGenericField k'))}

end ProEtale.CondensedRing.NearbyCyclesModel

end AlgebraicGeometry
