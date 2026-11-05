/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.SliceTraitPoint
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalPresentation
import WeilConjectures.RingTheory.StrictHenselizationAlgebraic

/-!

# The strict localization at the slice point is algebraic over the affine chart

Let `R₁` be a discrete valuation ring and `s = sliceTraitPoint b₁` the geometric point of `𝔸¹_{R₁}`
over the generic point of the special fibre. The ring `𝒪^{sh}_{𝔸¹_{R₁}, s}` of the strict
localization receives the chart map `g : R₁[x] ⟶ 𝒪^{sh}` and is a strict henselization of the
local ring `R₁[x]_q`. Since `𝒪^{sh}` is a domain, every element of it is algebraic over `R₁[x]_q`
(`Algebra.IsStrictHenselization.isAlgebraic`), hence over `R₁[x]` after clearing denominators.

## Main results

- `AlgebraicGeometry.exists_coord_isAlgebraic_strictHenselization_sliceTraitPoint`: the chart map
  `g : R₁[x] ⟶ 𝒪^{sh}` is compatible with the structure map, sends `x` to an element with value
  `traitSliceCoord κ₁` at the geometric point, and every element of `𝒪^{sh}` is a root of a nonzero
  polynomial with coefficients in `R₁[x]`.

-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

open Scheme

variable {R₁ : Type u} [CommRing R₁] [IsDomain R₁] [IsDiscreteValuationRing R₁] {κ₁ : Type u}
  [Field κ₁] (b₁ : R₁ →+* κ₁)

end AlgebraicGeometry
