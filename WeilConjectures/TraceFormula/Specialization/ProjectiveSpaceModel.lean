/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.AffineSpaceSliceModel
public import WeilConjectures.TraceFormula.Specialization.AffineSpaceSliceCartesian
public import WeilConjectures.Compactification.AffineCharts
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.BasicCharts
public import WeilConjectures.SixFunctors.NearbyCycles.TraitChangeInduction.Coordinates

/-!

# The standard model of `ℙⁿ` over the trait and its affine charts

Let `S = Spec k'⟦t⟧`. The standard model of the relative projective space `P = ℙⁿ_S`
(`NearbyCyclesModel.projectiveSpaceModel`) is a proper model over the trait. Its affine charts
`eₐ : 𝔸ⁿ_S ⟶ ℙⁿ_S` (`AlgebraicGeometry.AffineSpace.toRelativeProjectiveSpaceChart`) are open
immersions over `S`, hence morphisms of geometric models from the standard model of `𝔸ⁿ_S`
(`NearbyCyclesModel.projectiveSpaceChartHom`), with maps of special fibres
`eₐ,ₛ : 𝔸ⁿ_{k'} ⟶ ℙⁿ_{k'}` (`NearbyCyclesModel.projectiveSpaceChartSpecial`).

Every non-closed point of the special fibre `ℙⁿ⁺¹_{k'}` is the image, under a chart `eₐ,ₛ`, of a
point of a coordinate generic slice `hᵢ,ₛ : 𝔸ⁿ_K ⟶ 𝔸ⁿ⁺¹_{k'}` (`K = k'(x)^alg`,
`NearbyCyclesModel.affineSpaceSliceSpecialFibre`)
(`NearbyCyclesModel.exists_projectiveSpaceChartSpecial_affineSpaceSliceSpecialFibre_eq`): the
charts cover `ℙⁿ⁺¹`, a non-closed point of `ℙⁿ⁺¹_{k'}` has a non-closed preimage in a chart, a
non-closed point of `𝔸ⁿ⁺¹_{k'}` has a coordinate sending it to the generic point of `𝔸¹_{k'}`
(`AlgebraicGeometry.AffineSpace.exists_isGenericPoint_reindex_of_not_isClosed`), and the
coordinate generic slice is the base change of that coordinate along the generic point
(`AlgebraicGeometry.isPullback_affineSpaceSlice`).

These are the charts and slices of the global step of Deligne's proof of the finiteness of nearby
cycles (SGA 4½, [Th. finitude], proof of 3.2).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel

variable (k' : Type u) [Field k']

end NearbyCyclesModel

end AlgebraicGeometry.ProEtale.CondensedRing
