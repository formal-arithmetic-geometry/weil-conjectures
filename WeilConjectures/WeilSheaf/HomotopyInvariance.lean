/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.HomotopyInvariance.Lisse
public import WeilConjectures.WeilSheaf.HomotopyInvariance.Restriction

/-!
# Homotopy invariance for Weil complexes along trivial line bundles

Let `π : Y ≅ Z ×_{k₀} 𝔸¹ ⟶ Z` be the trivial line bundle over a `k₀`-scheme `Z` of finite type.
The unit `K ⟶ Rπ_* π^* K` of `π^* ⊣ Rπ_*` is an isomorphism for every Weil complex `K` on `Z`
(blueprint `lem-pur-a1-direct-image`, extended to all Weil complexes). This file proves it for
reduced `Z` by Noetherian induction on the closed subsets of an ambient scheme `X` containing
`Z` as a closed subscheme
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_of_isClosedImmersion_of_isReduced`); the general
case,
`AlgebraicGeometry.WeilComplex.isIso_upperStarDerivedLowerStarAdjunction_unit_app_of_isPullback`
in `WeilConjectures.WeilSheaf.AffineLineBundle`, follows by passing to the reduced subscheme.

For the induction step, `K` has lisse cohomology sheaves on a dense open subscheme `j : U ⟶ Z`
(`AlgebraicGeometry.WeilComplex.exists_dense_isLisse_homologySheaf_upperStar`); let
`i : T ⟶ Z` be the reduced closed complement. In the closed-support triangle
`i_* Ri^! K ⟶ K ⟶ Rj_* j^* K ⟶`, the unit is invertible at `Rj_* j^* K` by smooth base change
and homotopy invariance for complexes with lisse cohomology
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_of_isLisse_homologySheaf`), and at
`i_* Ri^! K` by smooth base change and the induction hypothesis for `T`, whose image in `X` is a
strictly smaller closed subset
(`AlgebraicGeometry.WeilComplex.isIso_unit_app_derivedLowerStar_obj`).
The objects at which the unit is invertible form a triangulated subcategory
(`CategoryTheory.Adjunction.isTriangulated_isoLocus_unit`), so it is invertible at `K`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.WeilComplex

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

end AlgebraicGeometry.WeilComplex
