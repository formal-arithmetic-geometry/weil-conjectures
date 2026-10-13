/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension

/-!
# Torsion cohomological dimension of an inverse limit

A uniform bound `cd_tor(Xᵢ) ≤ c` on a cofiltered system of quasi-compact quasi-separated schemes
with affine transition maps passes to the limit `X = lim Xᵢ`
(`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE.of_isLimit`, blueprint
`lem-sc-cd-affine-limit`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- Blueprint `lem-sc-cd-affine-limit`: Passing a uniform torsion bound to an affine limit.

Let `X = lim Xᵢ` be the limit of a cofiltered system `D` of quasi-compact quasi-separated
schemes with affine transition maps. If `cd_tor(Xᵢ) ≤ c` for every `i`, then `cd_tor(X) ≤ c`.

A torsion sheaf `F` on `X` killed by `n` is the filtered colimit of the pullbacks `pᵢ^* pᵢ_* F`,
whose cohomology is the colimit of the cohomology of the `pⱼᵢ^* pᵢ_* F` on the `Xⱼ`, `j ⟶ i`;
cohomology commutes with filtered colimits, and a general torsion sheaf is the union of its
`n`-torsion subsheaves. -/
theorem HasTorsionCohomologicalDimensionLE.of_isLimit {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) {n : ℕ}
    (h : ∀ i, (D.obj i).HasTorsionCohomologicalDimensionLE n) :
    c.pt.HasTorsionCohomologicalDimensionLE n :=
  sorry

end AlgebraicGeometry.Scheme
