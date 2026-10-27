/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.TowerIntegralPullbackData
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic

/-! # Canonical units endpoint mate calculation

Source: Stacks Project, Tag 00WX; the units endpoint of the change-of-site
pullback square. This is the canonical special case used to reduce the
arbitrary units-map endpoint to the chartwise normalized map.
(blueprint: lem-sp-integral-site-pullback-units-endpoint-canonical)

The proof transposes both sides through the comparison and inverse-image
adjunctions. For the canonical units map, its transpose is `unitsDirect`,
whose value on every pro-etale chart is pullback along the first projection.
The defining conjugate adjunction comparison then identifies both mates.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-- The endpoint equality for the canonical units map `towerIntegral_unitsSheafPull`.

This is strictly simpler than the arbitrary-map endpoint: the map is fixed by
its adjoint `unitsDirect`, so no chartwise hypothesis is required. -/
theorem integral_site_pullback_units_endpoint_canonical {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let κ := comparisonUpperStarCompUpperStarIso AddCommGrpCat.{u + 1} f
    (κ.inv.app Y.gmSheaf ≫
        (upperStar AddCommGrpCat.{u + 1} f).map (cartierUnitsComparison Y) ≫
        towerIntegral_unitsSheafPull f =
      (comparisonUpperStar AddCommGrpCat.{u + 1} X).map
          (Scheme.upperStarGmSheafToGmSheaf f) ≫ cartierUnitsComparison X) := by
  dsimp
  unfold towerIntegral_unitsSheafPull
  apply ((comparisonAdjunction AddCommGrpCat.{u + 1} X).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [cancel_epi ((comparisonAdjunction AddCommGrpCat.{u + 1} X).unit.app
    ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj Y.gmSheaf))]
  simp only [Functor.map_comp]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp]
  simp only [← Functor.map_comp]
  unfold comparisonUpperStarCompUpperStarIso
  unfold Scheme.upperStarGmSheafToGmSheaf
  simp only [Adjunction.homEquiv_counit]
  rw [conjugateIsoEquiv_symm_apply_inv]
  unfold cartierUnitsComparison
  ext U x
  unfold unitsDirect
  simp
  sorry

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
