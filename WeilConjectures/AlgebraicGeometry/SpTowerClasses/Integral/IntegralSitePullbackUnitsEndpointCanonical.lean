/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralPullbackData
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
import WeilConjectures.WeilSheaf.FieldCoefficientTateTwist

/-! # Canonical units endpoint mate calculation

The units endpoint square for the canonical units map, whose transpose is `unitsDirect`.

Source: Stacks Project, Tag 00WX.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

/-- The endpoint equality for the canonical units map `towerIntegral_unitsSheafPull`. -/
theorem integral_site_pullback_units_endpoint_canonical {X Y : Scheme.{u}} (f : X ⟶ Y) :
    let κ := comparisonUpperStarCompUpperStarIso AddCommGrpCat.{u + 1} f
    (κ.inv.app Y.gmSheaf ≫
        (upperStar AddCommGrpCat.{u + 1} f).map (cartierUnitsComparison Y) ≫
        towerIntegral_unitsSheafPull f =
      (comparisonUpperStar AddCommGrpCat.{u + 1} X).map
          (Scheme.upperStarGmSheafToGmSheaf f) ≫ cartierUnitsComparison X) := by
  dsimp
  apply (cancel_epi
    ((comparisonUpperStarCompUpperStarIso AddCommGrpCat.{u + 1} f).hom.app Y.gmSheaf)).mp
  simp only [Iso.hom_inv_id_app_assoc]
  symm
  apply conjugateIsoEquiv_symm_hom_app_comp_map_comp
    (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f)
    (comparisonAdjunction AddCommGrpCat.{u + 1} Y)
    (comparisonAdjunction AddCommGrpCat.{u + 1} X)
    (lowerStarCompComparisonLowerStarIso f AddCommGrpCat.{u + 1}).symm
  simp only [Scheme.upperStarGmSheafToGmSheaf, cartierUnitsComparison,
    towerIntegral_unitsSheafPull, Equiv.apply_symm_apply]
  erw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  ext U x
  simp [unitsDirect, lowerStarCompComparisonLowerStarIso, comparisonLowerStar,
    Etale.lowerStar, ProEtale.lowerStar, toProEtCompOverPullbackIso,
    Scheme.gmSheafToLowerStarGmSheaf, Scheme.etaleStructurePresheafToPullback]
  rfl

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
