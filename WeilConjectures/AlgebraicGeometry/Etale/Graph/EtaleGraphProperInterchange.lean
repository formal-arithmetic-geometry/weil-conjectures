/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphChosenComparisons
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianSumMateUnits
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianSumMateSheafNormalization
import WeilConjectures.AlgebraicGeometry.Etale.Graph.EtaleGraphProperSupportUnit

/-! # The proper square without an open source leg

Source: Stacks Project, Tags 0F7I and 0F7J.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunction mapDerivedUpperStarLowerStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso unboundedEtaleLowerShriekCongr

/-- The compact-support interchange for a proper Cartesian square with etale horizontal
maps is the mate of inverse sum exchange. This statement has no open source leg.
Source: Stacks Project, more-etale.tex Tags 0F7B and 0F7F. -/
theorem graph_proper_interchange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {W Y' Z Y : Scheme.{u}}
    [IsNoetherian W] [IsNoetherian Y'] [IsNoetherian Z] [IsNoetherian Y]
    (q : W ⟶ Y') [IsProper q] (p : Z ⟶ Y) [IsProper p]
    (b : W ⟶ Z) [Etale b] [IsSeparated b] [QuasiCompact b]
    (v : Y' ⟶ Y) [Etale v] [IsSeparated v] [QuasiCompact v]
    (sq : IsPullback b q p v)
    [HasCompactification b] [HasCompactification v]
    [HasCompactification (q ≫ v)] [HasCompactification (b ≫ p)]
    [IsIso (((mateEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance)).symm
      (TwoSquare.mk _ _ _ _ (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A)
        sq.toCommSq).hom)))] :
    let sumEx := ((mateEquiv
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) v inferInstance)
      (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) b inferInstance)).symm
      (TwoSquare.mk _ _ _ _
        (exactDerivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq.toCommSq).hom))
    let gam := (mateEquiv
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (TwoSquare.mk _ _ _ _ (inv sumEx)))
    (Functor.isoWhiskerRight (graphChosenProperComparison A q).symm
        (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (rightDerivedLowerShriek (ModuleCat.{u + 1} A) q)
        (graphChosenEtaleComparison A v).symm ≪≫
      unboundedEtaleLowerShriekCompIso A q v ≪≫
      unboundedEtaleLowerShriekCongr A sq.w.symm ≪≫
      (unboundedEtaleLowerShriekCompIso A b p).symm ≪≫
      Functor.isoWhiskerRight (graphChosenEtaleComparison A b)
        (rightDerivedLowerShriek (ModuleCat.{u + 1} A) p) ≪≫
      Functor.isoWhiskerLeft
        (etaleLowerShriek (ModuleCat.{u + 1} A) b inferInstance).mapDerivedCategory
        (graphChosenProperComparison A p)).hom = gam := by
  dsimp only
  let θ := (mateEquiv
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) p)
      (TwoSquare.mk _ _ _ _ (etaleLowerShriekBaseChangeIso A sq).hom))
  have hθ := cartesian_sum_mate_sheaf_normalization A q p b v sq
  have hmate := cartesian_sum_mate_units A q p b v sq
  apply Functor.rightDerived_ext
    ((lowerStar (ModuleCat.{u + 1} A) q).rightDerivedFunctor ⋙
      (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance).mapDerivedCategory)
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit
      (lowerStar (ModuleCat.{u + 1} A) q)
      (etaleLowerShriek (ModuleCat.{u + 1} A) v inferInstance))
    (HomotopyCategory.quasiIso _ (.up ℤ))
  exact (graph_proper_support_unit A q p b v sq.toCommSq θ hθ).trans hmate.symm

end AlgebraicGeometry.Etale
