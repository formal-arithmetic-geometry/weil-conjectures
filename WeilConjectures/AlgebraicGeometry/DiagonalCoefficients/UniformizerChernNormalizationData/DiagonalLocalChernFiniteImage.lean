/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalUniformizerLocalChernDefinitions
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Local.DiagonalLocalIntegralProjection
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImage
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralKummer
import all WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleIntegralEndpoints
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.DiagonalCompletedOrdinaryUnit
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientUnitNormalization
import all WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalSupportedCoefficientLimit
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalRootLimitCompatibility
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalFiniteRootsCanonicalMap
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Trace.DiagonalTraceFiniteEtaleImageSurjective
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerChernNormalizationData.DiagonalLocalChernHEqCongr
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus

/-! # The integral pro-etale image of an ordinary finite class
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients
-- Use the same abelian structure on module sheaves as the exact-derived comparison APIs.
attribute [-instance] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

section ExactImage
attribute [-instance] ConstantScalarRestriction.fixedAbelian
set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2

/-- The finite comparison image of an ordinary finite arrow, unfolded. -/
theorem finiteComparison_heq (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (N : ℕ) (hA : (N : A) = 0)
    (g : Etale.ordinaryFiniteUnit A T ⟶ Etale.p1DecompositionTwist A N hA T 1 2) :
    HEq ((finiteUnitComparison A T).inv ≫ (geoP1Comparison A T).map g ≫
        (finiteLineComparison A N hA T).hom)
      (((DerivedCategory.singleFunctor _ 0).map (DiagonalTrace.finiteEtaleConstantIso A T).inv ≫
          ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategorySingleFunctor 0).inv.app
            (Etale.ordinaryFiniteConstant A T)) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map g ≫
        (((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.commShiftIso
            (2 : ℤ)).hom.app _ ≫
          (((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategorySingleFunctor 0).hom.app
            (Scheme.finiteEtaleTateSheaf A N T hA 1))⟦(2 : ℤ)⟧')) := by
  have hU : HEq (finiteUnitComparison A T).inv _ :=
    compIsoApp_isoWhiskerRight_trans_mapIso_inv_heq _ _ _ _
  have hL : HEq (finiteLineComparison A N hA T).hom _ :=
    p1DecompositionShiftedComparison_hom_heq _ _ _ _ _ _ _ rfl _ HEq.rfl _
  heq_congr


/-- The integral image of the ordinary finite class of a finite arrow, as an exact image. -/
theorem ordinaryFiniteClass_integral_heq (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (N : ℕ) (hA : (N : A) = 0) [HasDerivedCategory.{u + 1} (DiagonalAb T)]
    (g : Etale.ordinaryFiniteUnit A T ⟶ Etale.p1DecompositionTwist A N hA T 1 2) :
    HEq (Ext.mk₀CompMk₀ (SpTowerClasses.integerComparison T).inv
      ((Etale.ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T N A hA) 2 g).mapExactFunctor
        (comparisonUpperStar AddCommGrpCat.{u + 1} T))
      ((forgetComparisonIso A T).hom.app (Scheme.finiteEtaleTateLine T N A hA))).hom
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
        ((SpTowerClasses.integerComparison T).inv ≫
          (comparisonUpperStar AddCommGrpCat.{u + 1} T).map
            (Etale.ordinaryFiniteIntegralGenerator A T) ≫
          (forgetComparisonIso A T).hom.app (Etale.ordinaryFiniteConstant A T) ≫
          (cartierForget A T).map (DiagonalTrace.finiteEtaleConstantIso A T).hom) ≫
      SpTowerClasses.mapSingleArrow (cartierForget A T) 2
      (((DerivedCategory.singleFunctor _ 0).map (DiagonalTrace.finiteEtaleConstantIso A T).inv ≫
          ((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategorySingleFunctor 0).inv.app
            (Etale.ordinaryFiniteConstant A T)) ≫
        (comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.map g ≫
        (((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategory.commShiftIso
            (2 : ℤ)).hom.app _ ≫
          (((comparisonUpperStar (ModuleCat.{u + 1} A) T).mapDerivedCategorySingleFunctor 0).hom.app
            (Scheme.finiteEtaleTateSheaf A N T hA 1))⟦(2 : ℤ)⟧'))) := by
  rw [← (Etale.ordinaryFiniteExtHomEquiv A T (Etale.ordinaryFiniteConstant A T)
    (Scheme.finiteEtaleTateLine T N A hA) 2).apply_symm_apply g,
    Etale.ordinaryFiniteClass_extHomEquiv, Etale.ordinaryFiniteExtClassCore,
    mk₀CompMk₀_mapExactFunctor_square_hom _ _ _ (cartierForget A T) _ _ _
      (DiagonalTrace.finiteEtaleConstantIso A T), map_comp_mapSingleArrow_eq,
    Etale.ordinaryFiniteExtHomEquiv_eq]
  heq_congr

end ExactImage

/-- The pro-etale integral image of an ordinary finite class, as a derived arrow: the
integer generator followed by the forgotten comparison image of the class. -/
theorem ordinaryFiniteClass_integral_hom (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (N : ℕ) (hA : (N : A) = 0) [HasDerivedCategory.{u + 1} (DiagonalAb T)]
    (g : Etale.ordinaryFiniteUnit A T ⟶ Etale.p1DecompositionTwist A N hA T 1 2) :
    (Ext.mk₀CompMk₀ (SpTowerClasses.integerComparison T).inv
      ((Etale.ordinaryFiniteClass A T (Scheme.finiteEtaleTateLine T N A hA) 2 g).mapExactFunctor
        (comparisonUpperStar AddCommGrpCat.{u + 1} T))
      ((forgetComparisonIso A T).hom.app (Scheme.finiteEtaleTateLine T N A hA))).hom =
    (DerivedCategory.singleFunctor (DiagonalAb T) 0).map
        ((SpTowerClasses.integerComparison T).inv ≫
          (comparisonUpperStar AddCommGrpCat.{u + 1} T).map
            (Etale.ordinaryFiniteIntegralGenerator A T) ≫
          (forgetComparisonIso A T).hom.app (Etale.ordinaryFiniteConstant A T) ≫
          (cartierForget A T).map (DiagonalTrace.finiteEtaleConstantIso A T).hom) ≫
      SpTowerClasses.mapSingleArrow (cartierForget A T) 2
        ((finiteUnitComparison A T).inv ≫ (geoP1Comparison A T).map g ≫
          (finiteLineComparison A N hA T).hom) := by
  have h₁ := finiteComparison_heq A T N hA g
  have h₂ := ordinaryFiniteClass_integral_heq A T N hA g
  heq_congr

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
