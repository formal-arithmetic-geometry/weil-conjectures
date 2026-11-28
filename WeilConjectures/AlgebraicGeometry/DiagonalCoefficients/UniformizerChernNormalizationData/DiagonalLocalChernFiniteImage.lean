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

section ExtLeft
attribute [local irreducible] Scheme.finiteEtaleTateLine

/-- The fixed-endpoint pro-etale image of a finite etale Ext class is its comparison image
between the explicit constant and Tate-line endpoints. -/
theorem finiteEtaleProImage_hom (A : Type (u + 1)) [CommRing A] (T : Scheme.{u})
    (N : ℕ) (hA : (N : A) = 0)
    (b : Ext (Etale.ordinaryFiniteConstant A T) (Scheme.finiteEtaleTateLine T N A hA) 2) :
    (Ext.mk₀CompMk₀ (DiagonalTrace.finiteEtaleConstantIso A T).inv
      (b.mapExactFunctor (comparisonUpperStar (ModuleCat.{u + 1} A) T))
      (DiagonalTrace.finiteEtaleLineIso A T N hA).hom).hom =
      (finiteUnitComparison A T).inv ≫ (geoP1Comparison A T).map b.hom ≫
        (finiteLineComparison A N hA T).hom := by
  simp only [Ext.mk₀CompMk₀, Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    ← SpTowerClasses.FiniteExactArrow.mapSingleArrow_ext]
  unfold finiteUnitComparison finiteLineComparison Etale.p1DecompositionShiftedComparison
    finiteSingleComparison DiagonalTrace.finiteEtaleConstantIso finiteConstantComparison
    DiagonalTrace.finiteEtaleLineIso SpTowerClasses.mapSingleArrow Functor.compIsoApp
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv, Functor.mapIso_hom, Iso.app_inv,
    Iso.app_hom, Functor.isoWhiskerRight_inv, NatTrans.comp_app,
    Functor.whiskerRight_app, eqToIso.inv, eqToHom_refl, Iso.refl_hom,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.assoc,
    Category.comp_id]
  erw [Category.id_comp, Category.comp_id]
  rfl

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
  obtain ⟨b, rfl⟩ := (Etale.ordinaryFiniteExtHomEquiv A T (Etale.ordinaryFiniteConstant A T)
    (Scheme.finiteEtaleTateLine T N A hA) 2).surjective g
  rw [← DiagonalTrace.integralImage]
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp,
    ← SpTowerClasses.FiniteExactArrow.mapSingleArrow_ext, DiagonalTrace.finiteEtaleProImage_apply]
  rw [Etale.ordinaryFiniteExtHomEquiv_eq]
  exact congrArg (fun t ↦ _ ≫ SpTowerClasses.mapSingleArrow (cartierForget A T) 2 t)
    (finiteEtaleProImage_hom A T N hA b)

end ExtLeft

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
