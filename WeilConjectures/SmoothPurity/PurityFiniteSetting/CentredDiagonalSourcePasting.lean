/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.DiagonalDncChartNormalization
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPasting
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Section.SectionEtaleOpenCancellation
import WeilConjectures.AlgebraicGeometry.DifferenceCoordinateSection.DifferenceFirstInputRestriction
import WeilConjectures.SmoothPurity.PurityFiniteSetting.DiagonalPasting.PurityDiagonalSectionPasting
import WeilConjectures.SmoothPurity.PurityFiniteSetting.FiniteTypeExceptionalInverseImage
import WeilConjectures.AlgebraicGeometry.AffineDifferenceTower.AffineDifferenceTowerFactorization

/-! # Source pasting in centred difference coordinates

Source: composition coherence proof Step 1, compatible-chart argument Steps 5--6.
(blueprint: lem-pur-centred-diagonal-source-pasting).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

open CategoryTheory.MonoidalCategory in
private theorem comparisonTensor_hom (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [CategoryTheory.MonoidalCategory A]
    [CategoryTheory.MonoidalPreadditive A] [CategoryTheory.SymmetricCategory A]
    [CategoryTheory.MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (U : Scheme.{u}) [(ProEtale.comparisonUpperStar A U).PreservesFlat]
    (K L : _root_.DerivedCategory (Sheaf U.smallEtaleTopology
      A)) :
    ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      A K).app L).hom =
    (ProEtale.comparisonUpperStar
      A U).leftDerivedFunctorIsoMapDerivedCategory.inv.app (K ⊗ L) ≫
      (((ProEtale.comparisonUpperStar
        A U).leftDerivedTensorComparison.app K).app L) ≫
      ((ProEtale.comparisonUpperStar
        A U).leftDerivedFunctorIsoMapDerivedCategory.hom.app K ⊗ₘ
      (ProEtale.comparisonUpperStar
        A U).leftDerivedFunctorIsoMapDerivedCategory.hom.app
          L) := by
  rw [tensorHom_def']
  rfl

open CategoryTheory.MonoidalCategory in
private theorem comparisonTensor_naturality (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [CategoryTheory.MonoidalCategory A]
    [CategoryTheory.MonoidalPreadditive A] [CategoryTheory.SymmetricCategory A]
    [CategoryTheory.MonoidalClosed A] [Abelian.HasFunctorialFlatResolution A]
    (U : Scheme.{u}) [(ProEtale.comparisonUpperStar A U).PreservesFlat]
    {K K' L L' : _root_.DerivedCategory (Sheaf U.smallEtaleTopology
      A)} (a : K ⟶ K') (b : L ⟶ L') :
    (ProEtale.comparisonUpperStar
      A U).mapDerivedCategory.map (a ⊗ₘ b) ≫
        ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
          A K').app L').hom =
      ((ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
        A K).app L).hom ≫
        ((ProEtale.comparisonUpperStar
          A U).mapDerivedCategory.map a ⊗ₘ
        (ProEtale.comparisonUpperStar
          A U).mapDerivedCategory.map b) := by
  rw [comparisonTensor_hom, comparisonTensor_hom]
  rw [NatTrans.naturality_assoc,
    Functor.leftDerivedTensorComparison_naturality_tensorHom_assoc]
  simp only [Category.assoc]
  congr 2
  rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
  rw [NatTrans.naturality, NatTrans.naturality]

private theorem tensorMap_comp {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {A B C' D E F : C} (a : A ≅ B) (b : B ≅ C') (c : D ≅ E) (d : E ≅ F) :
    (((T.mapIso (a ≪≫ b)).app D) ≪≫ (T.obj C').mapIso (c ≪≫ d)).hom =
      (((T.mapIso a).app D) ≪≫ (T.obj B).mapIso c).hom ≫
        (((T.mapIso b).app E) ≪≫ (T.obj C').mapIso d).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp,
    NatTrans.comp_app, Category.assoc]
  rw [← NatTrans.naturality_assoc]

end WeilConjectures.PurityFiniteSetting
