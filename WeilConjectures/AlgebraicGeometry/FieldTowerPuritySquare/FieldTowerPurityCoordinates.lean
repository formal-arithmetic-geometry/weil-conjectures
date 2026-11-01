/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystem.FieldExceptionalSystemIso
public import WeilConjectures.AlgebraicGeometry.FieldExceptionalSystem.FieldExceptionalSystemLaws
public import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionCompatibilities
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalChart
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalObjects
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemComparison
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemModels
public import WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalRealization
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SmoothPurityMap
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothPurityMaps
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1CoefficientCoordinates
public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1GeometricCoordinates
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
public import WeilConjectures.AlgebraicGeometry.Finite.General.FiniteGeneralRing
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekCalculus
public import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerTransitionCompatibility
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Diagonal.PurityDiagonalDualizingObject
public import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerBoundsOperations
public import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormula
public import Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData

/-! # Root-normalized scalar comparison of the ordered Tate line

Source: field-extension-towers proof (2), root-line comparison and tensor powers
(blueprint: def-sp-field-tower-purity-line-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures

namespace AlgebraicGeometry.ProEtale.FieldTowerPuritySquare
open FieldShriekSystem FieldExceptionalSystem
variable (P : PurityFiniteSetting.{u}) (D : Models P)

/-- The ordinary scalar comparison is fixed on every coefficient/root generator.
The shifted comparison is its localization through the scalar model counit,
with the canonical cochain and localization shift maps.
Source: blueprint field-extension-towers proof (2), rank-one scalar comparison
(blueprint: def-sp-field-tower-purity-line-coordinates). -/
structure LineCoordinates {E F : Index P} (h : E ≤ F) (X : Scheme.{u})
    (wE : SpChartAdmissibility.Twists P.coefficients.l E.val X)
    (wF : SpChartAdmissibility.Twists P.coefficients.l F.val X) where
  rootsE : SpCoordinateAdjunction.RootLines P.coefficients.l E.val X
  rootsF : SpCoordinateAdjunction.RootLines P.coefficients.l F.val X
  restriction : ∀ n : ℕ, FieldShriekSystem.RestrictionEvaluation P D h X n
  ordinary : (D.scalars E F h X).model.E.obj (wE.tower 1) ≅ wF.tower 1
  normalized : ∀ (n : ℕ) (U : X.ProEtᵒᵖ)
    (a : (SpTowerShriek.B P.coefficients.l E.val X n).obj.obj U)
    (z : (Scheme.proEtaleRootsOfUnitySheaf X (P.coefficients.l ^ (n + 1))).obj.obj U),
    (((SpTowerShriek.ev P.coefficients.l E.val X n).map
          (((D.scalars E F h X).ordinaryAdjunction.homEquiv _ _) ordinary.hom) ≫
        (restriction n).ordinary.hom.app (wF.tower 1) ≫
        (proEtaleRingRestrictScalars
          (proEtaleConstantRingMap (T := X) ((D.coefficients E F h).quotient n))).map
          ((wF.level n 1).hom ≫ (rootsF.iso n).hom)).val.app U
      (((rootsE.iso n).inv ≫ (wE.level n 1).inv).val.app U
        (Scheme.tateFiniteTensor X P.coefficients.l
          (SpTowerClasses.FiniteRing P.coefficients.l E.val n) n
          (SpTowerClasses.finiteScalar P.coefficients.l E.val n) U.unop a z)) =
      Scheme.tateFiniteTensor X P.coefficients.l
        (SpTowerClasses.FiniteRing P.coefficients.l F.val n) n
        (SpTowerClasses.finiteScalar P.coefficients.l F.val n) U.unop
        ((proEtaleConstantRingMap (T := X) ((D.coefficients E F h).quotient n)).hom.app U a) z)
  shifted : (D.scalars E F h X).T.obj
      ((SpCoordinateAdjunction.line P.coefficients.l E.val wE 1)⟦(2 : ℤ)⟧) ≅
    (SpCoordinateAdjunction.line P.coefficients.l F.val wF 1)⟦(2 : ℤ)⟧
  model :
    (D.scalars E F h X).T.map ((DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app
        (SpCoordinateAdjunction.lineComplex P.coefficients.l E.val wE 1)) ≫ shifted.hom =
    (D.scalars E F h X).model.ε.app
        ((SpCoordinateAdjunction.lineComplex P.coefficients.l E.val wE 1)⟦(2 : ℤ)⟧) ≫
      DerivedCategory.Q.map
        ((((D.scalars E F h X).model.E.mapHomologicalComplex (.up ℤ)).commShiftIso
            (2 : ℤ)).hom.app
            (SpCoordinateAdjunction.lineComplex P.coefficients.l E.val wE 1) ≫
          (shiftFunctor _ (2 : ℤ)).map
            (((D.scalars E F h X).model.E.mapCochainComplexSingleFunctor 0).hom.app
                (wE.tower 1) ≫
              (CochainComplex.singleFunctor _ 0).map ordinary.hom)) ≫
      (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app
        (SpCoordinateAdjunction.lineComplex P.coefficients.l F.val wF 1)

end AlgebraicGeometry.ProEtale.FieldTowerPuritySquare
