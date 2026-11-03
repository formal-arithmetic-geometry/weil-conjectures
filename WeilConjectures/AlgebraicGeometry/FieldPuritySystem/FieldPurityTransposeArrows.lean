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
public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionExceptionalConservativity
public import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemComparison
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.FieldShriekSystem.FieldShriekSystemModels
public import WeilConjectures.Algebra.Homology.RingedTensorSquare.RingedExchangeTensorCoherence
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.AlgebraicGeometry.SpTowerGamma.SmoothPurityTowerGammaData
public import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerGluingData
import WeilConjectures.AlgebraicGeometry.SpTowerCalculus.CoefficientTowerShriekInterfaces
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartData
import WeilConjectures.AlgebraicGeometry.VaryingRingGraph.VaryingRingGraphSummand
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
import WeilConjectures.Compactification.CategoryBaseChange
import WeilConjectures.AlgebraicGeometry.SmoothPurity.CompactifiableCompatibleTower
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.AlgebraicGeometry.StrictTower.StrictTowerProperOpenCalculus
import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.Algebra.Homology.Ringed.RingedOpenTotalTensorKFlat
import WeilConjectures.AlgebraicGeometry.SemilinearProperOpen.SemilinearProperOpenMatePasting
import WeilConjectures.AlgebraicGeometry.VaryingRing.SemilinearScalarRestriction
import WeilConjectures.AlgebraicGeometry.SmoothPurity.ChartNormalizedModelIdentification
import WeilConjectures.AlgebraicGeometry.ProperOpenCalculus.CompactificationRefinementCoherence
import WeilConjectures.AlgebraicGeometry.CoefficientCompatibility.EtaleProEtaleCoefficientCompatibility
import WeilConjectures.AlgebraicGeometry.AdjunctionTransfer.EtaleCtfChartDomain
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting
import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSupportDomains
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.TowerGeometryAdjunctionEvaluation
import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingProperOpenPasting
import WeilConjectures.CategoryTheory.RingedSliceExtensionExactness
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityEtaleNormalization
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateRightComparisons
import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerChartAdmissibility
import WeilConjectures.AlgebraicGeometry.SpTowerP1.SmoothPurityTowerP1Adjunction
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.AlgebraicGeometry.SpCoordinateAdjunction.SmoothPurityCoordinateCategories
import WeilConjectures.AlgebraicGeometry.SmoothOfRelativeDimension.SmoothAdmissibleCoordinateCover
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerBinaryPairGluing
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerPairOpenRestriction2
import WeilConjectures.AlgebraicGeometry.SpTowerGluing.SmoothPurityTowerLocalCounitRepresentability
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
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
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.SpChartAdmissibility.SmoothPurityTowerBoundsOperations
public import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.AlgebraicGeometry.SmoothPurity.TowerOperationsGroundFieldRetagging
import WeilConjectures.AlgebraicGeometry.SpFiniteOrientation.FiniteOrientationReduction
import WeilConjectures.SmoothPurity.Finite.FiniteLineTensorConditions
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.AlgebraicGeometry.Finite.FiniteLocallyFreeLineModels
import WeilConjectures.SmoothPurity.Supporting.SignedLineTensorEquivalence
import WeilConjectures.SixFunctors.Finite.Scalar.Tensor.FiniteScalarTensorRealization
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonTorInterval
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormula
public import Mathlib.FieldTheory.Finite.Basic
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalSmoothnessFiniteComparison
public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekData

/-! # Coefficient compatibility of the tower purity transpose

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-lem-sp-field-extension/sk-lem-sp-field-extension-towers.proof.md (2), tensor transpose
(blueprint: def-sp-field-purity-transpose-arrows).

All equalities are in the ordinary derived category of strict varying-coefficient
systems, in the published section coordinates. Index n means positive exponent n+1.
The maps below are actual adjunction transposes, rather than lifts of finite maps.
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

namespace AlgebraicGeometry.ProEtale.FieldPuritySystem

open FieldShriekSystem FieldExceptionalSystem
variable (P : PurityFiniteSetting.{u}) (D : Models P)

/-- The coefficient module already used by the tower orientation theorem.
Source: blueprint (2), J_A (blueprint: def-sp-field-purity-transpose-arrows). -/
abbrev coefficient (E : Index P) (T : Scheme.{u}) :=
  SpTowerClasses.coefficient T (SpTowerClasses.Arings P.coefficients.l E.val T)

variable {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
  (b : FieldShriekSystem.Laws P D c) (a : Domains P D c) (A : Adjoints P D c b a)

variable (t : ProjectionTensorComparisons P D) (q : Coordinates P D (f := f))

/-- The specified exceptional image of the coefficient unit.
Source: blueprint (2), omega_A (blueprint: def-sp-field-purity-transpose-arrows). -/
def omega (E : Index P) : N P D E X := (A.right E).obj (unit P D q E)

/-- Pullback of K tensor W, retained in the same full system category.
Source: blueprint (2), tensor source (blueprint: def-sp-field-purity-transpose-arrows). -/
def tensorSource (E : Index P) (K : N P D E Y) (W : N P D E X) : N P D E X :=
  ⟨_, q.tensor_mem E K W⟩

/-- The explicit inverse projection followed by identity tensor counit and right unit.
Source: blueprint (2), the displayed counit composite
(blueprint: def-sp-field-purity-transpose-arrows). -/
@[irreducible]
def projectionCounit (E : Index P) (K : N P D E Y)
    (hpf : IsIso (leftProjection P D t E c K.obj (omega P D c b a A q E).obj)) :
    (support P D c a E).obj (tensorSource P D q E K (omega P D c b a A q E)) ⟶ K :=
  ObjectProperty.homMk
    (@inv _ _ _ _ (leftProjection P D t E c K.obj (omega P D c b a A q E).obj) hpf ≫
      (SpTowerShriek.tensor P.coefficients.l E.val (D.base E) Y).map
        (Prod.mkHom (𝟙 _) ((A.adj E).counit.app (unit P D q E)).hom) ≫
      ((q.tensors E Y (.inr rfl)).rightUnit P.coefficients.l E.val K.obj).hom)

/-- Tau is literally the tower adjunction transpose, including its counit normalization.
Source: blueprint (2), tau_A,K (blueprint: def-sp-field-purity-transpose-arrows). -/
@[irreducible]
def tau (E : Index P) (K : N P D E Y)
    (hpf : IsIso (leftProjection P D t E c K.obj (omega P D c b a A q E).obj)) :
    tensorSource P D q E K (omega P D c b a A q E) ⟶ (A.right E).obj K :=
  (A.adj E).homEquiv _ _ (projectionCounit P D c b a A t q E K hpf)

/-- The exceptional unit component followed by G_B of the canonical scalar unitor.
Source: blueprint (2), c_JA under C_Y J_A = J_B
(blueprint: def-sp-field-purity-transpose-arrows). -/
@[irreducible]
def omegaComparison {E F : Index P} (h : E ≤ F) :
    (D.scalars E F h X).T.obj (omega P D c b a A q E).obj ⟶
      (omega P D c b a A q F).obj :=
  (component P D c b a A h (unit P D q E)).hom ≫
    ((A.right F).map (ObjectProperty.homMk (Y := unit P D q F)
      (q.scalarUnit E F h Y (.inr rfl)).derived.hom)).hom

/-- The first displayed whole-system equality, with its source comparison written out.
Source: blueprint (2), tensor-map transpose
(blueprint: def-sp-field-purity-transpose-arrows). -/
@[irreducible]
def TensorCompatibility {E F : Index P} (h : E ≤ F) (K : N P D E Y)
    (hA : IsIso (leftProjection P D t E c K.obj (omega P D c b a A q E).obj))
    (hB : IsIso (leftProjection P D t F c ((scalar P D a h Y).obj K).obj
      (omega P D c b a A q F).obj)) : Prop :=
  (D.scalars E F h X).T.map (tau P D c b a A t q E K hA).hom ≫
      (component P D c b a A h K).hom =
    (projectionTarget P D t h f K.obj (omega P D c b a A q E).obj).hom ≫
      (SpTowerShriek.tensor P.coefficients.l F.val (D.base F) X).map
        (Prod.mkHom (𝟙 _) (omegaComparison P D c b a A q h)) ≫
      (tau P D c b a A t q F ((scalar P D a h Y).obj K) hB).hom

end AlgebraicGeometry.ProEtale.FieldPuritySystem
