# Sheaf.Paper.ConstantCoefficientScalarNormalization

## Reason

Preflight requests a change record for the setup commands supporting the private,
proved regular-module scalar-extension helpers. The added universe and variable
context belongs to `ConstantScalarNormalization` and ends before the original
public declarations. The local notation ends with that namespace. The additional
instance-size option supports typeclass synthesis for the sheaf constructions.
The instance removal repeats the removal already made by the retained public
import `Sheaf.Paper.FiniteFreeCompletedScalarComparison`; it introduces no new
instance removal for consumers.

All existing signatures, definitions, visibility and public imports are preserved.
Only proofs, private proved helpers, proof imports, the proof setup, and the
isomorphism theorem's proof explanation change. No target statement or definition
changes meaning. No downstream module needs adaptation. The item closes its two
remaining holes without introducing any new holes.

## Old

Original opening command context, verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : Scheme.{u})
```

The later original command `variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)`
is unchanged.

## New

New generic-helper command context, verbatim:

```lean
@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 1024
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings
universe v c r
namespace ConstantScalarNormalization
variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}} (α : R ⟶ S)
set_option hygiene false in
local notation "ring" A => (sheafCompose J (forget₂ CommRingCat RingCat)).obj A
```

The private helpers are followed by the original public-declaration context:

```lean
end ConstantScalarNormalization

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
  (ι : E →ₐ[Padic l] L) (Y : Scheme.{u})
```

The later original command `variable (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)`
is unchanged. No original declaration signature changes.

## Users

The required `tools/downstream.py --uses` scan found 228 transitive importers.
The declaration-use scan found this module and
`Sheaf.Paper.ConstantWeilStructureStageIndependence`. The following table includes
all modules from both scans, with current holders; no consumer is edited.

| module | group holding it | effect |
|---|---|---|
| Sheaf.DeligneLaumon.GenericDualityModel | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.EtaleCohomology.Purity.RealSheaves.TateTwistWeightShift | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityExceptionalReduction | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityFiniteTensor | W8 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityObjects | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityRootComparisons | X5 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPuritySourceReduction | X6 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicPurityTwistReduction | X8 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.AdicSmoothDualizingComplexes | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CanonicalCoefficientPullbackReduction | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | G4 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CompletedStalkFrobeniusReduction | A4 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ConnectedConstantH0 | W3 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ConstantCoefficientScalarNormalization | D4 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ConstantWeilStructureStageIndependence | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.DualizingObjectPurity | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FinitePointInternalHomEvaluation | N3 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionAffineOrientation | T6 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionChartCalculus | S7 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionComparisons | T7 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionOfPurity | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteReductionRootCharts | D8 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteSmoothPullbackExchange | V6 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteTorStability | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FiniteUniversalSmoothTrace | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FixedStalkIdentificationReduction | W4 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FourierTraceFormula | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.FrobeniusFixesUnitSection | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | E5 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PointCompletedEvaluation | E4 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PurAdicReconstruction | H8 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PurityCompositionCoherence | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalBaseChangeCompared | R3 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalDualizingObject | G3 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDiagonalSectionPasting | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDncComparisons | G3 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDncFamilyIntrinsic | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PurityDncInvariance | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.PuritySectionInvariantIntrinsic | K6 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.QbarMiddleTStructure | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSubcategories | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.QbarPerverseSupportCondition | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalPurityPresentation | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalScalarTransposeCompatibility | K8 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalSmoothPurityCanonical | W5 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.RegularImmersionPurityComparison | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SfBidualityClass | C6 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPullbackSupportDimension | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothPurityMap | R2 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SmoothTrace | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.TateTwistSupportCondition | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.TwistFrobeniusScalar | G4 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierInversion | J6 | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.WeilOne | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.Paper.ZlShriekComposition | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | D6 | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.PurityDncCoefficientTransport | K9 | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.ReductionCompatibilities | E6 | Existing interface unchanged; no adaptation. |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.ArbitraryFieldVerdier | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefIntegralFiniteExtension | A9 | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | R5 | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.CoefTowerNaturalCurrying | F2 | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.FiniteMappingAdjunction | J7 | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralDualizing | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.IntegralVerdier | V2 | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.QbarDualRecollement | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | A4 | Existing interface unchanged; no adaptation. |
| Sheaf.SixFunctors.RationalVerdier | V4 | Existing interface unchanged; no adaptation. |
| Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison | T2 | Existing interface unchanged; no adaptation. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Existing interface unchanged; no adaptation. |
| TargetsCheck | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Adic | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.EtaleCohomology.Purity.Smooth.Rational | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Adic.Reduction | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ClosedUpperShriekCoproducts | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactConstructible | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ExcisionComparison | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegral | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationIntegralClosedSupport | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRational | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.LocalizationRationalWeil | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.NormalizedTowerRealization | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.RestrictScalars | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.Etale.Derived.ScalarExtension | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.CompactLocalizing | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekLocalizing | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.Statement | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyDegreeZero | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CohomologyZero | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Curve | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.DirectImageStalkMap | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.Finiteness | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LocalizationRational | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Existing interface unchanged; no adaptation. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Existing interface unchanged; no adaptation. |

## Status

landed 20261019T192708-L-1856128 2026-10-19 (merge of deliver/D4/Sheaf.Paper.ConstantCoefficientScalarNormalization)
