# Sheaf.Paper.ECoefficientSmoothBaseChange module environment

## Reason

The static check flags the new file-wide elaboration option and the scoped `omit`
command as a module-environment change. The option changes elaboration transparency;
it introduces no declaration or instance. `omit [Fact l.Prime] in` makes explicit that
the stalk unit lemma needs no primality assumption; its existing signature has no
primality binder because neither the statement nor proof requires that section variable.
No target, existing definition, theorem conclusion, or public import changes.
The unit-route import ProEtaleSiteComparisonFiniteLevel is retained.

## Old

```lean
public import Sheaf.Paper.AdmissibleLattices
public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.Paper.ProEtaleCanonicalTensorPullback
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonDerived
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.Paper.AdicSmoothBaseChange
import Sheaf.Paper.IntegralUniformCoefficient
import Sheaf.Paper.PbcRationalCategory
```

The existing options were:
```lean
set_option autoImplicit false
set_option synthInstance.maxSize 2048
```
The declaration began directly with its docstring and `theorem sbcPrimeUnitOnSource`.

## New

```lean
public import Sheaf.Paper.AdmissibleLattices
public import Sheaf.Paper.SbcCompletedOperations
public import Sheaf.AlgebraicGeometry.BaseChangeInverseImageIso
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.AlgebraicGeometry.ProEtaleSiteComparisonFiniteLevel
import Sheaf.CategoryTheory.ScalarLocalization
import Sheaf.Paper.AdicSmoothBaseChange
import Mathlib.Algebra.CharP.CharAndCard
import Sheaf.Paper.SbcFiniteWitnessRealization
import Sheaf.Paper.SbcFiniteConstructibility
```

The options now include:
```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
```
The same stalk-unit declaration is scoped by:
```lean
omit [Fact l.Prime] in
```
Its statement text and all existing definitions remain unchanged. The five removed
imports are proof-only. The two new imports are proof-only and all public imports are
identical. No new private helper occurs in any existing public definition or signature.

## Users

The source-only downstream scan listed these modules. All see the same public imports
and existing declaration signatures; none needs adaptation. Holders are from the current
claim records. The two direct consumers mentioning sbcPrimeUnitOnSource are
Sheaf.Paper.ExchangeFunctoriality and Sheaf.Paper.QbarCoefficientSmoothBaseChange.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ECoefficientSmoothBaseChange | K3 | proofs and elaboration commands changed |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.DeligneLaumon.Reduction.Composition | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.ArithmeticRoots | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.ChernFlagFormula | G4 | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.CommonStageConstituentNonexceptional | P2 | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.CommonStageFourierWeightUpper | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.CurveMiddleExtensionUpper | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.ExchangeFunctoriality | D6 | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.ExtensionByZeroPunctual | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.FiniteEtaleLisseWeilImage | H7 | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.FlagLocalComparison | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.FourierTraceFormula | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.LocalizedTopChern | E5 | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.PurityChernClasses | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.QbarCoefficientSmoothBaseChange | S3 | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | K7 | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.SmoothProperPurityHypotheses | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.WeilCohomologyScalarExtensionQlbar | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.WeilFourierInversion | J6 | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.WeilFourierPlancherel | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.WeilOne | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.Paper.ZlShriekComposition | unclaimed | existing exported declarations and signatures retained; no adaptation |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | existing exported declarations and signatures retained; no adaptation |
| TargetsCheck | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.BoundaryWeights | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.FiniteBoundary | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariants | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryStalkInvariantsUnconditional | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafCoinvariants | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.UnramifiedBoundary | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.Statement | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.AffineLineCohomology | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.CohomologicalRange | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.CohomologicalRangeAffine | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.Curve | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.CurveEndpoints | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.CurveTopCohomology | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.EulerProduct | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.FourierInversion | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.FourierInversion.Composite | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.FourierInversion.Delta | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.FourierInversion.OtherSections | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.FourierInversion.Vanishing | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.FourierPlancherel | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.FourierStalk | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.FourierTrace | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.GrothendieckLefschetz | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.LFunction | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.LissePoincarePairing | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.LowerShriekOperations | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.LowerShriekPackage | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.OpenClosedTriangle | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.PoincareDualityLisse | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.RealPurity | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.TraceIsomorphism | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.UnramifiedBoundaryPurity | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.VerdierDual | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.VerdierDualFinite | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.WeilSheaf.VerdierDualLocalization | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.CohomologicalFamily | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.Examples | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.Rationality | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.TraceFormula | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | existing exported declarations and signatures retained; no adaptation |
| WeilConjectures.ZetaFunction.Weights | unclaimed | existing exported declarations and signatures retained; no adaptation |

## Status

landed 20261019T231228-L-563531 2026-10-19 (merge of deliver/K3/Sheaf.Paper.ECoefficientSmoothBaseChange)
