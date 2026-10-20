# FieldShriekLowerBound local elaboration commands

## Reason

The stage-3 interface scanner classifies namespace opens, universe declarations,
transparency options and local attributes as interface changes. The proof adds the
commands shown below to elaborate the t-structure and scalar-localization argument
within the normal compile limit. These commands introduce no mathematical data,
change no existing declaration type or visibility, and add no global instance.
The local irreducibility attribute prevents repeated unfolding of the chosen
standard t-structures while assembling the final proof.

## Old

```lean
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GeneralAlgebraicallyClosedCoefficients
```

## New

```lean
@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open GeneralAlgebraicallyClosedCoefficients
open CategoryTheory.Triangulated
universe uC vC
open AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures.PurCompactSupport
attribute [local irreducible] sfRationalStandardTStructure sfCommonStageStandardTStructure
```

`WeilConjectures.fieldShriek_lowerBound` keeps its published signature verbatim.
All helpers are private and proved. The only new public theorem is in the new
module `Sheaf.Paper.CommonStageCompactSupportExactness`, with its own DAG node.
The scope around the original theorem suppresses unused-variable lint for its
published dependent instance binder names; it does not change their elaboration.

## Users

The required `tools/downstream.py Sheaf.Paper.FieldShriekLowerBound --uses
WeilConjectures.fieldShriek_lowerBound` scan lists 97 transitive consumers and
finds no textual use of the declaration outside its own module. Three direct
importers are `WeilShriekShiftCompatibility`, `FieldWeilShriekShiftData`, and
`CompactSupportLerayFiltration`. Every existing signature remains unchanged.
No consumer file is modified in this delivery.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.FieldShriekLowerBound` | F1 | Proof and local elaboration commands changed |
| `Sheaf.DeligneLaumon.GenericDualityModel` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.DeligneLaumon.QbarCurveDuality` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.DeligneLaumon.Reduction.AffineCurveUpper` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.AdicExceptionalBase` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.AdicExceptionalCoherence` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.AdicExceptionalComposition` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.AdicExceptionalOperations` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.AdicExceptionalProjection` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.AdicExceptionalProjectionData` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.AdicExceptionalScalars` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.ArithmeticRoots` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.ChernFlagFormula` | G4 | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.CommonStageConstituentNonexceptional` | P2 | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.CommonStageFourierWeightUpper` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.CompactSupportLerayFiltration` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.CurveIntermediateExtension` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.CurveMiddleExtensionUpper` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.DlConstantFieldCharts` | G8 | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.FieldWeilShriekShiftData` | G1 | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.FiniteEtaleLisseWeilImage` | H7 | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.FiniteRegularReductionDualizing` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.FlagLocalComparison` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.FlagPullbackInjective` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.GeometricProjectiveSpaceHyperplaneCohomology` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.LocalizedFlagProduct` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.LocalizedTopChern` | E5 | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.ProjectiveBundleFormula` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.PurityChernClasses` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.QbarMiddleTStructure` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.QuasiFiniteCompactSupportWeights` | K7 | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.RationalWeilPurityNaturalityMate` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.SmoothProperPurityHypotheses` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.SupportedProjectionSplitting` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.VectorBundleThomClass` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.WeilMixedUpperBounds` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.WeilOne` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.Paper.WeilShriekShiftCompatibility` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.SixFunctors.ArbitraryFieldVerdier` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.SixFunctors.IntegralBasicOperationShift` | Z8 | Theorem type unchanged; no adaptation needed |
| `Sheaf.SixFunctors.IntegralOperationShiftData` | R1 | Theorem type unchanged; no adaptation needed |
| `Sheaf.SixFunctors.IntegralRealizationShiftCoherence` | R5 | Theorem type unchanged; no adaptation needed |
| `Sheaf.SixFunctors.QbarDualRecollement` | unclaimed | Theorem type unchanged; no adaptation needed |
| `Sheaf.SixFunctors.SystemPrimitiveComparisonShift` | D6 | Theorem type unchanged; no adaptation needed |
| `Sheaf.ZetaWeil.WeightPurityRoots` | unclaimed | Theorem type unchanged; no adaptation needed |
| `TargetsCheck` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.BoundaryTransform` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.Concentration` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.CurveTopBound` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.DegreeOne` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.ExceptionalConstituents` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierAmplitude` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierTopSupport` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.FourierWeight` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.Perverse` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.PunctualTransform` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.Purity` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.Upper` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.UpperReduction` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.Reduction.AffineCurve` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.Reduction.DirectImage` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.Reduction.MixedStalk` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.Reduction.OpenLine` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.Reduction.RealSheaves` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.Statement` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.WeilSheaf.AffineLineCohomology` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.WeilSheaf.FourierInversion` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.WeilSheaf.FourierInversion.Composite` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.WeilSheaf.FourierInversion.Delta` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.WeilSheaf.FourierInversion.OtherSections` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.WeilSheaf.FourierInversion.Vanishing` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.WeilSheaf.LowerShriekPackage` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.ZetaFunction.BettiSymmetry` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.ZetaFunction.DualityReciprocity` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.ZetaFunction.Examples` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.ZetaFunction.ExamplesCohomology` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.ZetaFunction.FinalTheorems` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.ZetaFunction.HasseWeil` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.ZetaFunction.IntegralFactors` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.ZetaFunction.IntegralFrobeniusFactors` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.ZetaFunction.LissePurity` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.ZetaFunction.RealizationIndependence` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.ZetaFunction.RelativePurity` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.ZetaFunction.SmoothProper` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.ZetaFunction.WeightSeparation` | unclaimed | Theorem type unchanged; no adaptation needed |
| `WeilConjectures.ZetaFunction.Weights` | unclaimed | Theorem type unchanged; no adaptation needed |

## Status

landed 20261020T051229-L-1602093 2026-10-20 (merge of deliver/F1/Sheaf.Paper.FieldShriekLowerBound)
