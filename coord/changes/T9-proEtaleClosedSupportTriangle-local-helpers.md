# Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle proof-local commands

## Reason

The proof needs private coefficient comparisons and local typeclass evidence. The delivery
checker conservatively treats added section variables, `open` and local instance attributes as
interface commands. This record accounts for these commands. All helper class proofs are
private theorems, registered only inside the proof section. No global instance is added.
No existing declaration type, visibility, public import, notation or definition changes.
No target meaning review is reopened. No other library module is changed.

## Old

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.ProEtale
```

There was no helper section. The main theorem had its existing signature and a `sorry` proof.

## New

The existing commands above are unchanged. The added proof section begins with:

```lean
section

open Opposite

universe uC vC
```

Its private helper theorems are registered locally, immediately after their declarations:

```lean
attribute [local instance] finiteCoefficientRestriction_isEquivalence
attribute [local instance] finiteCoefficientRestriction_additive
attribute [local instance] finiteModulesGroth
attribute [local instance] finitePull_limits
attribute [local instance] finitePull_colimits
attribute [local instance] finitePush_limits
```

Its geometric variables are:

```lean
variable {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
  (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
  (hij : IsCompl (Set.range i.base) (Set.range j.base))
  (A : Type (u + 1)) [Ring A] [Finite A] [TopologicalSpace A] [DiscreteTopology A]
```

The main theorem repeats its existing explicit binders. The added section ends with `end`
before `end AlgebraicGeometry.ProEtale`, restoring the prior scope and instance environment.
All new definitions and theorems are private. The existing public zero-map instance is unchanged.

## Users

The completed command `python3 tools/downstream.py
Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle --uses
exists_proEtale_closedSupportTriangle` listed these 119 transitive importers. Its textual uses
check found only the declaration in the item itself. Every existing public signature and
public import remains unchanged, and the helper attributes are section-local. Thus every
importer's statements keep exactly their meanings and no adaptation is necessary.
`not adapted` in the holder column indicates that no downstream claim is exercised here.
No module belonging to another group is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.Reduction.AffineCurveUpper | not adapted | unchanged; no adaptation |
| Sheaf.DeligneLaumon.Reduction.Composition | not adapted | unchanged; no adaptation |
| Sheaf.Paper.AdicClosedConstructible | not adapted | unchanged; no adaptation |
| Sheaf.Paper.AdicPurityExceptionalReduction | not adapted | unchanged; no adaptation |
| Sheaf.Paper.AdicPurityFiniteTensor | not adapted | unchanged; no adaptation |
| Sheaf.Paper.AdicPurityObjects | not adapted | unchanged; no adaptation |
| Sheaf.Paper.AdicPurityRootComparisons | not adapted | unchanged; no adaptation |
| Sheaf.Paper.AdicPuritySourceReduction | not adapted | unchanged; no adaptation |
| Sheaf.Paper.AdicPurityTwistReduction | not adapted | unchanged; no adaptation |
| Sheaf.Paper.AdicSmoothDualizingComplexes | not adapted | unchanged; no adaptation |
| Sheaf.Paper.ArithmeticRoots | not adapted | unchanged; no adaptation |
| Sheaf.Paper.BoundedConstructibleHomFiniteness | not adapted | unchanged; no adaptation |
| Sheaf.Paper.CohomologicalSmoothEtaleLocality | not adapted | unchanged; no adaptation |
| Sheaf.Paper.CommonStageConstituentNonexceptional | not adapted | unchanged; no adaptation |
| Sheaf.Paper.CommonStageFourierWeightUpper | not adapted | unchanged; no adaptation |
| Sheaf.Paper.CurveIntermediateExtension | not adapted | unchanged; no adaptation |
| Sheaf.Paper.CurveMiddleExtensionUpper | not adapted | unchanged; no adaptation |
| Sheaf.Paper.DualizingObjectPurity | not adapted | unchanged; no adaptation |
| Sheaf.Paper.ExtensionByZeroPunctual | not adapted | unchanged; no adaptation |
| Sheaf.Paper.FiniteCoefficientSmoothPurity | not adapted | unchanged; no adaptation |
| Sheaf.Paper.FiniteFieldInternalHomFiniteness | not adapted | unchanged; no adaptation |
| Sheaf.Paper.FiniteReductionAffineOrientation | not adapted | unchanged; no adaptation |
| Sheaf.Paper.FiniteReductionChartCalculus | not adapted | unchanged; no adaptation |
| Sheaf.Paper.FiniteReductionComparisons | not adapted | unchanged; no adaptation |
| Sheaf.Paper.FiniteReductionOfPurity | not adapted | unchanged; no adaptation |
| Sheaf.Paper.FiniteReductionRootCharts | not adapted | unchanged; no adaptation |
| Sheaf.Paper.FiniteSmoothPullbackExchange | not adapted | unchanged; no adaptation |
| Sheaf.Paper.FiniteTorInternalHomAnyField | not adapted | unchanged; no adaptation |
| Sheaf.Paper.FiniteTorStability | not adapted | unchanged; no adaptation |
| Sheaf.Paper.FixedStalkIdentificationReduction | not adapted | unchanged; no adaptation |
| Sheaf.Paper.FourierTraceFormula | not adapted | unchanged; no adaptation |
| Sheaf.Paper.PurAdicReconstruction | not adapted | unchanged; no adaptation |
| Sheaf.Paper.PurityCompositionCoherence | not adapted | unchanged; no adaptation |
| Sheaf.Paper.PurityDiagonalDualizingObject | not adapted | unchanged; no adaptation |
| Sheaf.Paper.PurityDncInvariance | not adapted | unchanged; no adaptation |
| Sheaf.Paper.QuasiFiniteCompactSupportWeights | not adapted | unchanged; no adaptation |
| Sheaf.Paper.RationalSmoothPurityCanonical | not adapted | unchanged; no adaptation |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | not adapted | unchanged; no adaptation |
| Sheaf.Paper.RegularImmersionPurityComparison | not adapted | unchanged; no adaptation |
| Sheaf.Paper.SmoothPurityMap | not adapted | unchanged; no adaptation |
| Sheaf.Paper.SmoothTrace | not adapted | unchanged; no adaptation |
| Sheaf.Paper.TraceFormulaTopologicalInvariance | not adapted | unchanged; no adaptation |
| Sheaf.Paper.WeilFourierInversion | not adapted | unchanged; no adaptation |
| Sheaf.Paper.WeilFourierPlancherel | not adapted | unchanged; no adaptation |
| Sheaf.Paper.WeilOne | not adapted | unchanged; no adaptation |
| Sheaf.Paper.ZlShriekComposition | not adapted | unchanged; no adaptation |
| Sheaf.SecSmoothPurity.FiniteGeneralRing | not adapted | unchanged; no adaptation |
| Sheaf.SecSmoothPurity.SmoothPurityNaturality | not adapted | unchanged; no adaptation |
| Sheaf.ZetaWeil.WeightPurityRoots | not adapted | unchanged; no adaptation |
| TargetsCheck | not adapted | unchanged; no adaptation |
| WeilConjectures | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Concentration | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.DegreeOne | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Exactness | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.FourierWeight | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.LocalDuality | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Perverse | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Purity | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.RealPushforward | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.TraceEnergy | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.Upper | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.UpperReduction | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.AffineCurve | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.CompactSupport | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FibreCohomology | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteDirectImage | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMap | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FiniteMiddleExtension | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.FormalSteps | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.MixedStalk | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.OpenLine | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteStalk | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteVanishing | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteWeights | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RealCurve | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not adapted | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not adapted | unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.BoundaryPurity | not adapted | unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Chebotarev | not adapted | unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.DetWeightOperations | not adapted | unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.MiddleExtension | not adapted | unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Purity | not adapted | unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Rankin | not adapted | unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.Semicontinuity | not adapted | unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafBoundaryPurity | not adapted | unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafSemicontinuity | not adapted | unchanged; no adaptation |
| WeilConjectures.FourierTransform.Perverse | not adapted | unchanged; no adaptation |
| WeilConjectures.SixFunctors.Etale.Perverse.Operations | not adapted | unchanged; no adaptation |
| WeilConjectures.Statement | not adapted | unchanged; no adaptation |
| WeilConjectures.WeilSheaf.Curve | not adapted | unchanged; no adaptation |
| WeilConjectures.WeilSheaf.CurveEndpoints | not adapted | unchanged; no adaptation |
| WeilConjectures.WeilSheaf.LFunction | not adapted | unchanged; no adaptation |
| WeilConjectures.WeilSheaf.LowerShriekFunctoriality | not adapted | unchanged; no adaptation |
| WeilConjectures.WeilSheaf.RealPurity | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.BettiSymmetry | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.CohomologicalFamily | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.DualityReciprocity | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.Examples | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.FinalTheorems | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.HasseWeil | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.IntegralFactors | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.Rationality | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.RealizationIndependence | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.RelativePurity | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.SmoothProper | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.TraceFormula | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.WeightSeparation | not adapted | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.Weights | not adapted | unchanged; no adaptation |

## Status

landed 20261019T005432-L-2771059 2026-10-19 (merge of deliver/T9/Sheaf.AlgebraicGeometry.ProEtaleClosedSupportTriangle)
