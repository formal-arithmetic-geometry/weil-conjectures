# BertiniSections proof imports and local proof commands

## Reason

Prune unused public proof dependencies after proving the kernel, basis and generation assembly.
The added helpers are private. The added namespace openings and scoped transparency options
serve only those proofs; no definition or theorem statement is changed.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.InvertibleGeneratingSectionsFibre
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceFunctorOfPoints
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import Sheaf.AlgebraicGeometry.ProjectiveMorphismChartPreimage
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceStandardCharts
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.AmpleTwistGlobalGeneration
public import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
public import WeilConjectures.AlgebraicGeometry.CoherentKernelCokernelLocallyNoetherian
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
public import WeilConjectures.AlgebraicGeometry.ProjectiveAmpleInvertible
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProjectiveSpaceHomOfGeneratingSections
public import WeilConjectures.AlgebraicGeometry.Modules.VeryAmple
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.AlgebraicGeometry.ClosedImmersionIdealTensorSections
import Sheaf.DeligneLaumon.BertiniImmersionAux
import WeilConjectures.AlgebraicGeometry.Modules.HomSection
import WeilConjectures.AlgebraicGeometry.Modules.HilbertPolynomial
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
```

The source additionally opens `Scheme.Modules MonoidalCategory Opposite` locally and uses
scoped backward definitional-equality options on its private helpers and main proof.
Two private proved site-instance lemmas cache `HasWeakSheafify` and
`WEqualsLocallyBijective`; their instance attributes are local to this file. Profiling
identified their repeated inference as the main elaboration cost. No public notation,
instance, attribute or variable binder is added.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.BertiniSections | U7 | Signature unchanged; proof imports removed or added. No consumer edit required. |
| Sheaf.Paper.ArithmeticRoots | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| Sheaf.Paper.WeilOne | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| Sheaf.ZetaWeil.WeightPurityRoots | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| TargetsCheck | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.AlgebraicGeometry.Bertini | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.Statement | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.ZetaFunction.BettiSymmetry | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.ZetaFunction.DualityReciprocity | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.ZetaFunction.Examples | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.ZetaFunction.ExamplesCohomology | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.ZetaFunction.FinalTheorems | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.ZetaFunction.HasseWeil | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.ZetaFunction.IntegralFactors | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.ZetaFunction.LissePurity | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.ZetaFunction.RealizationIndependence | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.ZetaFunction.RelativePurity | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.ZetaFunction.SmoothProper | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.ZetaFunction.WeightSeparation | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |
| WeilConjectures.ZetaFunction.Weights | unclaimed | Signature unchanged; proof imports removed or added. No consumer edit required. |

## Status

landed 20261020T131158-L-1254126 2026-10-20 (merge of deliver/U7/Sheaf.DeligneLaumon.BertiniSections)
