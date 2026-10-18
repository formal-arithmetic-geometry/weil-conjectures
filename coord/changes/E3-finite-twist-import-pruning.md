# etaleFiniteTwistPullback: remove the unused general ringed-topos public import

## Reason

The statement uses the source library's concrete etale derived tensor and ordinary
module categories. Its proof now constructs the prescribed derived comparison from
that source API. The former general ringed-topos export introduces unrelated holed
infrastructure and supplies no symbol needed by this declaration. Only its import is
removed. Every existing declaration signature, definition, and visibility stays identical.

## Old

```lean
public import Sheaf.Paper.RingedTopoiDerivedTensorPullback
```

## New

The import above is removed. The remaining public imports supply the same objects in
the unchanged theorem signature; the concrete source derived tensor imports remain.
The exact theorem signature remains the original `etaleFiniteTwistPullback` signature
recorded verbatim in `lem-asd-etale-finite-twist-pullback.json`.

## Users

The read-only downstream query lists the following modules. None is adapted. The only
direct importer is `WeilConjectures.WeilSheaf.FourierInversion.OtherSections`; it uses
none of the declarations exported solely by the removed import and was copied unchanged
for compilation against the sandbox, then removed from the delivery. There are no
semantic changes to definitions used by a target.

| module | group holding it | effect |
| --- | --- | --- |
| TargetsCheck WeilConjectures WeilConjectures.DeligneLaumon.AffineLine.AffineCurveUpper WeilConjectures.DeligneLaumon.AffineLine.Concentration WeilConjectures.DeligneLaumon.AffineLine.ConstantTwist WeilConjectures.DeligneLaumon.AffineLine.DegreeOne WeilConjectures.DeligneLaumon.AffineLine.DualNonexceptional WeilConjectures.DeligneLaumon.AffineLine.Exactness WeilConjectures.DeligneLaumon.AffineLine.FourierWeight WeilConjectures.DeligneLaumon.AffineLine.MiddleExtension WeilConjectures.DeligneLaumon.AffineLine.Perverse WeilConjectures.DeligneLaumon.AffineLine.Purity WeilConjectures.DeligneLaumon.AffineLine.RealifiedKernel WeilConjectures.DeligneLaumon.AffineLine.Upper WeilConjectures.DeligneLaumon.AffineLine.UpperReduction WeilConjectures.DeligneLaumon.AffineLine.ZeroExtension WeilConjectures.DeligneLaumon.Reduction.AffineCurve WeilConjectures.DeligneLaumon.Reduction.DirectImage WeilConjectures.DeligneLaumon.Reduction.MixedStalk WeilConjectures.DeligneLaumon.Reduction.OpenLine WeilConjectures.DeligneLaumon.Reduction.QuasiFiniteMixed WeilConjectures.DeligneLaumon.Reduction.RealSheaves WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep WeilConjectures.Statement WeilConjectures.WeilSheaf.FourierInversion WeilConjectures.WeilSheaf.FourierInversion.Composite WeilConjectures.WeilSheaf.FourierInversion.Delta WeilConjectures.WeilSheaf.FourierInversion.OtherSections WeilConjectures.WeilSheaf.FourierInversion.Vanishing WeilConjectures.ZetaFunction.BettiSymmetry WeilConjectures.ZetaFunction.DualityReciprocity WeilConjectures.ZetaFunction.Examples WeilConjectures.ZetaFunction.ExamplesCohomology WeilConjectures.ZetaFunction.FinalTheorems WeilConjectures.ZetaFunction.HasseWeil WeilConjectures.ZetaFunction.IntegralFactors WeilConjectures.ZetaFunction.IntegralFrobeniusFactors WeilConjectures.ZetaFunction.RealizationIndependence WeilConjectures.ZetaFunction.RelativePurity WeilConjectures.ZetaFunction.SmoothProper WeilConjectures.ZetaFunction.WeightSeparation WeilConjectures.ZetaFunction.Weights | unchanged, no adaptation | existing signatures and definitions unchanged |

## Status

landed 20261018T071147-L-1666607 2026-10-18 (merge of deliver/E3/Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback)
