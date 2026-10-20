# AlgebraicGeometry.exists_open_smooth_bertiniMember proof commands

## Reason

Preflight classifies the additional namespace openings and local irreducibility
attributes as an interface change. These commands keep module and projective-space
constructions folded during elaboration of the private proof helpers. They do not
change a public declaration, definition, target, or exported import.

## Old

```lean
open CategoryTheory CategoryTheory.Limits Opposite
```

There was no `open Scheme.Modules` and no local irreducibility attribute in this file.

## New

```lean
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open Scheme.Modules
attribute [local irreducible] tensorPullback tensorPullbackObj
attribute [local instance] coordinateReindex_isIso
attribute [local irreducible] ProjectiveSpace.homOfIsFreeGenerator
```

The attributes are local to the file's section. The namespace openings affect name
resolution in this file. The reindexing isomorphism is a private theorem, supplied as
an instance only inside the file's `noncomputable section`; it has no global instance registration.
All three original definitions and the public theorem signature are verbatim unchanged.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.BertiniSmoothMember` listed the modules
below. Every effect is identical: the public statements and the definitions they use
are unchanged, so there is no consumer adaptation and no target meaning changes.
Holder information is immaterial here: none of these modules is edited by this packet.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ArithmeticRoots | not queried; no edit | unchanged; no adaptation |
| Sheaf.Paper.WeilOne | not queried; no edit | unchanged; no adaptation |
| Sheaf.ZetaWeil.WeightPurityRoots | not queried; no edit | unchanged; no adaptation |
| TargetsCheck | not queried; no edit | unchanged; no adaptation |
| WeilConjectures | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.AlgebraicGeometry.Bertini | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.DirectImage | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RealSheaves | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RelativeAffineLine | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.DeligneLaumon.Reduction.RelativeLineStep | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.EtaleCohomology.Purity.RealSheaves.SheafWeightOperations | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.Statement | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.BettiSymmetry | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.DualityReciprocity | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.Examples | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.ExamplesCohomology | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.FinalTheorems | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.HasseWeil | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.IntegralFactors | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.IntegralFrobeniusFactors | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.LissePurity | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.RealizationIndependence | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.RelativePurity | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.SmoothProper | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.WeightSeparation | not queried; no edit | unchanged; no adaptation |
| WeilConjectures.ZetaFunction.Weights | not queried; no edit | unchanged; no adaptation |

## Status

landed 20261020T051212-L-1593985 2026-10-20 (merge of deliver/E5/Sheaf.AlgebraicGeometry.BertiniSmoothMember)
