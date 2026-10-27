# Sheaf.AlgebraicGeometry.SharpSectionBasicChartData public imports

## Reason

The completed proof compares ambient fractions directly by cross multiplication,
so it does not need the affine-section-identification theorem. The statement's
Lean types need only FineFanBlowup. Remove the unused public import as required
by stage-3 pruning. Every existing declaration signature is preserved.

## Old

```lean
public import Sheaf.AlgebraicGeometry.FineFanBlowup
public import Sheaf.AlgebraicGeometry.AffineFanLocalizationSections
```

## New

```lean
public import Sheaf.AlgebraicGeometry.FineFanBlowup
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SharpSectionBasicChartData | G7 | Complete the proof; remove unused public import. |

A search of both Lean roots found no current direct importers of this module.
The DAG attachment and all existing statement dependencies are preserved; the
item is not withdrawn. No consumer needs adaptation. No target statement or
definition used by a target changes.

## Status

landed 20261026T081952-L-2112258 2026-10-26 (merge of deliver/G7/Sheaf.AlgebraicGeometry.SharpSectionBasicChartData)
