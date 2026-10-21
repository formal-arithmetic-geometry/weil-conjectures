# Sheaf.Algebra.Homology.FlatScalarCyclicResolution public imports

## Reason

The proof computes tensor using the published fixed-factor K-flat comparison.
No statement or definition in this module uses the ringed projection-mate API.
Removing its public import prunes that unused dependency.

## Old

```lean
public import Sheaf.Paper.ProjectionMateExact
```

## New

The public import above is removed. The proof instead privately imports
`Sheaf.Algebra.Homology.KFlatFixedTensorTriangulated`. Every existing declaration,
its visibility and its signature stay unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| No current Lean importers | none | No existing importing module needs adaptation. |

A direct import search of both library roots found no importers. DAG parents
still need this item's unchanged statement; no node or item is withdrawn.
`tools/downstream.py` reports zero downstream modules; its declaration-use scan
finds only the declaration in this module itself.

## Status

landed 20261021T120706-L-3933669 2026-10-21 (merge of deliver/U1/Sheaf.Algebra.Homology.FlatScalarCyclicResolution)

The complete proof compiles without warnings; independent delivery review is pending.
