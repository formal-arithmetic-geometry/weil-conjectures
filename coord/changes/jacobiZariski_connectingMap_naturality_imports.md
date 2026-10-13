# Algebra.jacobiZariski_connectingMap_naturality imports

## Reason

The complete proof needs only Mathlib. Remove the unused public import of
Sheaf.RingTheory.JacobiZariskiHomologySequence to prune the proof's dependency closure.
The theorem's signature and visibility are identical. No definition changed.

## Old

```lean
public import Sheaf.RingTheory.JacobiZariskiHomologySequence
public import Mathlib.RingTheory.Extension.ExtendScalars
```

## New

```lean
public import Mathlib.RingTheory.Extension.ExtendScalars
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.RingTheory.DifferentialsInjectiveOfH1CotangentInjectiveCharP | unclaimed | Already directly imports JacobiZariskiHomologySequence; no adaptation. |
| Sheaf.RingTheory.GeometricallyRegularH1Injective | unclaimed | Already directly imports JacobiZariskiHomologySequence; no adaptation. |

Both direct importers were inspected. Their statements use the retained Mathlib API;
their direct imports retain the removed public import's declarations. No target statement
or definition used by a target changes. No forced adaptation is included.

## Status

landed 20261013T060420-L-583790 2026-10-13 (merge of deliver/J3/Sheaf.RingTheory.JacobiZariskiConnectingMapNaturality)
