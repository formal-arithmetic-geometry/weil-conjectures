# WeilConjectures.sfOrientedCancellation_of_evaluationLaws

## Reason

The existing private oriented_cancellation already proves the generic closed-category
argument used by the node. Export a proved wrapper so the parent can use it on the
isomorphic single-complex presentation of the orientation line. No existing
signature or definition changes. The module is unclaimed.

## Old

The generic result is private: `oriented_cancellation` in
`Sheaf.Paper.OrientedDoubleHomCancellation`. Its proof and signature are unchanged.
The old import, verbatim, was:

```lean
import Sheaf.Paper.CoefficientEvaluationNaturality
```

## New

```lean
theorem sfOrientedCancellation_of_evaluationLaws
    (laws : SfCoefficientEvaluationLaws T s) (L I : B) :
    OrientedDoubleHomCancellation T s L I :=
  oriented_cancellation T s laws L I
```

The import becomes:

```lean
public import Sheaf.Paper.CoefficientEvaluationNaturality
```

The existing coefficient-evaluation import is public because it occurs in this
new public theorem's signature. The new wrapper declaration is recorded in the
cancellation node's Lean attachment. No target meaning changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.OrientedDoubleHomCancellation | unclaimed | Adds the proved wrapper and exposes its signature dependency; existing consumers and declarations unchanged. |
| Sheaf.Paper.OrientedPerfectDuality | H9 | New proof invokes the generic result for its actual orientation line. |

`tools/downstream.py Sheaf.Paper.OrientedDoubleHomCancellation` reports no existing
importers; the parent acquires this dependency in this delivery. No forced adaptations.

## Status

landed 20261025T123118-L-1833257 2026-10-25 (merge of deliver/H9/Sheaf.Paper.OrientedPerfectDuality)
