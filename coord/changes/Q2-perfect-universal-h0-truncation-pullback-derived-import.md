# AlgebraicGeometry.Scheme.perfect_universalH0_truncation_pullback_isIso

## Reason

The assigned module is restored from quarantine. Its unchanged public theorem statement
uses `derivedPullback`, but the former `Sheaf.AlgebraicGeometry.DerivedPullback`
compatibility module is now withdrawn and contains no declarations. Add the upstream
module as a public import so the existing statement elaborates and downstream users
retain the `derivedPullback` API.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

The archived module had no public import of
`WeilConjectures.AlgebraicGeometry.DerivedPullback`.

## New

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

The theorem signature and all declarations remain unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.AlgebraicGeometry.PicardBaseChangeStalkSurjective` (quarantined) | unclaimed | Its archived proof applies the unchanged theorem; no source adaptation is required. |

No live module currently imports this restored item. The DAG parent keeps the same
proof dependency.

## Status

landed 20261020T230823-L-617164 2026-10-20 (merge of deliver/Q2/Sheaf.AlgebraicGeometry.PerfectUniversalH0TruncationPullback)
