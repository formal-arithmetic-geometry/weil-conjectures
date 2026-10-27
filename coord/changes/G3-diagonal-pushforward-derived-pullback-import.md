# AlgebraicGeometry.diagonal_counit_identity

## Reason

Restore the archived module named in `coord/rework.tsv`. The recorded compiler error
is `Unknown identifier derivedPullback`, because its defining module is imported privately.
The archived public import `Sheaf.AlgebraicGeometry.DerivedPullback` now names an empty,
withdrawn module. The public theorem signature needs the canonical definition from
`WeilConjectures.AlgebraicGeometry.DerivedPullback`, so import that module publicly.

The complete theorem signature, universes, hypotheses, proof, docstring, attributes and
visibility are preserved verbatim from quarantine. No definition or mathematical statement
changes. The existing node attachment, proof steps and dependencies are preserved.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure --allow-missing
--uses diagonal_counit_identity` reports zero current downstream modules. Searching both
`lean/` and `quarantine/` finds the archived consumer below. It remains preserved, and its
application has the same arguments and result. No forced adaptation is needed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | G3 | Restored with the defining public import; identical theorem and proof. |
| Sheaf.AlgebraicGeometry.DiagonalCounitAcrossUniverses | unclaimed, quarantined in current snapshot | Identical theorem application; no adaptation. |

The local base-change dependency has already received the identical import repair in
`coord/changes/F4-diagonal-local-derived-pullback-import.md`. This delivery preserves that
proof route and all DAG dependencies. No target meaning changes and no source-library
module is edited.

## Status

landed 20261026T023209-L-530354 2026-10-26 (merge of deliver/G3/Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure)
