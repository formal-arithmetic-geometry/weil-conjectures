# AlgebraicGeometry.diagonal_baseChange_upperShriek_local

## Reason

Restore the module from the archive named in `coord/rework.tsv`. The recorded compiler
failure is `Unknown identifier derivedPullback`, with Lean reporting that the declaration
is imported privately. `Sheaf.AlgebraicGeometry.DerivedPullback` is now an empty withdrawn
module. The definition used by the public theorem signature lives in
`WeilConjectures.AlgebraicGeometry.DerivedPullback`, so import that module publicly.

The theorem's complete signature, universes, proof, docstring, and visibility are preserved
verbatim from the quarantine source. No definition or mathematical statement changes.
The node's Lean attachment and both recorded proof dependencies remain unchanged.

## Old

```lean
public import Sheaf.AlgebraicGeometry.DerivedPullback
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
```

## Users

`tools/downstream.py` with `--allow-missing --uses diagonal_baseChange_upperShriek_local`
reports zero current downstream modules. A separate search of `quarantine/` finds the
following archived consumer, which must be preserved rather than treated as withdrawn.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories | F4 | Restore with the defining public import; no theorem change. |
| Sheaf.AlgebraicGeometry.DiagonalPushforwardStructure | unclaimed, quarantined | Its call at line 145 has the same arguments and result; no adaptation. |

The archived consumer independently has the obsolete public import; its eventual restoration
must repair that import in its own assignment. This delivery does not restore that module.
The added public import exposes the same canonical `derivedPullback` used by the preserved
signature. There is no target-meaning change and no forced consumer adaptation.

## Status

landed 20261025T204545-L-2974095 2026-10-25 (merge of deliver/F4/Sheaf.AlgebraicGeometry.DiagonalBaseChangeLocalDerivedCategories)
