# Sheaf.AlgebraicGeometry.ScalarAbelianPullbackSquare

## Reason

The Sheaf compatibility module is a retired duplicate. The adopted source module
`WeilConjectures.AlgebraicGeometry.ScalarAbelianPullbackSquare` is the sole declaration
source and contains the complete theorem proof. The quarantined Sheaf implementation
also redeclared declarations already supplied by the adopted source and failed with a
duplicate-environment error after the upstream sync.

## Old

```lean
module

public import WeilConjectures.AlgebraicGeometry.ScalarAbelianPullbackSquare
```

The prior quarantined copy additionally imported Sheaf scalar-factorization modules
and redeclared the source declarations.

## New

The Sheaf path is withdrawn and replaced by the delivery tool's empty module stub:

```lean
module

/-! Withdrawn: no declarations remain. -/
```

The adopted `WeilConjectures` source file and its public declarations are unchanged.

## Users

| module | group holding it | effect |
|---|---|---|
| none | none | `tools/downstream.py --direct --allow-missing` reports zero importers |

## Status

landed 20261020T221242-L-4163988 2026-10-20 (merge of deliver/M1/Sheaf.AlgebraicGeometry.ScalarAbelianPullbackSquare)
