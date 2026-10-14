# singleComplexOpen_unit_square_factorization

## Reason

Repair the returned 83-second elaboration and preserve the importer interface.
The expensive definitions are the open-pullback comparison, the chosen derived
pullback, and exact restriction's localization functor. The proof uses their
functoriality and naturality, not their universal-property bodies. Keep them
locally irreducible and make the square calculation respect transparency.
The command-level interface checker flags local attributes and elaboration
options; none of these settings is exported.

## Old

The repository module has its original public imports and theorem signature with
`:= by sorry`. The returned sandbox had these settings before the theorem:

```lean
attribute [local irreducible] singleComplexOpenPullbackIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.unusedVariables false in
```

The returned sandbox also replaced the original public import
`Sheaf.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso` with
`Sheaf.AlgebraicGeometry.SingleComplexOpenRestrictionData`.

## New

Restore the original public imports exactly. The public signature and visibility
are unchanged. Before the theorem:

```lean
attribute [local irreducible] singleComplexOpenPullbackIso derivedPullback
  CategoryTheory.Functor.mapDerivedCategory

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
set_option linter.unusedVariables false in
```

Only the final `simpa only [...] using h` is wrapped in:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

This final conversion compares instance terms in the transported components.
The definitions' types, bodies, visibility, and global reducibility are unchanged.
The complete proof uses the proved private square helper and the shared proved
pinned counit theorem and introduces no new data choice or sorry. The shared
pinned counit theorem retains its scoped heartbeat budget;
the 60-second wall-clock file limit is unchanged.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization | S3 | Local elaboration repair; statement unchanged. |
| Sheaf.AlgebraicGeometry.SingleComplexOpenPullbackCounitHomotopyFactorization | unclaimed | Original source checked against fresh repaired artifacts; no adaptation. |

These are the textual users reported by `tools/downstream.py --uses
singleComplexOpen_unit_square_factorization`. Transitive importers retain the
original public imports and signature; local attributes do not propagate.
No target meaning or definition body changed, so no statement review reopens.

## Status

landed 20261014T130427-L-3287621 2026-10-14 (merge of deliver/S3/Sheaf.AlgebraicGeometry.SingleComplexOpenUnitSquareFactorization)
