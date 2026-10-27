# AlgebraicGeometry.perfect_descent_open_union

## Reason

Restore the zero-hole module archived by `coord/rework.tsv` at
`quarantine/Sheaf/AlgebraicGeometry/PerfectDescentOpenUnion.lean`. Its public
statement needs `HasDerivedCategory`, `moduleRings`, and `PerfectDescentOnOpen`.
The archived public import names the now-withdrawn, empty Sheaf module, leaving
these declarations available only through private proof imports. The original
archive reproduces the recorded unknown-identifier error for `HasDerivedCategory`.
The authoritative predicate is now in the source library.

## Old

```lean
public import Sheaf.AlgebraicGeometry.PerfectDescentOnOpen
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.PerfectDescentOnOpen
```

The theorem signature, its docstring, and both proof bodies remain verbatim.
The replacement publicly supplies the actual statement dependency; it does not
change any definition or the meaning of a target. Redundant private imports of
`WeilConjectures.AlgebraicGeometry.DerivedCategory` and
`WeilConjectures.AlgebraicGeometry.PerfectComplex` are removed: both are already
public dependencies of the replacement module. All five DAG proof dependencies
and the existing Lean attachment remain necessary and unchanged.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.PerfectDescentOpenUnion
--allow-missing --uses AlgebraicGeometry.perfect_descent_open_union` reports zero
current library importers, since the module is quarantined. A separate search of
`quarantine/` finds the following actual parent; its dependency is retained.
Local claim records do not list that parent as held by a group.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectDescentOpenUnion | J2 (assigned) | Restore the archived theorem with its correct public statement import. |
| Sheaf.AlgebraicGeometry.PerfectComplexDescent | unclaimed in local snapshot; quarantined | Calls the same theorem with the same arguments. Its archive has an independent stale public DerivedPullback import; no parent edit is delivered. |

## Status

landed 20261024T190101-L-3913571 2026-10-24 (merge of deliver/J2/Sheaf.AlgebraicGeometry.PerfectDescentOpenUnion)
