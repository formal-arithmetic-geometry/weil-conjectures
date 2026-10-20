## What changed

Withdraw Sheaf.AlgebraicGeometry.CartesianChartExchangeLeg under the explicit retirement
assignment in coord/retire-items.tsv. Both private declarations are identical to the
upstream twin after removing comments and whitespace. The upstream construction and its
complete equality proof are retained, including all signatures and public imports.
Change record: coord/changes/F2-cartesian-chart-exchange-leg-retirement.md.

Validation: lcompile.py compiled the exact withdrawal stub (0.0 s), the unchanged
upstream leg module (0.1 s), and its unchanged upstream naturality consumer (15.0 s),
with exit code 0 and no warnings. These checks use scratch copies; upstream files
are not part of the delivery.

## Proved and sorry left

Zero original holes, zero holes closed, zero holes added, zero holes left. This is the
assigned duplicate retirement, not a new theorem proof or decomposition. The existing
cartesianChartCone_leg_eq_pullback proof remains in the upstream twin. No new nodes.

## No longer needed

The duplicate module Sheaf.AlgebraicGeometry.CartesianChartExchangeLeg is withdrawn via
deleted.txt. Its public import of WeilConjectures.AlgebraicGeometry.CartesianChartClassPullback
is removed with it; that dependency remains in the upstream twin. No mathematical dependency
node is pruned. No current Lean import or DAG node references the Sheaf leg module.
The manifest's historical Sheaf.CartesianChartExchangeNaturality consumer has already
been retired; the current upstream consumer uses import all of the upstream leg module.
No consumer requires an edit, and no node's Lean attachment requires migration.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief does not identify the item as a retirement, but the current
queue and retirement manifest explicitly do. There is no sorry to close. The manifest's
consumer list is historical: its listed Sheaf consumer no longer exists. Its replacement
WeilConjectures.AlgebraicGeometry.CartesianChartExchangeNaturality already uses the twin.
The existing DAG attachment of lem-sc-cartesian-chart-exchange-naturality points at that
upstream consumer. All mathematical statements and the unit route remain unchanged.

Searches were run with msearch.py: LeanFinder for cone legs as canonical pullback lifts,
Loogle for CategoryTheory.Limits.pullback.lift, and grep for lift_fst/lift_snd theorem
spellings. Loogle found pullback.lift and its projection equations; the decisive exact
match is the upstream twin, checked directly. No new mathematical statement is needed.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
