## What changed

Restored `Sheaf.Paper.CoefficientTowerGeometricComposition` from its exact quarantine
source, as assigned by `coord/rework.tsv`. The archived module compiles against the
current restored dependencies. Scoped its sheafification instance removal inside a
section, replacing the final global high-priority re-registration by section closure.
This repairs the restoration/proof environment; it does not prove the theorem.

All declaration text, docstrings, public and private imports, universes and
normalization equations are otherwise unchanged. The original Lean attachment and
all DAG dependencies are preserved. Change record:
`coord/changes/E3-geometric-calculus-quarantine-restoration.md`.

Validation: the exact archive compiled in 3.3 seconds; the restored scoped version
compiled in 3.4 seconds through `lcompile.py`. There are no overlength Lean lines.
The unchanged archived consumer `CoefficientTowerShriekCalculus` was also attempted;
its dependency closure failed on missing `Mathlib.olean` before elaboration. No
consumer compatibility is claimed from that failed attempt.

## Proved and sorry left

This is the assigned quarantine restoration, not a proof or a decomposition.
Closed: 0 of the 1 original holes. Added: 0 holes relative to the quarantine source.
Split off: 0. The one retained hole is
`AlgebraicGeometry.ProEtale.SpTowerCalculus.geometric_calculus`
(node `lem-sp-tower-geometric-composition`), with its original complete proof plan
and source in its docstring and node. No definition contains a proof hole.

## No longer needed

None. No imports, declarations, nodes, modules or parent dependencies are pruned.
The node's full proof-dependency route is retained, including the quarantined
parent's planned use of this theorem. No quarantined source is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item is an assigned rework restoration: absence of the Lean source did not mean
its statement or parent dependency had been withdrawn. The archived source now
compiles after dependency restorations. Its global instance removal/re-registration
is unnecessary for importers; the section-scoped version retains the intended local
proof context and restores the inherited registration on exit.

The theorem's original mathematical proof remains unfinished. Search via LeanFinder,
Loogle (`leftAdjointUniq`) and library grep found no direct theorem supplying its
whole combination of normalized tower composition and etale calculus. No new
statement or proof route is introduced by this repair.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
