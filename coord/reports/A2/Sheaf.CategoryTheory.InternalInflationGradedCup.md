## What changed

Restored `lean/Sheaf/CategoryTheory/InternalInflationGradedCup.lean` from the quarantine
archive named by its current `coord/rework.tsv` row. The archived source reproduces
the missing `BraidedCategory (DerivedCategory (Modules A))` error at line 145.
Select upstream `DerivedCategory.braidedCategory'` as a local instance in a nested
section around the existing profinite-group assertions. This fixes elaboration of
the braided inflation statement with the canonical Koszul braidings on the base
and action derived categories. All archived declarations, statements, definition
bodies, docstrings and imports are preserved. The local instance does not escape
its section. No other modules are adapted.

Change record: `coord/changes/A2-internal-inflation-canonical-braiding.md`.
The original archive failed compilation; the repaired module compiled cleanly.

## Proved and sorry left

Assigned quarantine repair completed. Holes closed: 0 of 4. Holes added: 0.
No decomposition or new statements. The four retained holes, all attached to
`lem-sfb-internal-inflation-graded-cup`, are:

- `CategoryTheory.CondensedDerivedRestriction.internalInflationStructure`
- `CategoryTheory.CondensedDerivedRestriction.inflationPhiIdentity`
- `CategoryTheory.CondensedDerivedRestriction.inflationCupTranspose`
- `CategoryTheory.CondensedDerivedRestriction.internalInflationGradedCup`

## No longer needed

None. No imports, declarations, nodes or modules are pruned or withdrawn. The
quarantine archive and its Lean attachment remain preserved. Scanning both active
and quarantined Lean sources finds no current direct importers. The DAG parent
`lem-sfb-internal-bar-character-roof-cup` still requires this node, and that dependency
and the unit route are preserved.

## Where the brief, the DAG or earlier work was wrong

The item source is currently in quarantine rather than `lean/`, as documented by
the rework row. Its archived context assumed a globally inferred derived braiding.
Current upstream intentionally exposes the canonical derived braiding as a definition
for local selection. The archived mathematical assertions and their proof plans
need no change. The listed repair is a compilation repair, not closure of one of
the four existing theorem holes.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
