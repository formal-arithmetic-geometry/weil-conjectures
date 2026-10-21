## What changed

Filled the two theorem proofs in `Sheaf.Paper.SectionLocalComparisonData`.
`invertibleOnSource` applies `IsUnit.map` to `v.appTop.hom` and uses
`map_natCast`. `noetherianSource` applies the existing proved source-library
lemma `AlgebraicGeometry.isNoetherian_of_locallyOfFiniteType`.
The declarations, definitions, docstrings and imports are unchanged.

Searches: LeanFinder for finite-type permanence of Noetherianity, Loogle for
`IsUnit.map`, and ripgrep across Mathlib and both library roots. The existing
source theorem has exactly the required finite-type/quasi-compact hypotheses.
Both proofs apply uniformly to empty schemes; no nonemptiness or positivity
hypothesis was added. The entire module compiled cleanly through `lcompile.py`.

## Proved and sorry left

Closed 2 of 2 original holes:
- `AlgebraicGeometry.Etale.SectionLocalDualizingComparisons.invertibleOnSource`.
- `AlgebraicGeometry.Etale.SectionLocalDualizingComparisons.noetherianSource`.

Both belong to `def-trf-section-local-comparison-data`.
Remaining holes in the item: none. Added holes: none. Split-off statements: none.
This closes the local well-definedness obligations; the definitions continue to
use the existing comparison infrastructure and its existing proof dependencies.

## No longer needed

None. All four existing public imports support the unchanged definitions and
comparison interfaces. No node or module is withdrawn, and no unit route changes.

## Where the brief, the DAG or earlier work was wrong

No error found. The elementary domain obligations described in the existing
docstrings are already supported by the library. No change record or node edit
is needed for these two proof-only replacements.

## Second reading by H2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
