## What changed

Proved `CategoryTheory.spectralSequence_stationary_bottom_row` in
`Sheaf.CategoryTheory.StationaryBottomRow`, preserving its statement and imports.
The support condition kills both adjacent differentials on every page, including
outside the bottom row. Mathlib's `HomologicalComplex.isIso_iCycles` and
`HomologicalComplex.isIso_homologyπ` give the actual cycles and homology maps as
isomorphisms. The consecutive comparison is their prescribed composite with
`E.iso`. Integer induction constructs composites from page two; comparing two
pages through this common anchor proves identity, composition in arbitrary page
orders, and the required consecutive-page square. Specializing those composites
at `(n,0)` gives the bottom-row comparisons and recursion, including the empty
composite at page two. Updated the node's proof steps 3–4 and proof origin to
record the anchored construction. No public interface or definition changed.
Single-file compilation passed in 3.7 seconds; the final delivery tool checks
the cleaned proof and its axiom dependencies.

## Proved and sorry left

Closed the one existing hole:
`CategoryTheory.spectralSequence_stationary_bottom_row`
(node `lem-weil-pbc-stationary-bottom-row`).
Holes closed: 1. Holes added: 0. Sorries left: none. No statements split off.

## No longer needed

None. No imports removed, and all three declared proof dependencies are used:
`def-sp-abelian`, `def-sp-spectral-sequence`, and the Mathlib leaf
`lem-weil-pbc-short-complex-zero-homology`. No nodes or modules are withdrawn,
and the unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical error found. The common page-two anchor implements the planned
finite composites and inverse cancellation without a separate case distinction
on the order of three pages. The support calculation proves the zero differential
and isomorphism assertions for every page at least two, so the late-page bounds
are needed only to match the stated comparison interface. This also covers
negative bidegrees, the first page `r=2`, and `n=k=0` without extra hypotheses.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
