## What changed

Proved `CategoryTheory.scalarDual_signed_assembly` with the existing statement unchanged.
Private helpers construct the scalar coordinates using Mathlib's `toSingleEquiv`, compute
the differential and precomposition in those coordinates, and transport a commuting square
through a functor. The theorem constructs the signed comparison and sheaf precomposition
maps, proves uniqueness and naturality, and proves preservation of isomorphisms and reversed
support. The construction follows all six existing DAG steps. A proof-only import of
`Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle` supplies the coordinate
equivalence. A theorem-local heartbeat setting accommodates the six-clause elaboration;
the single-file wall-clock limit is unchanged.

## Proved and sorry left

Closed: `CategoryTheory.scalarDual_signed_assembly`
(node `lem-sfb-scalar-dual-signed-assembly`), 1 of 1 original holes.
Added: none. Remaining: none. No split-off theorem or new axiom.

## No longer needed

Removed the unused direct import `Sheaf.CategoryTheory.SiteCoveringAxioms`. Retained
`Mathlib.Algebra.Category.Grp.FilteredColimits` for the sheafification instances.
No declared DAG proof dependency or unit step is bypassed. All five proof
dependencies supply the structures used by the argument. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy found. The sign is the total-Hom sign `-(-1)^q`, and the
zero-object support argument imposes no nonempty-interval or nonzero-object hypothesis.

Change record: `coord/changes/B7-scalar-dual-signed-assembly-proof-interface.md`.
The downstream check reports zero consumer modules, so no consumer adaptation is needed.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
