## What changed

Replaced the proof of
`AlgebraicGeometry.Etale.isIso_constantSheaf_to_open_lowerStar` in
`Sheaf.AlgebraicGeometry.NormalConstantOpenImage`. Extracted integrally closed
stalks from `hY`, applied the existing normal-open unit theorem, and used the
instances for functors preserving isomorphisms and composition of isomorphisms.
The signature, docstrings, imports, and DAG route are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.isIso_constantSheaf_to_open_lowerStar`
(node `lem-fin-normal-constant-open-image`). No holes remain in this module;
no holes or split-offs were added. The existing normal-open unit theorem is
used as the DAG prescribes; this does not claim to close its dependencies.

## No longer needed

None. The proof uses the planned `NormalConstantOpenUnit` import, the normality
definition, the pullback-of-constants isomorphism, and the direct-image functor.
No new imports, nodes, or modules were needed. LeanFinder, Loogle, and grep
searches found no shorter applicable Mathlib result.

## Where the brief, the DAG or earlier work was wrong

None. The stated proof dependencies suffice directly. No definitions or
statements changed, and the unit route is preserved.

## Second reading by S5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
