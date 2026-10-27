## What changed

Filled the proof of `AlgebraicGeometry.existsUnique_coordinateQuotientGrading` in
`Sheaf.RingTheory.CoordinateQuotientGrading`, with all existing signatures,
definitions and public imports unchanged. Map the polynomial direct-sum
components into their specified quotient image submodules. Homogeneity makes
this additive map vanish on the ideal, so it descends to the quotient. Check
both inverse identities against the fixed sum map, and verify the unit and
multiplication on the image pieces. The resulting projections have the required
formula by construction. Mathlib's subsingleton theorem for decompositions
proves uniqueness. No additional assumptions exclude the zero quotient.

Searches used LeanFinder (quotients by homogeneous ideals), Loogle
(`DirectSum.IsInternal`), the launcher grep search, and direct `rg` searches in
Mathlib, WeilConjectures and Sheaf. The useful existing API is
`DirectSum.map`, `QuotientAddGroup.lift`,
`DirectSum.Decomposition.ofAddHom`, and the subsingleton instance for
`DirectSum.Decomposition`. No extra statement module is needed.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.existsUnique_coordinateQuotientGrading`
(node `def-sfb-coordinate-quotient-grading`). No holes added or split off.
No `sorry` remains in the delivered module.

## No longer needed

None. No imports, nodes or modules withdrawn. The node has no planned proof
dependencies; the proof implements the existing theorem's documented argument
using Mathlib. Existing public imports are preserved as part of the interface.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was needed. The definition node has no numbered
proof steps, but the theorem's docstring gives the quotient-decomposition
argument followed here. The unit route is unchanged.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
