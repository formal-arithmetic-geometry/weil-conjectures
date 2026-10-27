## What changed

Proved `AlgebraicGeometry.ProjectiveLine.bijective_overlap_laurent` from the existing
monomial-basis bijection in `ProjectiveSpace.TwistSections`. Private helpers identify
integer exponents with degree-zero two-coordinate exponent vectors, compute the
restriction of the concrete ratio unit, and compare its positive and negative powers
with the basis monomials. Reindexing finitely supported coefficients then identifies
Laurent evaluation with that bijection. Restriction between the two equal descriptions
of the overlap gives the theorem with its original signature.

The item module is the only Lean file changed. Its existing imports and public
interface are preserved. Updated its node's proof and proof origin to describe the
implemented argument.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.ProjectiveLine.bijective_overlap_laurent`
(node `lem-sfb-projective-line-overlap-laurent-coordinates`).
Original holes: 1. Closed: 1. Added: 0. Remaining: 0. No decomposition.

Validation: `lcompile.py` compiled the module cleanly in 6.3 seconds, with no warnings.
The delivery tool runs the final mechanical checks and axiom probe.

## No longer needed

None. All three existing imports are used. The stated dependency nodes are retained.
No new statement modules, withdrawn modules, or split-off holes.

## Where the brief, the DAG or earlier work was wrong

The original DAG described constructing an inverse by homogeneous fractions.
The source library already has the stronger monomial-basis bijection, so an explicit
inverse is unnecessary: reindex that proved bijection and compute the concrete
ratio on each monomial instead. The theorem's meaning and the unit route are unchanged.

## Second reading by G4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
