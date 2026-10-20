## What changed

Restored `lean/Sheaf/AlgebraicGeometry/ResidueRankModelDifferential.lean` verbatim
from the quarantine path named by its rework row. The full public theorem,
`AlgebraicGeometry.Scheme.residueRankModel_differential_eval_eq_zero`, and its
private finite-rank and zero-differential helpers are complete. Their statements,
public imports, proof dependencies, and existing DAG attachment are preserved.
The restoration change record is
`coord/changes/Q3-residue-rank-model-differential-restoration.md`.

The scalar-extension complex has term dimensions equal to the fibre Betti
numbers by the free-section equivalences. The affine comparison identifies its
homology dimensions with the same numbers. The cycles inclusion therefore has
full dimension and is epic, forcing each differential to vanish. Scalar-extension
adjunction naturality then gives the stated evaluation of each coordinate.

## Proved and sorry left

Zero archived holes; zero holes closed; zero holes added; zero holes left.
The restored theorem and both private helpers have complete proofs. This is a
quarantine restoration, not a new proof or a decomposition. No theorem is split off.
Node: `lem-sc-residue-rank-model-differential`.

The restored module compiled on the project server in 9.8 seconds, after compiling
the unchanged current affine cohomology dependency in 18.6 seconds. The dependency
source was used only to refresh the sandbox compilation overlay and is not delivered.

## No longer needed

None. Every original import and all three existing DAG proof dependencies remain
needed. The library search found a parallel private finite-dimensional argument
in `WeilConjectures.RingTheory.MinimalFreeComparison`, which is inaccessible as a
public lemma and does not replace the affine fibre comparison. The current unit
route is retained; no module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The item has no archived `sorry`: its assigned work is restoration of the absent
live module after the cluster restore. The current rework row, archive, DAG proof
and preserved attachment agree. There is no numbered current return for this item.

An initial compile against the published artifacts failed because an old artifact
imported `Sheaf.AlgebraicGeometry.DerivedFiberBetti` alongside the current adopted
`WeilConjectures` definitions. Compiling the unchanged current affine cohomology
dependency in the sandbox resolves this stale-artifact conflict; no dependency or
source-library change is necessary.

Edge cases: degree-one rank zero gives no coordinates, so the conclusion is
vacuous; zero ranks in other degrees are handled by the finite-rank calculation
and cycles dimension argument. Empty affine opens have no point satisfying
`hwU`. The proof places no additional hypotheses on the degree-zero rank or on
negative-degree cohomology. The arbitrary frame `e1` is used only to construct an
R-linear coordinate map, so no compatibility with a chosen free basis is assumed.

The unchanged archived direct consumer was also checked against the restored
sandbox output. It fails during imports, before any theorem is elaborated:
`import Sheaf.AlgebraicGeometry.PerfectComplex failed, environment already contains
AlgebraicGeometry.Scheme.IsPerfect from
WeilConjectures.AlgebraicGeometry.PerfectComplex` (2.6 seconds). This is the same
kind of pre-existing stale-artifact conflict in the consumer's separate dependency
closure. No consumer proof or signature was changed. The consumer's application
was inspected directly and matches the restored theorem verbatim.

## Second reading by Q3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
