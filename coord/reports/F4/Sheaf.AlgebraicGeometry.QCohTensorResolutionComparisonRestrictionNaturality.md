## What changed

Restored `Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonRestrictionNaturality`
from its quarantined failure by making it a compatibility import of the complete, existing
source-library theorem. The archived file is preserved. The archive's imports were tested
and failed with a duplicate `AlgebraicGeometry.tensorResolutionSiteModules` declaration;
the restored module compiles in 2.0 seconds.

Updated the existing node's Lean attachment to the canonical source module and its exact
signature. A text comparison establishes that its signature differs from the archive only
by `IsKFlatTensor` versus `IsAcyclicTensorKFlat`; both define the same acyclic-tensor
condition, with the same universes. The entire proof body is verbatim identical. All
mathematical dependencies and the unit route are retained.

Change record: `coord/changes/F4-qcoh-tensor-restriction-restore.md`.

## Proved and sorry left

This is a zero-hole rework item: the archive contains 0 `sorry`s; the restored compatibility
module adds 0. Holes closed: none. Holes added: none. Split-off statements: none.

`AlgebraicGeometry.tensorResolutionComparison_restriction` is already fully proved in
`WeilConjectures.AlgebraicGeometry.QCohTensorResolutionComparisonRestrictionNaturality`
(node `new-h4-qcoh-tensor-comparison-restriction-naturality`). Through the restored public
import, `#check` succeeds and `#print axioms` reports only `propext`, `Classical.choice`,
`Quot.sound`. No `sorry` is reachable from this theorem.

## No longer needed

Removed direct imports of
`Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonNaturality` and
`Sheaf.AlgebraicGeometry.QCohTensorResolutionComparisonFormula` from the quarantined module.
The replacement imports the canonical source restriction theorem, whose existing proof
still uses the four tensor squares, K-flat quasi-isomorphism invariance, homology zigzag,
and comparison hom formula. No mathematical nodes or modules are pruned: those dependencies
remain needed by the source proof. No upstream declaration, module, proof, or public import
is removed or modified. No new module is withdrawn, and `deleted.txt` is unnecessary.

## Where the brief, the DAG or earlier work was wrong

The item is listed as a quarantined global-build repair, rather than an unfinished proof.
Its preserved proof became unusable because one dependency now re-exports source-library
comparison declarations while another still supplies their duplicate Sheaf versions.
The full theorem, including all six K-flat hypotheses and all three compatibility squares,
already exists with a complete proof in the source tree. Reusing it repairs the concrete
import failure without weakening the statement or sending the obligation on again.

The old node attachment pointed to the quarantined Sheaf declaration; it now points to the
canonical theorem. The dependency graph and parent node remain intact. There are no
consumer adaptations: both the source chart theorem and its Sheaf compatibility import
already use the canonical theorem. The independent delivery reviewer can compare the
preserved archive with the source signature and proof and compile the restored import.

## Second reading by F4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
