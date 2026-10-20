## What changed

Restored `Sheaf.AlgebraicGeometry.IsomorphicSingleTensorCounitEquation` as a public
re-export of `WeilConjectures.AlgebraicGeometry.IsomorphicSingleTensorCounitEquation`.
The existing adopted module proves the exact equation. Its public signature and
proof body match the quarantined copy verbatim, and its two direct imports match
exactly. The re-export adds only the proved equation module itself to the old
dependency closure.

Reattached `lem-pc-isomorphic-single-tensor-counit-equation` to the adopted source
declaration. Its statement, mathematical proof route, proof dependencies, and
unit realization are unchanged. No source-library module is edited.

The original quarantined file reproduces the recorded local irreducibility error
in 45.5 s. Removing only the redundant assignment compiles in 44.4 s, but the full
delivery axiom probe then exceeds 60 seconds. Reusing the exact existing proof
avoids repeating that elaboration and duplicate declaration. The final re-export
compiles in 13.8 s; an explicit `#print axioms` check compiles in 2.7 s and reports
only `propext`, `Classical.choice`, and `Quot.sound`.

Change record: `coord/changes/Q7-IsomorphicSingleTensorCounitEquation-rework.md`.

## Proved and sorry left

This is a quarantine repair with zero original holes and zero remaining holes.
`AlgebraicGeometry.isomorphic_single_tensor_counit_transport_equation` is supplied
by its identical existing adopted-source proof. Holes closed: none (0).
Holes added: none (0). Split off: none (0). No `sorry` remains in the delivered
compatibility module. The delivery does not claim a new mathematical proof.

## No longer needed

The duplicate local equation theorem and its private helpers `single_comp`,
`homotopy_single_comp`, `tensorAdjunction`, `tensorCompositionComparison`,
`tensorCounit`, `pinned_single_comp`, `transport_eq`, and
`single_tensor_transport_equation` are replaced by the adopted proof.

The direct public import of `IsomorphicSingleTensorCounitTransport` and private
import of `PinnedPullbackCompositionShifts` are replaced by the public equation
import. Both dependencies remain used by the adopted source equation; neither
module nor any DAG proof dependency is pruned. The Sheaf module remains as the
compatibility re-export, with no declarations of its own. No module is deleted.

## Where the brief, the DAG or earlier work was wrong

The queued item is a one-module quarantine repair in `coord/rework.tsv`, with its
source under `quarantine/Sheaf/AlgebraicGeometry/`, not an unproved theorem under
`lean/Sheaf/`. The stale local attribute conflicts with upstream's `irreducible_def`.
The DAG attachment still pointed at the removed copy although the identical
proved source declaration is already present.

The twin inventory flags a possible conflict with retained dependencies. For this
module specifically, comparison of the actual quarantined and upstream import
lines proves their dependencies below the equation are the same: both already import
upstream transport and upstream pinned composition shifts. The re-export adds
only the proved upstream equation module, with no additional imports below it.
The adopted proof is exactly the node's existing argument.

Source searches find no direct importer of the assigned Sheaf module in either
`lean/` or `quarantine/`. The upstream consumer already uses the adopted equation.
No forced consumer adaptations are needed. The unit's realization lists are
empty and no unit route is bypassed.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
