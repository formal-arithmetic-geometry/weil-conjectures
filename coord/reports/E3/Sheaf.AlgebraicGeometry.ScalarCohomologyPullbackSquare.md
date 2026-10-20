## What changed

Restored `lean/Sheaf/AlgebraicGeometry/ScalarCohomologyPullbackSquare.lean`
from its recorded quarantine archive. Replaced its public import of the
retired `Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations` with
`WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`.
This repairs the assigned missing-public-interface error. The theorem,
four private proved helpers, and all proof bodies are verbatim from the archive.
The composition dependency remains a private proof import.

Single-file compile through `lcompile.py` passed in 1.7 seconds with no warnings.
The DAG Lean attachment is preserved, with a restoration note. Proof, dependency
lists, and unit route are unchanged. Consumer review includes both quarantined
consumers and the direct consumer's two applications of the theorem.
Change record: `coord/changes/scalarCohomologyPullbackSquare-upstream-import.md`.

## Proved and sorry left

This is an assigned repair with zero original holes. Closed: zero. Added: zero.
Remaining textual `sorry`: zero. No statements split off.
`AlgebraicGeometry.Scheme.Modules.scalarCohomologyPullback_square` retains its
complete proof from `scalarCohomologyPullback_comp`, functoriality, equality
transport, and cancellation. This delivery claims an import repair, not a newly
closed mathematical hole. Node: `lem-sc-scalar-cohomology-pullback-square`.

## No longer needed

Removed the stale public import of
`Sheaf.AlgebraicGeometry.FieldLinearModuleCohomologyOperations`, an already
withdrawn empty module; the corresponding upstream import supplies the same
recorded operations. No mathematical node or additional module is pruned.
The square theorem and its quarantined parents remain needed and preserved.

## Where the brief, the DAG or earlier work was wrong

The archived import still points at the retired local operations module after
upstream sync. The recorded `Field` visibility failure is fixed by importing the
canonical public interface. The archive already contained a complete proof,
so the actual hole count is zero. There is no mathematical statement change.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
