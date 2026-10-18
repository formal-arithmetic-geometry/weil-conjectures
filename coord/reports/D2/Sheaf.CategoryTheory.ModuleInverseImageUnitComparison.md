## What changed

Proved `SheafOfModules.inverseImage_underlying_unit_of_ring_presentation` by applying
`SheafOfModules.inverseImage_underlying_of_ring_presentation` from
`Sheaf.CategoryTheory.ModuleInverseImageAdjunction`. The existing theorem has exactly
the same hypotheses and conclusion, including compatibility with the adjunction unit.
Removed the unused private `inverseImage_underlying_unit_of_actions` and its generator
parameter block, rather than duplicating the existing restricted-adjunction proof.
The public statement and public imports are unchanged. Updated the item's node to
record the single dependency actually applied. The conservative command-change
gate requested a record for removing local `open` and `variable` commands; see
`coord/changes/D2-module-inverse-image-unit-reuse.md`. No public signature changes. The single-file server compile passed
in 2.2 seconds without warnings.

Searches: LeanFinder returned the generic module pullback adjunction and free-module
comparison APIs; Loogle returned the underlying-sheaf functor APIs; the remote grep
query found no exact match. Local `rg` and reading the full existing adjunction module
found the exact theorem, whose proof already constructs the scalar-linear lift and
retains the unit equation. No new construction or choice of data is introduced here.

## Proved and sorry left

Closed 1 original hole, added 0 holes, left 0 holes in the delivered module.
The original hole was in the private
`SheafOfModules.inverseImage_underlying_unit_of_actions`; that redundant helper is
removed. The unchanged public
`SheafOfModules.inverseImage_underlying_unit_of_ring_presentation` is proved by the
existing theorem above, attached to
`lem-weil-pbc-module-inverse-image-action-adjunction`. This is reuse of an already
proved declaration, not decomposition into a new holed statement.

## No longer needed

Removed the direct proof imports
`Sheaf.CategoryTheory.ModuleInverseImageAction` and
`Sheaf.AlgebraicGeometry.EtaleInverseImageModuleAdjunction`. Replaced
`import all Sheaf.CategoryTheory.ModuleInverseImageAdjunction` by its ordinary proof
import: no private declarations are needed.

Removed direct proof-dependency edges to
`lem-weil-pbc-inverse-image-module-adjunction`,
`lem-weil-pbc-module-inverse-image-action-of-presentations`,
`lem-weil-pbc-sheaf-pullback-forget-comparison`, and
`lem-weil-pbc-sheaf-pullback-unit-presentation`.
Their construction and generator arguments are already encapsulated in the existing
adjunction theorem; they remain its transitive dependencies where required. No claim
is made that these modules leave the targets' transitive import closure.
The presentation module remains publicly imported because the statement uses its
structure. The unit-comparison module retains its public theorem used by
`Sheaf.AlgebraicGeometry.ProEtaleModuleSpecializationUnit`; no consumer adaptation or
module withdrawal is necessary.

## Where the brief, the DAG or earlier work was wrong

The original local proof repeats a construction which the current
`ModuleInverseImageAdjunction` theorem already proves with the full unit equation.
The latter node records that its statement was strengthened to include unit
compatibility on 2026-10-15, and its current proof was repaired by B2 on 2026-10-17.
Consequently the item's private remaining hole and independent construction are
unnecessary. No mathematical statement is changed and no unit-level route is bypassed.

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
