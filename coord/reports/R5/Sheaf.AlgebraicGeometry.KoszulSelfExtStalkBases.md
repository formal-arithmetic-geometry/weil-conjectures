## What changed

Removed the unused public import `Mathlib.LinearAlgebra.ExteriorPower.Basis` from
`Sheaf.AlgebraicGeometry.KoszulSelfExtStalkBases`. The module's theorem,
private coordinate and stalk-basis helpers, and all public imports needed by the
statement remain unchanged. The module compiles with no `sorry`s.

## Proved and sorry left

The existing declaration `AlgebraicGeometry.koszulRegularImmersion_self_ext_stalk_bases`
and every private helper in the module are proved. No `sorry` remains and no new
statement or node was added.

## No longer needed

The removed direct import `Mathlib.LinearAlgebra.ExteriorPower.Basis` was not
referenced by the module; the required basis API is available through the remaining
imports. No DAG node or other module is pruned.

## Where the brief, the DAG or earlier work was wrong

The source module was already fully proved at the current repository tip, so there
was no proof hole to close. The only needed repair was pruning the unused public
import; the theorem signature and the DAG proof route remain unchanged.

Change record: `coord/changes/KoszulSelfExtStalkBases-import-pruning.md`.

## Second reading by R5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
