## What changed

Restored `Sheaf.Paper.PbcConstructibleReductionCriterion` from the quarantined
archive named by `coord/rework.tsv`. The module proves
`AlgebraicGeometry.Scheme.pbc_constructible_reduction_criterion` by combining the
uniform reduction criterion with the exact constant coefficient comparison. The
public statement, imports, theorem name, and DAG attachment are unchanged from
the archived module. The file compiles with `lcompile.py`.

## Proved and sorry left

`AlgebraicGeometry.Scheme.pbc_constructible_reduction_criterion` is complete. The
restored module contains no `sorry`; no new statements or holes were added. The
number of holes closed in this delivery is zero because the quarantined archive
already contained the complete proof, and the number of holes left is zero.

## No longer needed

None. The proof uses both `Sheaf.Paper.PbcUniformReductionProfile` and
`Sheaf.Paper.PbcUniformReductionCriterion`; no imports, DAG nodes, declarations,
or unit steps were pruned.

## Where the brief, the DAG or earlier work was wrong

The module was absent from `lean/` only because the rework record quarantined it
after a cluster restore and merge-queue reversion. Its archived proof is complete
and compiles against the current dependency modules. No statement or definition
was changed, and no consumer adaptation is required.

## New nodes

None.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
