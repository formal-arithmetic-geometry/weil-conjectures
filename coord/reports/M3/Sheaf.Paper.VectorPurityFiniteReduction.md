## What changed

Restored `lean/Sheaf/Paper/VectorPurityFiniteReduction.lean` verbatim from the
quarantine path recorded in `coord/rework.tsv`. The live path was absent.
All seven definitions and five public imports are retained exactly, including
actual quotient maps, normalized scalar-line/power/source maps, and the
compact-support and exceptional-mate compatibility predicates.

Single-file server compilation through `lcompile.py` succeeded without errors
or warnings in 34.2 seconds. The existing node copy is unchanged; the Lean
attachment and all statement dependencies are preserved. The archived parent
`VectorBundlePurity` still uses this predicate, so restoration preserves its
interface and route. No consumer requires adaptation.

Change record: `coord/changes/M3-vector-purity-finite-reduction-restoration.md`.

## Proved and sorry left

This is a zero-hole definition restoration, not a proof or decomposition.
Holes closed: 0. Holes added: 0. Sorries left in the restored module: 0.
No new module or theorem with a sorry is introduced.

Restored declarations (namespace `WeilConjectures.PurityFiniteSetting`):
`purityReductionRing`, `purityReductionRingMap`, `PurityScalarLineNormalization`,
`purityScalarPower`, `purityScalarSourceMap`, `PurityScalarReductionEquation`,
and `PurityFiniteReductionEquation`.

## No longer needed

None. No import, node, module or declaration is removed. The node
`def-pur-vector-purity-finite-reduction` and its archived parent
`cor-pur-vector-bundle-purity` retain all dependencies. The archive is preserved.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a module with sorry holes; the current
rework row instead assigns restoration of a quarantined definition module
with zero holes. The row, archive and existing node agree. No statement,
definition or unit-route correction was needed. No current return entry for
this item was found in `coord/returns/M3.md`.

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
