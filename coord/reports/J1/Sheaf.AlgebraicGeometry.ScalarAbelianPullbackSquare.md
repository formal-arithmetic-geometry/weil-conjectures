## What changed

Restored `lean/Sheaf/AlgebraicGeometry/ScalarAbelianPullbackSquare.lean` as a compatibility
module publicly importing `WeilConjectures.AlgebraicGeometry.ScalarAbelianPullbackSquare`.
The archived source used the retired Sheaf factorization together with upstream proof modules,
causing the duplicate `scalarAbelianForget` error recorded in `coord/rework.tsv`.
The restored path exposes the canonical upstream declarations and complete existing proof;
it does not redeclare any of them. No source-library file was changed.

The existing node attachment and proof dependencies are preserved verbatim. The record
`coord/changes/scalar-abelian-pullback-square-compatibility.md` documents the interface repair.

## Proved and sorry left

This is a zero-hole import repair: 0 holes closed, 0 holes added, and 0 direct holes remain.
`AlgebraicGeometry.Scheme.scalar_abelian_pullback_square` is already proved in the canonical
upstream module. Its supporting `scalar_forget_pullback_adjunction` and
`scalar_structure_coefficient_adjunct` are also proved there. No proof is split off.

The restored module compiles in 1.2 seconds. A separate scratch probe compiled and checked
all three theorem axiom sets: each uses only `propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

The wrapper replaces all four archived imports with the single public import of the canonical
upstream square. Removed archived imports:
`Sheaf.AlgebraicGeometry.ScalarAbelianExtFactorization`,
`WeilConjectures.AlgebraicGeometry.TensorPullbackStructureSheaf`,
`WeilConjectures.AlgebraicGeometry.ScalarForgetPullbackAdjunction`, and
`WeilConjectures.AlgebraicGeometry.ScalarStructureCoefficientAdjunct`.
The last three remain dependencies of the canonical implementation. No mathematical node or
upstream module is pruned. The duplicate Sheaf declarations are not restored.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving a hole, but this item is a quarantined import repair with
zero direct holes. The current node already records the canonical upstream attachment and the
independently reviewed retirement of the Sheaf duplicate (reviewer C-91aed, group V2,
2026-10-20). The quarantined archive is older than that reconciliation and cannot safely be
restored verbatim. A compatibility import repairs its module path while preserving that
reviewed attachment and every mathematical dependency. Exact import searches in both `lean/`
and `quarantine/` found no direct consumers of the historical Sheaf path; no adaptations are
required.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
