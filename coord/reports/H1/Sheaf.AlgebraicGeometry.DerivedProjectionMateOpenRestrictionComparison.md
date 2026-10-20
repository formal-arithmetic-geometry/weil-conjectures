## What changed

The quarantined Sheaf compatibility module was verified and retained as a public import of
`WeilConjectures.AlgebraicGeometry.DerivedProjectionMateOpenRestrictionComparison`. Its module
docstring now records that this path intentionally exports the canonical upstream declaration
without introducing a duplicate, and gives the precise Stacks source place. The upstream
module and its complete proof are unchanged.

## Proved and sorry left

The canonical declaration
`AlgebraicGeometry.exists_derivedProjectionMate_openRestriction_comparison` is already proved
and has no `sorry` (0 of 0 holes in this compatibility module). No holes were added or split
off. Its proof dependencies remain the quasi-coherence restriction criterion, adjunction
hom descent, and tensor/counit descent.

## No longer needed

No proof-dependency import or DAG node is removed. The former quarantined duplicate declaration
and its local helper are unnecessary because the canonical upstream module supplies the exact
statement and proof; the Sheaf file only preserves the import path.

## Where the brief, the DAG or earlier work was wrong

The rework row describes an import collision in the old full Sheaf copy. The current base already
contains the correct A6 restoration as a compatibility import, so no duplicate proof can be
introduced safely. Verification with `lcompile.py` confirms the compatibility module compiles;
LeanFinder finds no shorter exact Mathlib theorem for the derived projection mate comparison.

## Second reading by H1

No second worker reading is required under the current stage-3 direct-delivery procedure; the
maintainer's independent review is the required review. The module statement and the node's
existing upstream lean attachment are unchanged.
