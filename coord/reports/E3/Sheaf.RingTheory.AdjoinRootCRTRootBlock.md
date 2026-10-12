## What changed
Added `Sheaf.RingTheory.AdjoinRootCRTRootBlockAux` with two strictly smaller CRT sublemmas, and proved the target by combining them. The target module imports the auxiliary module.

## Proved and sorry left
`Polynomial.adjoinRoot_crt_matrix_root_block` is proved by real composition of the two auxiliary declarations. The degree declaration `Polynomial.adjoinRoot_crt_degree_equiv` is now proved by monic degree additivity and `Fintype.equivOfCardEq`; `Polynomial.adjoinRoot_crt_matrix_for_degree_equiv` remains `sorry` and is recorded by node `lem-weil-pbc-adjoinRoot-crt-matrix-root-block-aux-matrix`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The original proof plan requires substantial CRT and matrix-coordinate theory; these were split into degree-index and fixed-equivalence coordinate statements.

## New nodes
`lem-weil-pbc-adjoinRoot-crt-matrix-root-block-aux` and `lem-weil-pbc-adjoinRoot-crt-matrix-root-block-aux-matrix` record the two auxiliary statements.

## Second reading by E3
1. Compared both delivered modules with the repository versions. Existing theorem signatures are byte-for-byte unchanged; only the target proof and the degree auxiliary proof changed, with the auxiliary module added as declared.
2. Compiled both modules with `lcompile.py --all`. There are no errors, forbidden declarations, or unlisted `sorry`s. The target proof uses only the two auxiliary declarations, and the degree auxiliary has no remaining axiom beyond the permitted foundation.
3. Checked the split statements against the CRT degree and coordinate steps. The degree statement is true by monic degree additivity; the matrix statement is the strictly smaller fixed-equivalence coordinate sublemma and remains explicitly named with its node and source.
4. The target proof follows the supplied route and keeps the unit route; no imports were removable. The degree proof uses the shortest available Mathlib route (`Monic.natDegree_map`, `Monic.natDegree_mul`, `Fintype.equivOfCardEq`).
5. The DAG records match the declarations and proof status. Changed the report and closed the degree hole; no new hole was added.

## Earlier second reading (a previous round; superseded)
The target proof compiles and combines the two strictly smaller auxiliary statements; both auxiliary declarations have matching nodes.
