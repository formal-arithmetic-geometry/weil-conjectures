## What changed

Completed the proof of
`Matrix.exists_isUnit_maximal_minor_of_annihilator_eq_maximalIdeal`
in `Sheaf.RingTheory.UnitMaximalMinorOfDepthZero` without changing its signature.
Added the proof-only import `Mathlib.RingTheory.LocalRing.ResidueField.Basic`.
The proof follows the existing DAG route: lift a residue-field kernel vector coordinatewise,
multiply by the annihilator witness, use injectivity over R, and reduce again to prove that
the residue-field kernel is zero. Apply the existing field-minor theorem, lift the nonzero
determinant to a unit using determinant functoriality, and conclude that its ideal is top.

## Proved and sorry left

Closed the sole original hole:
`Matrix.exists_isUnit_maximal_minor_of_annihilator_eq_maximalIdeal`
(blueprint: `lem-weil-pbc-depth-zero-injective-free-map-unit-minor`).
No sorry remains in the delivered module; no holes were added or split off.
This is a complete proof from the existing stated dependency
`Matrix.exists_strictMono_submatrix_det_ne_zero_of_mulVec_injective`
(node `lem-weil-pbc-field-injective-matrix-nonzero-maximal-minor`), which still has sorry
in its own module and is not part of this delivery. Thus the target is reduced to that
existing dependency, rather than claimed to be free of sorry transitively.

## No longer needed

None. The existing field-minor dependency and all original imports are retained.
The proof keeps the original DAG route and prunes no nodes or modules.

## Where the brief, the DAG or earlier work was wrong

None. The annihilator argument works without separately proving that its witness is nonzero.
No assumptions, statements, definitions, visibility, or unit-level proof routes changed.
The proof includes zero columns and empty minors through the existing field-minor theorem.

## Second reading by Q1

1. Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte-for-byte unchanged; only a proof-only residue-field import and the theorem proof differ.
2. Compiled `lean/Sheaf/RingTheory/UnitMaximalMinorOfDepthZero.lean` with `lcompile.py`; it succeeds with no errors or warnings. The module contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or hollow definition. The proof uses only the existing field-minor dependency and standard residue-field/local-ring lemmas.
3. The delivered theorem is the original statement, with no split-off statements or new nodes. Its residue-field kernel argument is valid also for zero dimensions, and the unit-minor and ideal conclusions have the required strength. No duplicate library theorem was introduced.
4. The proof follows the node's stated route: choose the annihilator witness, prove injectivity after residue-field reduction, apply the field maximal-minor theorem, lift the determinant to a unit, and put that unit in the generated ideal. No shorter applicable route was found; the proof-only residue-field import is needed.
5. The unit route is preserved: the node and its `realized` unit route remain unchanged, and the DAG proof dependencies still describe the field-minor and determinant/submatrix steps. No nodes or modules were pruned.

Changed during second reading: no mathematical statements or definitions; only the proof-only import and completed proof are retained. No holes were added; the sole original hole was closed.
