## What changed
Added the affine core theorem `idealPowersLocalCoefficientSpan_affine` as a named split and proved the original local theorem by choosing an affine neighbourhood and applying the core. The target module now compiles.

## Proved and sorry left
`idealPowersLocalCoefficientSpan` is proved. `idealPowersLocalCoefficientSpan_affine` remains `sorry` as the strictly simpler affine algebraic expansion node `lem-weil-pbc-ideal-powers-local-coefficient-span-affine-core`.

## No longer needed
None; all stated proof imports remain available for the affine core.

## Where the brief, the DAG or earlier work was wrong
The DAG proof plan omitted a separately stated affine core needed to make the local-to-affine reduction compile cleanly.

## New nodes
`lem-weil-pbc-ideal-powers-local-coefficient-span-affine-core` records the remaining affine coefficient expansion.

## Earlier second reading (a previous round; superseded)
The affine core is the only remaining node; the local theorem preserves the original signature and follows by affine-neighbourhood restriction.

## Second reading by X3

1. Compared the delivered module with the repository version. The existing target declaration is byte-for-byte unchanged; only its proof was filled and the affine split declaration was added.
2. Compiled the module with `lcompile.py`; it succeeds with the sole remaining `sorry` in `idealPowersLocalCoefficientSpan_affine`. No definitions contain `sorry`, and no forbidden declarations occur. The proven local theorem uses only the permitted kernel axioms apart from the explicitly open affine theorem.
3. The affine split is a strict, true reduction of the target: it fixes an affine open and a restricted section, while retaining the original hypotheses and conclusion in specialized form. Its docstring gives the algebraic expansion source and proof route, and its DAG node records the split. Searches found no existing theorem with this statement.
4. The proof follows the unit route by first choosing an affine neighbourhood and then invoking the affine coefficient expansion. The target node now records the affine core as its proof dependency; the affine node depends only on the original definitions and the three stated affine algebra modules. No unused imports were found.
5. The DAG and Lean declarations agree after updating the target proof and proof dependencies and removing the circular statement dependency from the affine node. The unit record and target statement remain unchanged.

Changed the target node's proof metadata, corrected the affine node's statement dependencies, and added this second-reading record. No Lean proof text required repair.
