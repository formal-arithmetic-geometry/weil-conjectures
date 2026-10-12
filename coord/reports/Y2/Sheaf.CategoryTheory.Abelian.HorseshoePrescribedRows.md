## What changed

Proved `CategoryTheory.InjectiveResolution.exists_horseshoe_prescribed_rows` in
`Sheaf.CategoryTheory.Abelian.HorseshoePrescribedRows`, with its signature unchanged.
Added the proved private helper `offDiagonal` and the proof-only import
`Mathlib.CategoryTheory.Abelian.Refinements`. The existing public import remains necessary
for the statement. Updated the node `lem-sp-horseshoe-prescribed-row-construction` to
record the actual direct upper triangular construction.

The helper descends the initial obstruction along the short exact sequence and extends
it across the right augmentation into the injective left degree-one term. It recursively
extends each subsequent obstruction using exactness of the prescribed right resolution.
The main proof constructs the biproduct complex, its inclusion/projection maps, and its
augmentation explicitly. Degree-zero exactness follows by lifting the right coordinate
of a cycle after an epimorphic refinement and then correcting the left coordinate.
This is the upper triangular differential construction of Stacks Tag 013T, Step 2,
specialized directly to the prescribed resolutions and prescribed initial lift.
The source was read at https://stacks.math.columbia.edu/tag/013T because the literature
TeX file is absent from this machine.

## Proved and sorry left

Closed the sole hole:
`CategoryTheory.InjectiveResolution.exists_horseshoe_prescribed_rows`
(node `lem-sp-horseshoe-prescribed-row-construction`).
The private helper `offDiagonal` is also fully proved. No holes remain in the module,
no holes were added elsewhere, and no statements or definitions were changed.
All construction data comes from proved Mathlib constructions and the proved helper.
Local compilation passes without warnings. The delivery dry run additionally checks
the axioms of every declaration; only the permitted standard axioms are allowed.

## No longer needed

The proof no longer needs `lem-weil-pbc-snake-lemma-abelian`
(Mathlib `CategoryTheory.ShortComplex.SnakeInput.snake_lemma`, module
`Mathlib.Algebra.Homology.ShortComplex.SnakeLemma`), nor the planned successive
short exact cokernel rows. This dependency was removed from the item's `proof_deps`.
There was no snake-lemma import in the original module to remove. No existing import
was removed. No Sheaf proof-dependency module or new intermediate theorem is needed.
The injective-resolution definition node `def-sp-injective-resolutions` remains used.
This is local pruning; the snake lemma can still be required elsewhere in the project.
The unit record has no realized statement or step nodes, and its route is unchanged.

## Second reading by Y2

1. Compared the delivered Lean module with the repository version. The theorem signature and
   all existing declarations are byte-for-byte unchanged; only the proof and a proof-only
   Mathlib import differ. The DAG node records the same statement and the implemented route.
2. Compiled the module with `lcompile.py`; it succeeds without warnings. Searched the source
   for `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, and `implemented_by`; none remain.
   The construction uses only proved exactness, injective extension, and biproduct APIs.
3. Checked the direct upper-triangular construction against the node and the Stacks Tag 013T
   source. The off-diagonal recursion and degree-zero exactness argument are strictly below
   the target statement and introduce no new split-off claims. The existing node remains the
   sole statement and its conclusion is unchanged.
4. Checked pruning: the snake-lemma dependency is absent from the proof and removed from
   `proof_deps`; `Mathlib.CategoryTheory.Abelian.Refinements` is proof-only. No other import or
   node is unnecessarily retained, and no new node is needed.
5. The unit record has no realized statement or step nodes, so its route is unaffected. The
   target theorem is proved directly from the prescribed injective resolutions, with no change
   to definitions or public interfaces.

Changed only the theorem proof, its proof-only import, and the DAG proof/proof-dependency
metadata; no holes remain and no holes were added.

## Where the brief, the DAG or earlier work was wrong

The theorem's statement is correct. The former DAG and declaration docstring describe
a valid but unnecessary snake/cokernel induction. Mathlib's exactness-to-injective
extension API gives the off-diagonal recursion directly. The DAG now records that
shorter proof. The existing declaration docstring was preserved; it describes the
previous mathematical plan, while inline comments and the updated node describe the
implemented route. No statement correction or change record is needed.
