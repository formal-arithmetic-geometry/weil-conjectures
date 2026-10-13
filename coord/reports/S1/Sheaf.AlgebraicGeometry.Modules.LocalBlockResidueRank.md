## What changed

Repaired the returned delivery by removing the module-level private theorem
`matrix_restrict`, which duplicated the word-for-word statement
`freeMatrix_restrict` already recorded in `LocalInvertibleMinorBlockData`. Its proof is
now a local `hrestrict` fact inside `local_block_residue_rank`; the theorem signature
and all public interfaces are unchanged.

Proved `AlgebraicGeometry.Scheme.Modules.local_block_residue_rank` in
`Sheaf.AlgebraicGeometry.Modules.LocalBlockResidueRank`, preserving its signature and
visibility. Added one proof-only import, `Sheaf.LinearAlgebra.MatrixRankFieldExtension`.
All local helpers are private and proved: free-matrix composition, rank invariance under
arbitrary finite free change of basis, block rank additivity, biproduct coordinates,
full evaluated rank of an isomorphism, ULift reindexing, and the restriction matrix formula.
No definition uses unproved data. Updated the node's proof to the compiled argument.

The proof transports the original bases to U, compares evaluations through the induced
residue-field homomorphism, and uses the stated normal form. It then computes the diagonal
matrix rank via the product of its two ranges. The invertible block has rank a because
its inverse remains an inverse after evaluation. This avoids building a fibre functor.
The unit's route through the local normal form is retained.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.local_block_residue_rank`
(node `lem-pc-local-block-residue-rank`).

Holes closed: 1. Holes added: 0. No sorry remains in the delivered module.
This is a proof, not a decomposition. Every helper is proved and the field-extension
rank theorem imported from the library is already proved.

## No longer needed

The module-level duplicate `matrix_restrict` declaration is no longer needed; its exact
calculation is retained locally as `hrestrict` solely at the use site. No original import
or proof-dependency node was pruned. The two original public imports
are required by the unchanged statement. Trial proof-only imports of
`WeilConjectures.Mathlib.AlgebraicGeometry.Restrict` and
`Mathlib.LinearAlgebra.Dimension.Constructions` were removed: the needed declarations
are already available through the retained imports.

No import of `Sheaf.AlgebraicGeometry.TensorPullback` is required: the proof uses Mathlib's
`Scheme.Modules.pullback`, which the existing pullback/restriction node explicitly allows.
No new fibre-comparison, block-rank or pullback-biproduct lemma with sorry is needed.
The explicit pullback-to-Spec route in the old proof plan is replaced by evaluation
naturality and field-extension rank invariance, with all matrix glue proved locally.

## Where the brief, the DAG or earlier work was wrong

The returned delivery was wrong to introduce a module-level theorem duplicating the
existing `freeMatrix_restrict` statement. This repair removes that duplicate while
preserving the same calculation locally. No statement error was found. The plan's
residue-field isomorphism hypothesis is
unnecessary for rank comparison: any homomorphism of fields preserves rank. Open
immersion is still used for restriction comparison. The rank proof handles rectangular
change-of-basis matrices by inequalities in both directions, so it does not require an
extra hypothesis a ≤ m or a ≤ n. Zero ranks and empty complementary indices need no
separate case split; every identity used holds for empty finite index types.

The source blueprint file named by the node is not present in this read-only clone.
The argument is retained in the existing declaration docstring, node proof, and unit
record; this delivery formalizes that argument without introducing any new unproved lemma.

## Earlier second reading (a previous round; superseded)

1. **Visible changes.** Compared the delivered module and node with the repository versions. The theorem signature and all existing declarations are unchanged; the only module interface change is the proof-only import of `Sheaf.LinearAlgebra.MatrixRankFieldExtension`. The node records the revised proof route and dependencies.
2. **Proof validity.** Compiled `LocalBlockResidueRank.lean` successfully with `lcompile.py`. The file contains no `sorry`, axioms, unsafe/opaque declarations, or hollow definitions. The proof uses only the permitted library axioms through its dependencies.
3. **Statements.** No statements were split off or added. The target theorem remains exactly the original statement, and all private helper lemmas are proved locally. The block-rank and field-extension steps cover zero and empty-index cases as well as ordinary ranks.
4. **Pruning and route.** The retained public imports are required by the unchanged statement; the added import is proof-only. The proof keeps the unit's local normal-form route, while replacing the planned explicit residue-field pullback with evaluation naturality and field-extension rank invariance. No old proof dependency is unused according to the updated node.
5. **DAG agreement.** The node's proof steps, `proof_deps`, and `proof_origin` describe the compiled argument and match the declarations used by the module. The unit record and target statement remain unchanged.

Changed only the proof, its proof-only import, the matching node proof metadata, and this second-reading report section.


## Second reading by S1

1. **Visible changes.** Compared the delivered module and node with the repository versions. The theorem signature and existing declarations are unchanged; only a proof-only import, the proof, matching DAG proof metadata, and this report differ. Verdict: pass.
2. **Proof validity.** Compiled the module with `lcompile.py`; it is error-free and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or hollow definition. The scratch-copy `#print axioms` lists exactly `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. **Statements.** No statement was split off or weakened. The target theorem remains byte-for-byte unchanged, and all private helper lemmas are proved. Verdict: pass.
4. **Pruning and route.** The proof uses the local normal-form unit route, retains all required public imports, and the added matrix-rank theorem is proof-only. The removed duplicate helper is no longer needed; no proof dependency node is unused. Verdict: pass.
5. **DAG agreement.** The node proof steps, dependencies, and origin describe the compiled proof, and the unit route is preserved. Verdict: pass.

Changed the node proof text to name the actual local `hrestrict` fact rather than the removed `matrix_restrict` helper, and recorded this independent second reading. No mathematical repair was required. The unchanged unit record has empty realized lists; this delivery preserves its local-normal-form argument and introduces no bypass. Repository searches for block-rank and rank-of-global-sections alternatives found no shorter applicable residue-evaluation theorem.
