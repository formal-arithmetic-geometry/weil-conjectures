## What changed

Proved `ModuleCat.residue_kernel_unit_minor_pivot` in
`Sheaf.Algebra.Homology.ResidueKernelUnitMinorPivot`, preserving its signature,
visibility, original docstring and public imports. Added five proof-only imports:
`Mathlib.LinearAlgebra.Matrix.ToLinearEquiv`,
`Mathlib.RingTheory.LocalRing.ResidueField.Basic`,
`Mathlib.RingTheory.TensorProduct.Free`,
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.ChangeOfRings`, and
`WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank`.

The private proved rank helper transports tensor-product bases through
`ModuleCat.tensorEquivExtendScalars`, uses `extendScalarsComp` naturality to
identify the two residue kernels, and applies rank-nullity. The original proof
then uses the proved `Matrix.exists_submatrix_det_ne_zero_of_le_rank`, proves
both minor index maps injective, and lifts the nonzero determinant to a unit.
Private coordinate helpers split each index type into the selected indices and
their complement. The source complement has exactly one element; the target
complement gives the free module C. `Matrix.toLinearEquiv` constructs B, and
reindexing the finite coordinate sum proves the required first-component equation.
The original node's three-step route is followed throughout; no node update or
new statement with a postponed proof is needed.

The construction includes rank-zero/empty selected minors: it never assumes
`r > 0`. It also allows an empty target complement. The impossible empty-source
case is excluded by the proved equality `card(source basis) = residue rank + 1`.
All choices of coordinate indices are made inside the theorem proof from proved
results; the only new definition constructs an explicit coordinate equivalence.

## Proved and sorry left

Closed the one original hole:
`ModuleCat.residue_kernel_unit_minor_pivot`
(node `new-residue-kernel-unit-minor-pivot`).

No sorry remains in the module. No holes were added or split off. The private
rank and coordinate helper declarations are fully proved. Single-file compilation
through `lcompile.py` succeeds without warnings. The delivery dry run checks the
axioms of every added declaration as well as the preflight requirements.

## No longer needed

None. The original file had no proof-dependency imports to prune, and all five
added proof-only imports are used. No DAG node or module from the original plan
is bypassed: the original proof dependencies were empty, and the completed proof
implements all three original steps using already proved infrastructure.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The original node's search already
mentioned the proved source-library minor theorem; applying it to the actual
residue matrix supplies the selection step without adding intermediate holes.
The source-library tensor/scalar-extension equivalence has exactly the universe
generality needed here, so no duplicate tensor equivalence was introduced.

Searches: LeanFinder returned related general linear-algebra facts but no pivot
statement; Loogle returned the matrix-rank API; grep found rank-nullity and local
ring infrastructure. LeanSearch was unavailable (Internal Server Error), recorded
by `msearch.py`. Direct source reading located the two proved source-library APIs
used above. The unit record `sk-prop-av-cube` has empty realization lists, and this
delivery preserves the original node's route within that unit.

## Second reading by S4

1. **Visible changes:** Compared the delivered module with the repository version.
   The theorem signature, visibility, docstring, and existing public imports are
   byte-for-byte unchanged; only proof-only imports, private helpers, and the proof
   body were added. Verdict: pass.
2. **Proof and axioms:** Compiled the module with `lcompile.py` and with the
   sandbox import-order build. The module has no `sorry`, forbidden declarations, or
   hollow definitions. The proof uses only the stated assumptions and the helper
   theorems, and its construction handles the rank-zero case. Verdict: pass.
3. **Statements and prior work:** No statements were split off or changed, so no
   new theorem requires a node or separate source justification. The existing node
   statement is proved exactly as written; no Mathlib or upstream duplicate was
   introduced. Verdict: pass.
4. **Route and pruning:** The proof follows the node's three steps: residue
   rank-nullity, selection and lifting of a unit minor, then coordinate
   decompositions and the leading automorphism. All five added imports are used;
   no old proof dependency or unit step is bypassed. Verdict: pass.
5. **DAG agreement:** The node's declaration, proof route, and proof dependencies
   agree with the Lean proof. The unit `sk-prop-av-cube` realization is unchanged.
   Verdict: pass.

Changed in this second reading: added this required review record; no Lean or DAG
changes were necessary.
