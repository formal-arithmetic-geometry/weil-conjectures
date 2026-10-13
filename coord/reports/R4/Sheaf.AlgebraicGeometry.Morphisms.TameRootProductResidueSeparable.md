## What changed

Proved `AlgebraicGeometry.Scheme.tameRootProduct_residue_separable` in the item module. The proof adds the needed `Mathlib.FieldTheory.SeparableClosure` import and uses the finite-product prime factorization, residue-field fraction-ring presentation, and separability of tame root polynomials.

## Proved and sorry left

The declaration `AlgebraicGeometry.Scheme.tameRootProduct_residue_separable` is proved. No `sorry` remains and no new declarations were added.

## No longer needed

None. The existing public imports are retained; `Mathlib.FieldTheory.SeparableClosure` is used by the proof.

## Where the brief, the DAG or earlier work was wrong

The DAG proof sketch omitted the explicit algebraic identification of residue fields. The proof supplies this by constructing the coefficient map into the residue field, using the fraction-ring presentation of a prime residue field, and showing every residue element lies in the separable closure.

## Second reading by R4

1. Compared the delivered module with the repository version. The theorem statement and all existing declarations are byte-for-byte unchanged; only a proof-only import and proof body differ. Verdict: pass.
2. Compiled the module with `lcompile.py`; it succeeds with no errors or warnings. The module contains no `sorry`, axioms, unsafe declarations, or hollow definitions. Verdict: pass.
3. Checked the proof route and edge cases (`m = 0`, zero ring, `e = 1`, and `f = 0`) against the theorem hypotheses and construction. The factor selection, tame root separability, and residue-field localization argument establish exactly the stated separability conclusion. No new statements were introduced. Verdict: pass.
4. The proof uses `Mathlib.FieldTheory.SeparableClosure` and all retained public imports; no imported module was shown unnecessary. The proof closes the sole target hole and adds none. Verdict: pass.
5. The DAG node's declaration and statement match the Lean theorem, and its unit route is retained. The proof is a direct implementation of the node's stated finite-product/root-chart argument. Verdict: pass.

Changed only the proof import/body as described above; no statement, definition, node, or unit metadata required repair.
