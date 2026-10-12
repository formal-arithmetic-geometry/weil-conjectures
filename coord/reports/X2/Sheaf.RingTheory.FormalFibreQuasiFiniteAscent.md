## What changed

Replaced the sole `sorry` in `Sheaf.RingTheory.FormalFibreQuasiFiniteAscent` with a complete
proof of `RingHom.isRegular_formalFiber_of_isQuasiFiniteAtPrime` following all six steps of
the existing DAG plan. Added proof imports `Mathlib.RingTheory.TensorProduct.Pi` and
`Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra`. Added a proved private helper
`regularRing_fst`, which applies the existing localization regularity theorem to the first
projection, localizing at powers of the idempotent `(1, 0)`.

The completion splitting is upgraded to an R'-algebra equivalence using its pure-tensor
formula. Tensor cancellation and distribution over products identify the extended old fibre
with a product whose first factor is the new fibre. The finite type residue-field extension
is essentially finite type, and remains so after a finite field extension. Apply the existing
geometric regularity field-extension theorem, then the private factor helper, both over the
residue field itself and over each finite purely inseparable extension.

## Proved and sorry left

Closed one hole: `RingHom.isRegular_formalFiber_of_isQuasiFiniteAtPrime`
(node `lem-weil-pbc-formal-fibre-quasi-finite-ascent`). The module has no remaining `sorry`.
Added zero holes and split off zero statements. This is a proof from existing declared
lemmas, including `Algebra.completion_at_quasiFiniteAtPrime`, whose existing hole is retained
in its own module. It is not an assertion that the entire transitive closure is sorry-free.

## No longer needed

None. All original imports and planned proof dependencies remain needed. Tensor cancellation
uses the Mathlib equivalence directly; residue-field finite generation uses Mathlib's
`IntermediateField.fg_top`. No module is claimed pruned. The existing DAG proof and its
unit route still describe the Lean proof, so no node edit is required.

## Where the brief, the DAG or earlier work was wrong

No mathematical errors found. The inequality `q' ≤ p'` is retained in the unchanged signature;
the splitting and scalar-extension argument in fact needs no use of this inequality beyond
its contracted counterpart. No definitions, statements, signatures, or visibility changed.
Local compilation and the delivery dry run provide the checks; no library build or push was
performed.

## Second reading by X2

1. **Statements and interfaces.** Compared the delivered module with the repository version. The theorem signature and all existing declarations are byte for byte unchanged; only proof imports, a private helper, and the target proof differ.
2. **Proof validity.** Compiled the module with `lcompile.py`; it succeeds with no errors and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The proof uses the existing completion splitting, tensor cancellation, finite field extension, and localization regularity results and closes the target without adding a statement.
3. **Search and split statements.** No statements were split off and no new nodes were added. The helper `regularRing_fst` is private and is an elementary factor argument, so it introduces no public interface or DAG node.
4. **Pruning and route.** The two added imports are used by the tensor-product product equivalences and `IntermediateField.fg_top`; all pre-existing imports remain used by the proof. The six-step unit route is preserved through the completion splitting and factor-regularity arguments, and no proof dependency can be removed.
5. **DAG agreement.** The target node, declaration, and statement remain unchanged; the proof now follows the same six planned steps, with Mathlib lemmas supplying the tensor and finite-generation details. No node or unit record requires an edit.

I changed only the completed proof and its two proof-only imports, and added this second-reading report section.
