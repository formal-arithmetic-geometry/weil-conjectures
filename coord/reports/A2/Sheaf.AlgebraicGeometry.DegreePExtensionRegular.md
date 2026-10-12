## What changed

Replaced the proof of `Algebra.isRegularRing_quotient_X_pow_sub_of_isUnit_derivation` with a
complete proof.  The proof uses Mathlib's coefficientwise derivation extension
`Derivation.mapCoeffs`, the regularity theorem for polynomial rings, and the imported
hypersurface derivation criterion.  Removed the unused smooth-ascent import and made the
MapCoeffs and polynomial-regularity imports proof-only.  The interface review is recorded in `coord/changes/isRegularRing_quotient_X_pow_sub_of_isUnit_derivation.md`.

## Proved and sorry left

The target declaration `Algebra.isRegularRing_quotient_X_pow_sub_of_isUnit_derivation` is proved;
no `sorry` remains in the delivered module.

## No longer needed

The proof does not use `Sheaf.RingTheory.RegularRingSmoothAscent`, nor the DAG dependencies
`lem-weil-pbc-polynomial-ring-smooth` and `lem-weil-pbc-regular-ring-smooth-ascent`.  Polynomial
regularity is supplied directly by Mathlib's `Polynomial.isRegularRing_of_isRegularRing`.

## Where the brief, the DAG or earlier work was wrong

The planned smoothness-and-ascent step is unnecessary: Mathlib directly proves that a
polynomial ring over a regular ring is regular.  The coefficientwise extension is also
available directly as `Derivation.mapCoeffs`.

## Earlier second reading (a previous round; superseded)

The proof was compiled independently with the sandbox single-file compiler; a second-reader
review remains for the receiving lead.

## Second reading by A2

1. Interface check: compared the delivered module with the repository version. The theorem signature and all existing declaration statements are byte-for-byte unchanged; only proof text and proof-only imports differ. Verdict: pass.

2. Proof check: compiled `lean/Sheaf/AlgebraicGeometry/DegreePExtensionRegular.lean` with the sandbox compiler. The target has no `sorry`, `axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`; the proof uses coefficientwise derivation extension, computes the derivative of the defining polynomial, maps the unit to the quotient, and applies the hypersurface criterion. Verdict: pass.

3. Statement and dependency check: the target statement is unchanged and the existing DAG node has no new split-off theorem. The proof dependency list was pruned to the declarations actually used, while the unit-level hypersurface route remains. Verdict: pass.

4. Pruning check: removed the unused smooth-ascent import and its two DAG proof dependencies; polynomial regularity is supplied directly by Mathlib's `Polynomial.isRegularRing_of_isRegularRing`. Verdict: pass.

5. DAG and route check: updated the node's proof, proof dependencies, and proof origin to match the Lean proof and Mathlib regular-polynomial instance. The unit route and target meaning remain unchanged. Verdict: pass.

Changed in this second reading: added the synchronized DAG proof metadata and this review; no Lean statements or definitions changed.
