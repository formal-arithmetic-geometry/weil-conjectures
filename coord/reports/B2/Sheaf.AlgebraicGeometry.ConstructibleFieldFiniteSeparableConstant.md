## What changed
Added two intermediate theorem modules. The target theorem now extracts a finite trivializing datum and applies the finite-separable-extension core theorem.

## Proved and sorry left
`AlgebraicGeometry.constructible_field_finite_separable_constant` is proved by composition. The intermediate declarations `constructible_field_finite_separable_constant_datum` and `constructible_field_finite_separable_constant_of_datum` remain `sorry`.

## No longer needed
None; the original imports remain available for the stated route.

## Where the brief, the DAG or earlier work was wrong
The seven-step geometric argument is too large to formalize in one item; it was split into the datum extraction and extension core intermediate statements.

## New nodes
`lem-weil-pbc-constructible-field-finite-separable-constant-step1` and `lem-weil-pbc-constructible-field-finite-separable-constant-step3-7`.

## Earlier second reading (a previous round; superseded)
The target statement is unchanged. The two intermediate statements are strict substeps: extraction of a finite datum and the geometric extension argument from that datum. The unit route is retained.

## Second reading by B2

1. Compared the delivered target module with the repository version: the theorem signature and all existing declarations are byte-for-byte unchanged; only proof imports and proof bodies differ. Verdict: pass.
2. Compiled all three sandbox modules with the launcher; there are no errors, forbidden declarations, or unstructured partial proofs. The two remaining `sorry`s are named public theorems with source and blueprint docstrings. Verdict: pass.
3. Checked both split statements against their Lean declarations and tested the route on the field-spectrum and finite-etale edge cases. They are strict substeps (datum extraction and the residue-field/trivialization construction), not restatements of the target. Verdict: pass after replacing placeholder wording with exact mathematical statements.
4. The target proof follows the two split nodes; the original geometric imports are retained only where the split theorem modules need their declarations. No shorter closed theorem was found in the local library or Mathlib; the unit route is preserved. Verdict: pass.
5. Updated the target node proof, proof dependencies, and proof origin to match the actual composition proof; both new nodes now carry complete statements, sources, proof steps, and required search records. Verdict: pass.

Changed the two new node statements and proof metadata, corrected the target node route metadata, and made the two intermediate-module imports proof-only.
