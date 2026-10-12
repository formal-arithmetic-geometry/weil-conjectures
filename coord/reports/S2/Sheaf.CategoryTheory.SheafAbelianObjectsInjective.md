## What changed

Proved `CategoryTheory.sheafAbelianObjects_injective` in
`Sheaf.CategoryTheory.SheafAbelianObjectsInjective` with its statement and visibility unchanged.
Added the proof-only import `Mathlib.Algebra.Group.Ext` and three proved private helpers:
`sectionGroup_eq`, `section_cast`, and `section_mul_cast`.
The proof transports multiplication between equal internal group objects, applies
`AddCommGroup.ext` to identify bundled section groups, then uses the faithful forgetful
functor and `Functor.ext` to identify restrictions and presheaves. Sheaf witnesses agree
by proof irrelevance. Updated the existing node's proof and proof_origin to this argument.

## Proved and sorry left

Closed 1 hole: `CategoryTheory.sheafAbelianObjects_injective`
(node `lem-weil-pbc-sheaf-abelian-objects-bijective-injective`).
All three private helpers are proved. No holes added or split off; no `sorry` remains
in the delivered module. This is a proof, not a decomposition.
Compilation through `lcompile.py` passed without warnings. The dry-run tool also
checks axioms of the delivered declarations.

## No longer needed

No imports removed and no dependency nodes or modules pruned: the original node's
`proof_deps` was empty and the module had only statement-required Mathlib imports.
The injectivity proof needs only the multiplication clause of `hsections`:
`AddCommGroup.ext` determines zero, negation, subtraction and scalar operations from
addition. The unused clauses remain in the unchanged statement. Reconstruction of
an entire sheaf and the surjectivity part of the original docstring are unnecessary
for this item's proof. No blueprint unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing docstring discusses surjectivity as well as injectivity, but this module
states only injectivity. Its generic reconstruction plan is stronger than needed:
comparison of existing section groups suffices. The DAG record now describes the
actual Lean argument. No statement or definition was changed.

## Second reading by S2

1. Compared the delivered module with the repository version. The theorem signature and all existing declaration statements are unchanged; the only interface addition is the proof-only import `Mathlib.Algebra.Group.Ext` and private helpers.

2. Compiled the module with `lcompile.py`; it succeeds without warnings. There are no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern` declarations. The proof uses only the allowed equality transports and `AddCommGroup.ext`.

3. The proof closes the existing injectivity theorem directly. The private helpers are elementary equality-induction facts, are not split-off public statements, and no new DAG node is required. The node statement is unchanged and agrees with the theorem.

4. The proof follows the shortest available route: sectionwise multiplication identifies each additive group, then faithful forgetful maps and functor extensionality identify restrictions and the presheaf. No imports were removable beyond the original statement imports; the added import is proof-only. No proof dependency node is pruned.

5. The unit route is preserved: the injectivity node remains realized under `sk-def-exchange`; only the proof field and proof origin were updated to record the direct sectionwise argument.

Changed only the proof, the proof-only import, private helpers, the matching DAG proof metadata, and this report.
