## What changed

Proved `AlgebraicGeometry.fieldPoint_factorsThrough_immersion` by factoring an immersion through Mathlib's `liftCoborder` closed immersion and open immersion. The proof uses the closed-immersion residue-field isomorphism and field-point factorization theorem, then constructs and proves uniqueness of the open lift using `IsOpenImmersion.lift` and monomorphism cancellation.

## Proved and sorry left

The target theorem `AlgebraicGeometry.fieldPoint_factorsThrough_immersion` is proved. No `sorry` remains in the delivered module.

## No longer needed

The planned residue-field naturality, open-factorization, and open-immersion-monomorphism nodes are not needed explicitly: Mathlib's `liftCoborder`, `IsOpenImmersion.lift`, and the `Mono` instance for immersions supply these steps.

## Where the brief, the DAG or earlier work was wrong

The DAG plan was longer than necessary. Mathlib already provides the canonical closed-then-open factorization of an immersion and the open lift operation, so the separate custom open-factor nodes can be pruned for this proof.

## Second reading by V2

1. Compared the delivered module with the repository version. The theorem statement and all existing declarations are unchanged; only the proof body was filled.
2. Compiled the module locally. It compiles without errors and contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The proof uses only the permitted foundational axioms through its imported results.
3. The target proof follows the stated closed-then-open immersion factorization. The two imported closed-immersion results are used, while the open lift and monomorphism facts come from Mathlib; no new split-off statement was added.
4. The proof is pruned to the Mathlib factorization and lift route. The planned custom residue-field naturality, open-factorization, and open-monomorphism nodes are unused and are recorded above as no longer needed.
5. The DAG node's proof, proof dependencies, and proof origin agree with the Lean proof, and the unit route remains realized through the target node.

Changed only the proof (plus the second-reading record); no statement, definition, import, or DAG statement was changed.

The linter option change is recorded in `coord/changes/field-point-factors-through-immersion-linter.md`.
