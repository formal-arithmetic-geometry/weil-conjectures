## What changed
Added the existence of a stable locus as a named intermediate result with a documented `sorry`, and proved the requested specialization theorem by applying it.

## Proved and sorry left
Proved `Smooth.section_component_generalization_of_isNoetherian`. The only remaining sorry is `Smooth.exists_noetherian_section_component_stable_locus`, recorded in node `lem-sbc-smooth-section-component-noetherian-generalization-core`.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The planned geometric argument is substantial and is represented as the named core intermediate theorem.

## New nodes
`lem-sbc-smooth-section-component-noetherian-generalization-core` records the unresolved geometric stability argument.

## Second reading by G1

1. **Statements unchanged.** Compared the delivered module with the repository version. The
   existing target declaration has the same signature byte for byte; the only added declaration
   is the documented split-off core theorem recorded by its DAG node.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it compiles cleanly after
   formatting. The target proof is a direct application of the split-off theorem. The remaining
   `sorry` occurs only in the named public theorem and is not inside a definition. No unsafe
   declarations or extra axioms were introduced.
3. **Split-off statement.** Checked the stable-locus theorem against the noetherian geometric
   argument in Stacks Tag 055Q. Its hypotheses and conclusion state exactly the needed
   intermediate result, with a source, proof description, and matching DAG node.
4. **Pruning and route.** The module needs only `Mathlib.AlgebraicGeometry.Morphisms.Smooth`;
   no proof-only imports were present to remove, and the unit route is preserved through the
   noetherian core theorem.
5. **DAG agreement.** The node's Lean declaration, statement, proof origin, and dependency
   metadata agree with the delivered file. No existing declaration or target statement was
   weakened or altered.

Changed the split theorem formatting only; no mathematical statements or imports were changed.
