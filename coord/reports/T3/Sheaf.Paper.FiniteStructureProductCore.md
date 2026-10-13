## What changed
Pruned the vacuous compatible-family split: a constant zero family supplies the required compatible family directly. The target now invokes only `finite_structure_product_section_identity` with that family. Retained the section-identity theorem as the sole unresolved algebraization step.

## Proved and sorry left
`AlgebraicGeometry.finite_structure_product_exists_core` is proved. The only sorry left is `AlgebraicGeometry.finite_structure_product_section_identity`, recorded by node `lem-weil-pbc-finite-structure-section-identity`. No new sorry remains for compatible-family existence.

## No longer needed
Removed the split declaration and node `lem-weil-pbc-finite-structure-compatible-family`; the constant family `(fun _ => 0)` and `rfl` compatibility proof make it unnecessary.

## Where the brief, the DAG or earlier work was wrong
The earlier delivery introduced a compatible-family theorem whose conclusion is immediate from the zero morphism and duplicated the target's full interface. It was not a meaningful lower statement, so it was removed. The remaining theorem isolates the genuinely unresolved Grothendieck-existence and section-evaluation step.

## Second reading by T3
1. Compared the delivered module with the repository: the existing target declaration and all definitions retain byte-for-byte signatures; only the proof and the retained split declaration were added.
2. Compiled the module successfully with `lcompile.py`; the only remaining `sorry` is the named theorem above, with no axioms or forbidden declarations introduced.
3. Checked the retained statement against the target: it adds the compatible family as input and therefore is strictly more specialized; its node records the source, proof route, and dependency. The vacuous compatible-family statement was removed.
4. The proof uses the constant zero endomorphism family, so no imported compatible-family result is needed; the section identity remains the planned Grothendieck-existence route.
5. DAG metadata and Lean declaration agree after pruning; no unused split node remains.

## New nodes
`lem-weil-pbc-finite-structure-section-identity` records the unresolved algebraization and section-evaluation theorem in this module.
