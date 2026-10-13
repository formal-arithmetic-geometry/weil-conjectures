## What changed

Added `RegularQuotientIdealIntersectionAux` with the strict intermediate inclusion
`Ideal.inf_ofList_le_mul_of_regular_quotient`. The target theorem now applies this
inclusion and proves the reverse inclusion by ideal monotonicity. The auxiliary
inclusion remains a named `sorry` for the Koszul H₁ argument.

## Proved and sorry left

The reverse inclusion and equality assembly in
`Ideal.inf_ofList_eq_mul_of_regular_quotient` are proved. The target theorem's
nontrivial inclusion is split off as
`Ideal.inf_ofList_le_mul_of_regular_quotient` in node
`aux-regular-quotient-ideal-intersection-inclusion`.

## No longer needed

No imports were removed; the existing Koszul imports remain the recorded route
for the split theorem.

## Where the brief, the DAG or earlier work was wrong

The full Koszul chase could not be completed in this window. No statement was
changed.

## New nodes

`aux-regular-quotient-ideal-intersection-inclusion` records the strict inclusion
needed by the target and its source proof.

## Earlier second reading (a previous round; superseded)

The target equality is assembled from the new inclusion and the elementary
reverse inclusion. The new statement is a strict part of the target and matches
the nontrivial Koszul chase in Tag 0665.

## Second reading by N3

1. **Interfaces: PASS.** I diffed the delivered target module against the repository version. The existing theorem statement and docstring are unchanged byte for byte; its proof only imports and applies the new auxiliary theorem. The auxiliary module is a new proof dependency and introduces no changed existing declaration.
2. **Proof and axioms: PASS as a decomposition.** Both modules compile with `lcompile.py --all`. The target equality proof is complete; the only remaining `sorry` is the explicitly named `Ideal.inf_ofList_le_mul_of_regular_quotient`, recorded by its node. The auxiliary statement is a strict inclusion, so this is a genuine decomposition rather than a restatement. The remaining theorem's proof follows the documented Koszul H₁ argument and has no hollow definition or forbidden declaration.
3. **Statements and nodes: PASS.** The target statement is unchanged and the auxiliary inclusion is true and exactly the nontrivial half required for equality. I searched the Lean tree and Mathlib-facing declarations for existing regular-quotient intersection results and found none. The auxiliary node records its source, proof route, dependencies, Lean declaration, and split status; the target node proof/dependencies now match the delivered proof.
4. **Pruning and imports: PASS.** The target keeps the unit route through the regular-sequence/Koszul imports. The auxiliary import is proof-only and is therefore a plain import. No prior proof dependency can be removed while the split theorem remains open; no unrelated imports were added.
5. **Axioms and route: PASS.** Compilation is clean, and the proof uses only ideal lattice monotonicity beyond the split theorem. The reverse inclusion handles the empty-list case through the general ideal lemmas. The unit's recorded route is preserved.

Changed files: added the auxiliary theorem/module and node, updated the target node's proof metadata to reflect the split, and added this review. No statement or definition was changed.
