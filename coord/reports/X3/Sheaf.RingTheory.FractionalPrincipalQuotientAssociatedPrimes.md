## What changed
Split the theorem into independently stated height-one and minimal-prime components, and proved the original theorem by combining those components.

## Proved and sorry left
The target `Ideal.associatedPrimes_fractionalPrincipalQuotient` is proved. The component declarations `Ideal.associatedPrimes_fractionalPrincipalQuotient_height` and `Ideal.associatedPrimes_fractionalPrincipalQuotient_minimal` remain as named `sorry`s for parallel proof.

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The original direct injection argument is substantially larger than the available proof window; the two component statements expose its independent mathematical obligations without changing the target interface.

## New nodes
`lem-weil-pbc-normal-domain-fractional-principal-quotient-ass-height` and `lem-weil-pbc-normal-domain-fractional-principal-quotient-ass-minimal`.

## Earlier second reading (a previous round; superseded)
The sandbox modules compile with `lcompile.py --all`; the target combines the two strictly smaller component conclusions.

## Second reading by X3

1. The target statement is byte-for-byte unchanged from the repository. The two new component statements are strict conjunct projections of the target and do not alter existing declarations.
2. All three delivered Lean files compile with `lcompile.py --all`. There are no axioms, unsafe declarations, or hollow definitions; the target proof depends only on the two explicitly named component holes (and therefore reports `sorryAx` until those components are proved).
3. The component statements are true consequences of the source clause and are strictly simpler than the conjunction. Their source, proof descriptions, and DAG nodes are present; no duplicate Mathlib or library declaration was found.
4. The target proof follows the split route and retains the unit route. No imports were removed; the two component imports are proof-only plain imports.
5. The target node proof and `proof_deps` now match the Lean proof, and the new nodes match their declarations. No statement or definition was changed.

Changed the target DAG proof metadata and added this second-reading record. The target remains a decomposition with two named sorry components, as reported above.
