## What changed

Proved `WeilConjectures.RationalTwistedPullback.component_naturality` in
`Sheaf.Paper.RationalTwistedPullbackCompositor`. Private proved helpers establish
pullback-compositor naturality on pure tensor arrows and sums, transfer
associator naturality through faithful coherent reduction, and then localize the
associator square. The main proof pastes three natural isomorphisms whose
components are precisely the existing canonical factors.

Added the proof-only import `Sheaf.Paper.IntegralSystemReductionFullyFaithful`.
All existing declarations, signatures, definitions and public imports are preserved.
Updated the existing node's proof fields to record these naturality calculations.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.RationalTwistedPullback.component_naturality`
(node `def-pur-rational-twisted-pullback-compositor`).
No holes added or split off. No `sorry` remains in the delivered module.
The proof uses existing statements with their existing proof dependencies;
it does not claim those dependencies are all axiom-free.

## No longer needed

None. All three original public imports support the existing constructions.
The node had no listed proof dependencies to prune. No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The definition node had empty proof fields, although it included the naturality
obligation. These fields now describe the proof. No mathematical statement or
canonical comparison required repair. The unit's statement and route are preserved.

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
