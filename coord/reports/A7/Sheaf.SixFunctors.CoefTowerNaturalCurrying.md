## What changed

Marked `WeilConjectures.coefTowerNaturalCurrying` STATEMENT-DISPUTED while
preserving its signature, definitions, imports and original proof hole. Added the
new module `Sheaf.SixFunctors.CoefCurryingTraceTwist`, which proves an elementary
normalization test for arbitrary compact-support trace comparisons.

## Proved and sorry left

Holes closed: 0 of 1. Holes added: 0. The remaining hole is
`WeilConjectures.coefTowerNaturalCurrying` (node `lem-coef-tower-natural-currying`).
The new declaration `WeilConjectures.coefCurrying_trace_twist` is proved with no
sorry. This is a diagnostic counterexample to the unrestricted trace-normalization
step, not a replacement theorem.

## No longer needed

No imports, nodes, modules or unit steps are pruned. The diagnostic module has only
Mathlib imports and does not alter the item dependency closure.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: `eTrace` is an arbitrary isomorphism of compact-support values,
with no requirement that it preserve the dualizing exceptional counit. On two
components, the invertible map e(x,y)=(x-y,y) changes the sum trace to first
projection, which annihilates the second component. Thus an isomorphism of compact-support objects alone does not justify
invertibility of the finite duality arrow. The full scheme-level counterexample,
including the freedom in existential model witnesses, needs independent review. The proved
`coefCurrying_trace_twist` theorem records this algebraic test, including the
nonzero second basis vector and characteristic-two edge case. The route should supply a
counit-preserving trace comparison before using finite mapping adjunction for
step 5. No formal refutation of the complete existential theorem is claimed.

The newest blueprint was read through literature/blueprint/latest/: its adjunction
uses the actual exceptional counit, and identifies the finite adjunctions with
that counit. A previous interrupted draft asserting invertibility for every model
and omegaOrigin was removed after this edge-case test; it is not delivered.
Attempts to formalize the independent naturality and detection steps in the large
item reached the fixed compile time limit, including profiling and declaration
markers that produced no output. Those unverified helpers are not delivered.
No original definition or statement is weakened to make the theorem provable.

## New nodes

`lem-coef-currying-trace-twist` records the proved elementary linear-algebra test
and its source in the finite pairing normalization step.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
