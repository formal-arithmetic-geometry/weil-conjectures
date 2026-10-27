## What changed

Proved `AlgebraicGeometry.Scheme.strictLocalComparison_indEtale` in
`Sheaf.AlgebraicGeometry.StrictLocalComparisonIndEtale` with its complete original signature.
The proof factors each structural map through its chart using generalization from the closed
point of a local spectrum. Cancelling the first chart's open immersion proves compatibility
for every pair of factorization maps. The existing small-model chart theorem gives their
ind-etaleness, and composition and relative permanence give the remaining two assertions.
A proved private ULift equivalence handles the universe-transport predicate. Limit
extensionality identifies the residue formula with point evaluation; the canonical pointed
equation then proves locality. All helpers are private and completely proved.

Added the proof-only import `Sheaf.Paper.StrictHenselizationPointEvaluationPointed`.
Updated the item's DAG proof and dependencies to match this route. No other existing module,
public signature, definition, public import or unit route changes.

Validation: the complete module compiled through `lcompile.py` with exit code 0 in
7.1 seconds and no warnings. The delivery tool performs the required preflight and axiom checks.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.strictLocalComparison_indEtale`
(node `lem-trf-strict-local-comparison-ind-etale`).
Original holes: 1. Remaining holes in the item: 0. Added holes: 0. Split off: 0.
The proof uses existing declared dependencies; this does not assert that all transitive
proof dependencies are already free of sorry.

## No longer needed

Removed the proof-only import `Mathlib.AlgebraicGeometry.Morphisms.Etale`.
Removed proof dependencies `lem-weil-pbc-etale-composition-cancellation` and
`def-weil-pbc-pointed-etale-neighbourhoods`: the argument no longer constructs chart objects
in the pointed etale neighbourhood category or transports their representatives.
The closed-point property and open-immersion lifting give the factorizations directly.
No separate invocation of the neighbourhood-compatibility clause (4) is needed, since the
structural square and cancellation give the required ring-map equation.
The strict-local limit, structural map, affine spectrum, small-model chart theorem,
functoriality and ind-etale stability remain used. No module is withdrawn; the two removed
proof dependencies can still be needed by the underlying definitions and other consumers.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The DAG's transport of chart objects through the chosen
representative category was unnecessary for this open-chart case. Its conclusions follow
from the closed-point clause of its already declared functoriality dependency. The original
small-model and universe parameters remain unchanged.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
