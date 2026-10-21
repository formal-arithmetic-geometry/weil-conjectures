## What changed

Proved `AlgebraicGeometry.ProEtale.PrincipalReduction.principalReductionConeData`
from the existing `principal_reduction_cone_calculus` theorem in the same module.
The proof packages its strict data into `PrincipalReductionConeData`, then supplies
its scalar test and the same coherent shift, cone, and derived comparison witnesses
at each test. All coordinate identities, units, transitions, and normalization
clauses are retained. No declaration signature, definition, or import changed.

## Proved and sorry left

Closed one of the two original direct holes:
`AlgebraicGeometry.ProEtale.PrincipalReduction.principalReductionConeData`.

One direct hole remains:
`AlgebraicGeometry.ProEtale.PrincipalReduction.principal_reduction_cone_calculus`
(node `lem-pe-principal-reduction-cone-calculus`). The proved packaging theorem
still depends on this hole; the complete principal cone calculus is not claimed
axiom-free. No holes were added and none were split off.

## No longer needed

None. Imports and the dependencies of the remaining main theorem are retained.

## Where the brief, the DAG or earlier work was wrong

The structured interface had a second independent `sorry` despite being a direct
logical consequence of the full theorem. This delivery removes that duplicate
obligation. It does not replace either declaration or alter the planned
mathematics of the remaining theorem.

## Second reading by M5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
