## What changed

Proved `ContinuousCohomology.CosetResidual.coset_averaged_homogeneous_residual`
in `Sheaf.RepresentationTheory.CosetAveragedHomogeneousResidual`. The statement,
all eight concrete constructions, and the public imports are unchanged.

Private proved helpers implement evaluation on free integer tuple chains,
cancellation of paired deletions, right-transversal reindexing, continuity,
linearity, and the fixed evaluation formulas. Evaluating the supplied homotopy
gives the unaveraged decomposition. Applying the differential gives the residual
cocycle equation; applying normalized averaging gives the averaged identities.
The support hypothesis proves vanishing independently of the cocycle condition.
The coset permutation argument follows the already-proved local argument in
`FiniteCosetHomogeneousAveraging`, without importing its larger cochain interface.

Validation: the complete single-file proof compiled through `lcompile.py` in
10.2 seconds. The delivery gate independently compiles the final file and checks
its declarations for forbidden axioms and remaining holes.

## Proved and sorry left

Closed the single original hole:
`ContinuousCohomology.CosetResidual.coset_averaged_homogeneous_residual`
(node `lem-sfb-coset-averaged-homogeneous-residual`).

No holes remain. No holes or new statements with postponed proofs were added.
This is a proof, not a decomposition.

## No longer needed

None: no imports, modules, or DAG dependencies were removed. The existing
nine-step finite-sum proof route and the unit route are retained. No new proof
imports are needed. The unchanged hypotheses `hA0`, `hQ0`, and `hchain` are
redundant for this residual argument: the displayed homotopy identity and
squared-zero differential already imply the required cocycle equation.

## Where the brief, the DAG or earlier work was wrong

No mathematical discrepancy was found. The auxiliary statement is proved by
the agent-written finite-sum argument already recorded in its node. Searches
through Lean Finder, Loogle, the pinned Mathlib sources, and both library roots
found useful finite-index and deletion APIs but no theorem giving this complete
residual statement directly. No statement or definition repair was needed.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
