## What changed

Filled `AlgebraicGeometry.Scheme.completedKoszulReductionRoosTriangle` without
changing its statement or any existing public definition. The proof transports
the native Koszul fiber through the completed coefficient equivalence, uses the
existing normalized Koszul/quotient comparison and strict quotient normalization,
and reflects the actual Roos triangle through the derived coefficient equivalence.
Private proved helpers supply the quotient transition squares and the specified
model's derived adjunction unit calculation. All added imports are proof imports.
The node's proof and proof dependencies now describe these calculations.

Validation: the complete refactored module compiles through `lcompile.py` in
50.0 s with normal linters enabled and no increased heartbeat limit. The only
warning was the profiling option, removed from the delivered source. Generic
categorical helpers perform the pointed comparison and normalized Roos transport;
the concrete coefficient proof supplies their equations. Earlier delivery attempts
timed out and pushed nothing. The declaration comparison reports no changed
statement or public import. No diagnostic probe remains in the source.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.Scheme.completedKoszulReductionRoosTriangle`
(node `lem-weil-pbc-completed-koszul-reduction-roos-triangle`).
Added holes: zero. Holes remaining in the delivered module: zero.
No statements were split off. Existing dependency theorems are used with their
stated hypotheses; their proofs remain separate project items.

## No longer needed

No original import, declared dependency, node, or module is pruned. In particular,
the original Koszul comparison, intrinsic descent, coefficient comparisons, and
Roos triangle route are retained. An exploratory proof import of
`Sheaf.Paper.ActualCompletedReductionReconstruction` was removed before delivery:
only elementary restriction identities were needed, and these are proved locally.
This exploration did not change the repository's import closure.

## Where the brief, the DAG or earlier work was wrong

The planned normalization needs the already stated
`completedQuotientUnitNormalization` to pass from the derived reduction tower to
the strict quotient tower. The DAG now records that dependency explicitly. The
quotient transition compatibility also uses the existing coefficient equivalence
module's generic adjunction transport and surjective projection lemmas; its
node is now recorded. No mathematical statement was corrected.

The exact restriction comparison is computed using its localization factorization
on complexes. The final model equation follows from the defining hom-equivalence
formula of `adicDatumAdjunction_exists`, rather than an unproved claim that two
arbitrarily chosen adjunctions have identical units.

The launcher resumed this same sandbox with a fresh reference clock
(`.budget` start 1792769089.101973); no budget metadata was edited by the worker.
The previous interrupted work and all proof experiments were retained.

## Second reading by U5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
