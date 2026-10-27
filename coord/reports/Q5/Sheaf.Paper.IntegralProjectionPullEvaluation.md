## What changed

Prove `WeilConjectures.IntegralProjectionReduction.integralProjectionPullEvaluation`
from the prescribed quotient, Roos, and finite evaluation normalizations. Proved
helpers compute the published pullback model directly, then the datum's
`pullProjection` equation supplies the required finite comparison. No existing
statement or definition is changed. Update the item's DAG proof and dependencies.
The tower and counit calculations are in three new modules so each file meets the
compile-time limit; they introduce no new holes.

## Proved and sorry left

Closed: `WeilConjectures.IntegralProjectionReduction.integralProjectionPullEvaluation`
(one original hole). Added: none. Sorry left in the delivered modules: none.
All new public and private helpers have complete proofs. The new public declarations
are `WeilConjectures.IntegralPublishedPullback.finite_evaluation_component`,
`WeilConjectures.IntegralPublishedPullback.published_tower_finite_component`, and
`WeilConjectures.IntegralPublishedPullback.published_counit_finite`.

## No longer needed

Removed the unused proof import of `IntegralAmbientOperationModels` from the finite
factor module, and the unused `MapDerivedCategoryMate` import from the tower module.
The strict-component import in the finite factor module is private to its proof.

The planned direct dependency on
`lem-pod-integral-pullback-counit-projection`
(`Sheaf.Paper.IntegralPullbackCounitProjection`) is unnecessary: that theorem is
formulated with another chosen normalized model. Compute the published model's
projection directly using its existing uniqueness and normalization equations.
No module is withdrawn, and this observation does not claim that the dependency
is unused elsewhere. The statement dependencies and the unit route are retained.

## Where the brief, the DAG or earlier work was wrong

The original plan leaves an identification between the normalized realization in
`integralPullbackCounitProjection` and `pullbackTensorIntegralPullbackModel`
implicit. The proof avoids that identification by calculating directly with the
published model. The theorem's statement is unchanged. The argument includes the
zero object and the first finite level `m = 0`; it uses K-flat representatives,
not flatness of a quotient.

A whole-DAG traversal also encountered an existing cycle, unchanged by this packet:
`lem-weil-pbc-derived-exchange-termwise` →
`lem-weil-pbc-derived-exchange-unbounded-transport` →
`lem-weil-pbc-derived-exchange-bounded-comparison` →
`lemma-weil-pbc-derived-exchange-replacement` →
`lem-weil-pbc-derived-exchange-termwise`. None of the new dependency edges returns
to its originating node.

## New nodes

- `lem-sf-integral-published-finite-evaluation` records the proved exact restriction
  and finite representative evaluation factor identities in
  `Sheaf.Paper.IntegralPublishedFiniteEvaluation`.
- `lem-sf-integral-published-tower-evaluation` records the proved Roos projection,
  limit/Roos bridge projection, and strict finite tower evaluation calculation in
  `Sheaf.Paper.IntegralPublishedTowerEvaluation`.
- `lem-sf-integral-published-counit-evaluation` records the proved finite evaluation
  of the published pullback model followed by the reconstruction counit in
  `Sheaf.Paper.IntegralPublishedCounitEvaluation`.

These are proved steps of the original argument, with no split-off obligations.

## Second reading by Q5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
