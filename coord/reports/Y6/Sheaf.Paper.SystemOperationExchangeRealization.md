## What changed

Reduced `WeilConjectures.FrobeniusExchange.directAlpha_isIso` to the strictly earlier
geometric whole-system reconstruction step in its existing source proof. The new
`WeilConjectures.systemDirectImage_effective` states that the actual reconstruction
counit is invertible on the system direct image of a coherent constructible reduction.
It has no horizontal map or alpha comparison. The parent proof composes its functorial
images with the already constructed pullback realization isomorphism.

This is a decomposition, not a net proof. The geometric statement is in one new module
with its source, complete proof in words and matching DAG node. No statement, definition,
public import or blueprint unit route changes. No other existing module is changed.

## Proved and sorry left

One of eight original holes is closed by reduction:
`WeilConjectures.FrobeniusExchange.directAlpha_isIso`.
One strictly earlier hole is added:
`WeilConjectures.systemDirectImage_effective`.
Net holes closed: zero. This delivery is one decomposition and zero complete proofs
of the original geometric obligations.

The seven original holes left are:

- `WeilConjectures.FrobeniusExchange.systemDirectEvaluation_isIso`
- `WeilConjectures.FrobeniusExchange.systemExchange_evaluation`
- `WeilConjectures.FrobeniusExchange.systemOpenEvaluationInv_isIso`
- `WeilConjectures.FrobeniusExchange.systemOpenExchangeInv_isIso`
- `WeilConjectures.FrobeniusExchange.systemOpenScalarInv_isIso`
- `WeilConjectures.FrobeniusExchange.directImage_roos`
- `WeilConjectures.FrobeniusExchange.compactRealization_existsUnique`

The delivered item has seven holes; the new module has one named theorem hole.
No definition contains a hole.

## No longer needed

No existing import, module or declared dependency is pruned. The alpha combination
requires no new theorem about pulling limits along a scheme isomorphism: the pullback
realization is already an isomorphism, and the remaining functors preserve the new
whole-system counit isomorphism. The new obligation concerns the actual counit before
pullback, not merely its finite evaluations or its image under the total limit.

## Where the brief, the DAG or earlier work was wrong

The current item source exists and is preserved with its full Lean attachment. The
rework row records a historical transitive dependency on `SfP1ProjectionTraceFalseTail`;
the item itself does not directly import it. No quarantine archive or module was
withdrawn to satisfy that record.

The proof of directAlpha_isIso separates into whole-system effectivity and a categorical
composition. The latter is now complete Lean. The former retains the simultaneous
resolution, quotient-transition, finite reduction and normalized reconstruction work
from the original source proof; it is not another name for alpha invertibility.

## New nodes

- `lem-weil-system-direct-image-effectivity`, realized by
  `Sheaf.Paper.SystemDirectImageEffectivity`: effectivity of the actual reconstruction
  counit on the derived direct image of one coherent quotient system. Its statement
  is independent of a horizontal pullback and the alpha construction.

## Second reading by Y6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
