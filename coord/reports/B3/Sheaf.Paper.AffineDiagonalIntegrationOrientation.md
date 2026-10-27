## What changed

Added two split-off theorem modules for the integration and transpose conjuncts of the
translation clause. The parent theorem now combines those two component statements.
The existing proved declarations are `affineDiagonalIntegration_exponent` and
`affineDiagonalIntegrationOrientation`.

## Proved and sorry left

The translation conjunction hole was decomposed and closed in the parent by combining
`affineDiagonalIntegration_translation_integration` and
`affineDiagonalIntegration_translation_transpose`. The two new component declarations each
retain one documented `sorry`; the rank-zero hole remains in
`affineDiagonalIntegration_zero`. Thus this delivery adds 2 split-off sorries and leaves 3
module-closure sorries across the three delivered modules. The existing
`affineDiagonalIntegration_exponent` and `affineDiagonalIntegrationOrientation` are proved.

## No longer needed

No imports, nodes, or modules were pruned in this delivery.

## Where the brief, the DAG or earlier work was wrong

No statement or proof dependency was changed. The two pending theorem proofs require the
recorded translation and rank-zero normalization arguments and are left for a later proof
pass.

## New nodes

`lem-pur-affine-diagonal-integration-translation-integration` and
`lem-pur-affine-diagonal-integration-translation-transpose` are the two strict conjuncts
of the original translation theorem. Their Lean modules carry the corresponding documented
`sorry` obligations, and the parent theorem is proved by combining these two statements.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
