## What changed

The target theorem now compiles by assembling two strictly simpler public statements. `exists_integral_reindexing_maps` supplies the family of balanced `IntegralReindex` maps, and `exists_realization_comparison_descent` supplies the common-stage natural isomorphism and all `integralRealizationAgreement` equations once that family is given. The target packages those outputs without changing its statement. The target proof route in the copied DAG node records this decomposition.

## Proved and sorry left

Closed one target sorry: `WeilConjectures.AdicQbarRealization.exists_integral_realization_reindexing`.

Added two strictly simpler split-off sorries:

- `WeilConjectures.AdicQbarRealization.exists_integral_reindexing_maps`, the balanced integral reindexing family construction.
- `WeilConjectures.AdicQbarRealization.exists_realization_comparison_descent`, the common-stage comparison and representative-agreement descent with the family supplied as input.

Both split statements are genuine subarguments of the original proof and compile in their own modules.

## No longer needed

No imports were removed and no declared lower dependency was pruned. The original coefficient, inverse-image, derived-comparison, scalar-extension, and algebraically-closed-coefficient dependencies remain attached to the two split proof plans, where their eventual proofs will use them.

## Where the brief, the DAG or earlier work was wrong

The original node bundled the finite quotient construction, the realization comparison, and scalar descent into one theorem. That bundle was too large to make into Lean in this item. The route is therefore decomposed at the two mathematical interfaces: construction of the `IntegralReindex` family, then comparison descent given that family. Neither split statement repeats the target: the first has no realization comparison, and the second takes the integral family as an explicit input.

## New nodes

- `lem-sf-adic-integral-reindexing-maps` in `dag/nodes/sec-six-functors/lem-sf-adic-integral-reindexing-maps.json`.
- `lem-sf-adic-realization-comparison-descent` in `dag/nodes/sec-six-functors/lem-sf-adic-realization-comparison-descent.json`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdicIntegralReindexingDescent": "6ec8ec034cbf312bd88caba1ee1571de4b518c20", "Sheaf.Paper.AdicIntegralReindexingMaps": "3e72978097d18b751798417dfbb379fcfab0efec", "Sheaf.Paper.AdicRealizationComparisonDescent": "e33bd520899a22afe5f2fa34fcd823adfb0d2bff"}, "results": {}, "time": "2026-10-28T06:38:02+0800", "transitive": 0, "version": 1}
```

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
