## What changed

The assigned `reductionPairing` hole is decomposed into three strictly simpler named
compatibility-square statements in separate modules: the signed bidual square, the finite
internal-Hom reduction square, and the finite Verdier reduction square. The item imports
those modules and proves its conjunction by applying their statements. The original target
signature and all canonical definitions are unchanged.

## Proved and sorry left

The original `reductionPairing` declaration is proved from the three named component
theorems. Three split-off theorem holes remain, one in each new module:

- `WeilConjectures.IntegralFiniteExtension.CoefIntegralFiniteExtensionDeltaSquare`
  (`lem-sf-integral-finite-extension-delta-square`);
- `WeilConjectures.IntegralFiniteExtension.CoefIntegralFiniteExtensionHomReductionSquare`
  (`lem-sf-integral-finite-extension-hom-reduction-square`);
- `WeilConjectures.IntegralFiniteExtension.CoefIntegralFiniteExtensionBetaReductionSquare`
  (`lem-sf-integral-finite-extension-beta-reduction-square`).

No `sorry` remains in the assigned item module itself.

## No longer needed

No imports or declared proof dependencies were pruned; each component uses the same Core
comparison data and hypotheses required by its displayed square.

## Where the brief, the DAG or earlier work was wrong

The previous split left this lower lemma as one large three-conjunct hole. The current
split is a finer decomposition into the three independent squares already listed in the
node's proof plan; no statement is weakened.

## New nodes

The three new node files in `dag/nodes/sec-six-functors/` record the component statements,
their source paragraphs, and their corresponding Lean declarations.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionBetaReductionSquare": "e9bc055b7b2428d1c1a68c75837fd719cb27786a", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionDeltaSquare": "455701758175dfa4e86ff015fa56d750a616fa0c", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionHomReductionSquare": "34ed5b216357820b46e33d90f12c2323423b27a7", "Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing": "2b784b1215f0423449be5c100624ed7b610ba08b"}, "results": {}, "time": "2026-10-28T00:57:16+0800", "transitive": 0, "version": 1}
```

## Second reading by H5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
