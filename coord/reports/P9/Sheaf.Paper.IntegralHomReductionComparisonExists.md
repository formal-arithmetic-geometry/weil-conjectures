## What changed

Proved `WeilConjectures.IntegralHom.reduction_comparison_exists` in
`Sheaf.Paper.IntegralHomReductionComparisonExists`, preserving its signature and public import.
Added two proof imports: `Sheaf.Algebra.Homology.ScalarTensorComparisonTransport` and
`Sheaf.Algebra.Homology.RingedDerivedTensorHomAdjunction` (both with `import all`, to reuse
proved private helpers). No other existing Lean module changes.

The private, fully proved `tensorModelIso` identifies each supplied tensor presentation with
the generic coefficient tensor by fully faithful restriction along the K-flat product
localization. The theorem obtains the already proved fixed scalar tensor comparison and
conjugates it by those two tensor identifications. All coefficient and site universes remain
independent. The DAG proof and proof dependencies now describe this argument.

## Proved and sorry left

Closed 1 of 1 original holes:
`WeilConjectures.IntegralHom.reduction_comparison_exists`
(node `lem-sf-integral-hom-reduction-comparison-exists`).
No holes remain in the item. No holes or split-off statements are added.
The helper `tensorModelIso` is fully proved using localization.

## No longer needed

The planned direct use of `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
(`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`) is unnecessary: the existing
same-site scalar tensor comparison already supplies the needed coefficient extension iso.
No geometric inverse image or flat-term tensor-model conversion is needed.

`lem-weil-derived-scalar-extension-restriction-adjunction` is no longer a direct proof
premise: the fixed scalar transport uses the universal left-derived counit instead.
Its module remains available through the unchanged public import of
`IntegralHomReductionModels`; its adjunction is also used transitively by the generic
scalar models. This delivery does not withdraw that module or any other module.

No original Lean imports are removed. The trial explicit Mathlib localization-product
import was removed because the two proof imports already expose that API.

## Where the brief, the DAG or earlier work was wrong

The comparison did not need another split. Existing generic scalar tensor transport and
K-flat localization already suffice, even for arbitrary supplied source and target tensor
presentations. Their representative fields identify the tensors naturally in both variables;
no extra naturality of the presentation's separately supplied adjunctions is assumed.
No statement, definition, public attribute or unit route was changed.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 1 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.Paper.IntegralHomReductionComparisonExists": "9206258cb2a79d62e651348cbb1d368421438297"}, "results": {"Sheaf.Paper.IntegralHomReductionNormalization": {"hash": "eaf89bc43be9a1979aded47e5b25bf27ec691d65", "status": "INFRA"}, "Sheaf.Paper.IntegralHomReductionNormalizationData": {"hash": "16489e89a79fe6da8fbc611715ee174962ad6d55", "status": "OK"}}, "seconds": 84, "time": "2026-10-28T12:03:01+0800", "transitive": 0, "version": 1}
```

## Second reading by P9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
