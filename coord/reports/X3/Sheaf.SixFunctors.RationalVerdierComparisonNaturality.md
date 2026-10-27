## What changed

The parent theorem `WeilConjectures.RationalVerdier.localizedBeta_naturality` is now proved by
unpacking scalar-localized objects, applying `TensorProduct.induction_on` to the morphism,
and handling zero and addition by additivity. Its pure-tensor case invokes the new integral
pure-tensor comparison theorem. The new module
`Sheaf.SixFunctors.RationalVerdierIntegralBetaNaturality` records that strictly smaller
integral calculation as a named theorem with its source and proof plan.

## Proved and sorry left

Closed the original sorry in `localizedBeta_naturality` (1 of 1). Added one strictly smaller
split-off sorry, `WeilConjectures.RationalVerdier.integralBeta_naturality`, in the new helper
module and recorded it in node `lem-coef-rational-verdier-integral-beta-naturality`.

## No longer needed

The proof does not use the original planned completion/model and hom-reduction route. The
following planned dependencies are therefore pruned from this node's proof plan:
`def-sf-integral-finite-extension-models`, `lem-fix-constructible-tensor-completion`,
`lem-sf-cochain-tensor-model-rigidity`, and `def-sf-integral-hom-reduction-models`.
No existing public import was removed; the parent retains its model import and adds only the
private proof import of the new helper.

## Where the brief, the DAG or earlier work was wrong

The original DAG expanded the rational naturality argument into completion and derived
model comparisons. In the current definitions, rational morphisms are represented by a
TensorProduct, so the upper theorem reduces formally to zero/addition cases and one pure-
tensor integral calculation. This shorter route leaves the integral calculation as a
strictly smaller theorem and changes no target statement.

## New nodes

`lem-coef-rational-verdier-integral-beta-naturality` in
`Sheaf.SixFunctors.RationalVerdierIntegralBetaNaturality` is the integral pure-tensor
subcase used by the parent proof.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierComparisonNaturality": "3d79e54b9fde0b6d9af17262973d5fbf697ac193", "Sheaf.SixFunctors.RationalVerdierIntegralBetaNaturality": "54f48cd04c8542ae73a2b82e6ca09213d8f77de7"}, "results": {"Sheaf.SixFunctors.RationalVerdierExtension": {"hash": "eb03a68ef0c262d17b9fb672cbd50ff32a56c64c", "status": "OK"}}, "seconds": 23, "time": "2026-10-28T07:02:14+0800", "transitive": 0, "version": 1}
```

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
