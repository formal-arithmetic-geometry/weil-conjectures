## What changed

Added the integral-representative evaluation lemma in
`Sheaf.SixFunctors.RationalVerdierComparisonEvaluationIntegral` and used it to
transport the equality to every raw rational object. The main theorem now
compiles with a proof that destructs the unchanged scalar-localization object
and converts the representative heterogeneous equality to the required equality.

## Proved and sorry left

Closed `normalizedExtension_evaluation` (1 of 1 original holes). Added the
strictly simpler intermediate theorem `normalizedExtension_evaluation_integral`,
whose proof remains `sorry` and records the representative-level calculation.

## No longer needed

None. The main proof uses the rational models and the new integral representative
node; all imports retained by `RationalVerdierModels` remain part of the public
statement interface.

## Where the brief, the DAG or earlier work was wrong

The original node's proof plan omitted a Lean-level statement for the integral
representative calculation. The final objectwise theorem can be reduced to that
strictly simpler HEq statement by the fact that `ScalarLocalization` wraps an
unchanged integral object, but the representative calculation itself must be a
separate named theorem.

## New nodes

`lem-coef-rational-verdier-comparison-evaluation-integral` — integral
representative evaluation compatibility used by the delivered theorem.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalVerdierComparisonEvaluation": "196e72a39aa1a5e37100add2794fbcdceb0566b2", "Sheaf.SixFunctors.RationalVerdierComparisonEvaluationIntegral": "8dad9f82de2feade1941f0e588c08dac212432d9"}, "results": {}, "time": "2026-10-28T06:48:56+0800", "transitive": 0, "version": 1}
```

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
