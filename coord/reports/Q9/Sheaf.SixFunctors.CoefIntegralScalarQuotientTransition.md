## What changed

Proved `quotient_reduction_transition` from injectivity of the target normalized DVR scalar adjunction hom equivalence. Added the proof-only import and split-off module `Sheaf.SixFunctors.CoefIntegralScalarQuotientTransitionTranspose`, whose transpose equality is the remaining mate calculation. Updated the item node proof route and dependencies and added the corresponding DAG node.

## Proved and sorry left

The item theorem `WeilConjectures.IntegralFiniteExtension.quotient_reduction_transition` is proved. One strictly simpler intermediate theorem remains sorry: `quotient_reduction_transition_transpose` in node `lem-sf-integral-scalar-quotient-transition-transpose`.

## No longer needed

No imports from the original item were removed. The proof uses the scalar reduction exchange, finite extension models, and normalized DVR transition declarations; all remain needed. No additional planned dependency was pruned.

## Where the brief, the DAG or earlier work was wrong

The prior item imported `Sheaf.SixFunctors.CoefScalarReductionExchange` as a public import, but the current global build quarantined that dependency path and reported the import as bad. The item source itself is retained unchanged in the sandbox; the proof-only helper is imported privately and compiles against the current published artifact.

## New nodes

`lem-sf-integral-scalar-quotient-transition-transpose` isolates the mate-transpose equality strictly below the item theorem. Its statement is the image equality under the target adjunction hom equivalence, so the item proof combines it with genuine equivalence injectivity rather than restating the item.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefIntegralScalarQuotientTransition": "4fabc57ca5b1e99423b0b706fc7448bb67508ddb", "Sheaf.SixFunctors.CoefIntegralScalarQuotientTransitionTranspose": "ee93256dbd290555813eae7afb82453ab0419179"}, "results": {}, "time": "2026-10-28T01:01:41+0800", "transitive": 0, "version": 1}
```

## Second reading by Q9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
