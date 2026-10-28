## What changed

Proved `WeilConjectures.CoefQbarVerdier.finite_exceptional_comparison_naturality`
without changing its statement or any shared definition. The proof identifies the
canonical pullback comparison with equality transport from normalized coherent stage descent,
then applies a proved private categorical pasting lemma to the exceptional and
finite/common duality comparisons. All helpers are proved in the item module.

Added the proof-only import `Sheaf.Paper.CommonStagePullbackNormalizedDescent` and
updated the item's DAG proof and dependencies. This existing proved theorem is used
as a general descent tool; it does not replace any step of the unit's Verdier route.

Validation: the final item compiled through `lcompile.py` without warnings in 19.7 seconds.
The original theorem statement text is unchanged.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.CoefQbarVerdier.finite_exceptional_comparison_naturality`
(node `lem-coef-qbar-finite-exceptional-core-naturality`).
No holes remain in the module; no holes were added or split off.

## No longer needed

Removed the proof-only import `Sheaf.SixFunctors.RationalExceptionalIdentifications`.
The dependency `lem-sf-rational-exceptional-identifications` is unnecessary for this
naturality argument: the exceptional natural isomorphism is already an input.
Its construction and scalar compatibility are not needed here. Other consumers
still use that module, so no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original plan called the pullback object comparison natural without naming its
arrow-level justification. The existing normalized descent theorem supplies that
justification, so no further split or statement repair is necessary.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarFiniteExceptionalCoreNaturality": "a8ab0d6bbb4eabe90fd82e597b14ff0234ef1320"}, "results": {"Sheaf.SixFunctors.CoefQbarFiniteExceptionalCore": {"hash": "5080a3c353fcd0e376a8da8f074cbc7dae318184", "status": "OK"}}, "seconds": 50, "time": "2026-10-28T12:32:43+0800", "transitive": 0, "version": 1}
```

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
