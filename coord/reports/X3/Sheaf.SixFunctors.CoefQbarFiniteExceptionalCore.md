## What changed

Restored and completed the proof of `finite_exceptional_formula_core`. For each finite
coefficient stage, the proof obtains the normalized rational exceptional identification
from `RationalOperations.rationalExceptional_identifications`, transports it with
`exceptionalIdentificationOfIso`, and assembles the comparison isomorphism from the
finite Verdier comparison, pullback comparison, and common-stage duality. The proof-only
module `CoefQbarFiniteExceptionalCoreNaturality` records the component naturality needed
by the assembly.

## Proved and sorry left

Closed the item's one original sorry: `finite_exceptional_formula_core` (1 of 1).
Added one strictly smaller split-off theorem, still with `sorry`:
`finite_exceptional_comparison_naturality` in
`Sheaf.SixFunctors.CoefQbarFiniteExceptionalCoreNaturality`, node
`lem-coef-qbar-finite-exceptional-core-naturality`. No definition contains a `sorry`.

## No longer needed

No planned dependency was pruned. The proof uses the rational exceptional
identifications and common-stage Verdier data, plus the split naturality statement.

## Where the brief, the DAG or earlier work was wrong

The earlier proof packet was quarantined because its source dependency snapshot was
incomplete. The current packet restores the same valid construction against the current
published sources. The component naturality step is separately named because it is a
strictly smaller categorical pasting obligation and is not discharged by definitional
simplication alone; the main theorem remains unchanged.

## New nodes

`lem-coef-qbar-finite-exceptional-core-naturality` is realized by
`WeilConjectures.CoefQbarVerdier.finite_exceptional_comparison_naturality` in
`Sheaf.SixFunctors.CoefQbarFiniteExceptionalCoreNaturality`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefQbarFiniteExceptionalCore": "5080a3c353fcd0e376a8da8f074cbc7dae318184", "Sheaf.SixFunctors.CoefQbarFiniteExceptionalCoreNaturality": "d50f6ed7519f191ae33bb4304c8d981cf4bba11c"}, "results": {"Sheaf.SixFunctors.CoefQbarFiniteExceptionalScalar": {"hash": "66eb69004e780ee2eeec47a46633baaf4f8363f5", "status": "OK"}}, "seconds": 29, "time": "2026-10-28T09:53:02+0800", "transitive": 0, "version": 1}
```

## Second reading by X3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
