## What changed

The item theorem now performs the finite/sequence case split and delegates each case to a named component theorem. Added `AmbientCoefficientPullbackFiniteIso` and `AmbientCoefficientSequencePullbackIso`, each documenting the corresponding adjunction comparison still required.

## Proved and sorry left

The main theorem `coefficientPullback_isIso` is reduced to the two component statements. The component declarations `coefficientPullback_some_isIso` and `coefficientPullback_none_isIso` remain as split-off `sorry` theorems, with one node each.

## No longer needed

No proof-dependency imports were removed. The original broad proof plan is replaced by the two component nodes; all other declared dependencies are not imported by this delivery.

## Where the brief, the DAG or earlier work was wrong

The finite constant-sheaf comparison available in the library is stated only when the scheme and coefficient universes coincide. The ambient construction uses coefficient universe `max u (t + 1)` and transported site categories, so that theorem does not typecheck directly. The remaining proof requires explicit universe-transported adjunction comparisons and their sequence-site assembly.

## New nodes

`lem-sf-ambient-coefficient-pullback-iso-finite` records the finite-stage specialization. `lem-sf-ambient-coefficient-pullback-iso-sequence` records the product sequence-site specialization.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AmbientCoefficientPullbackFiniteIso": "de719c7329392166a2118df7ba10ec3c851b4f65", "Sheaf.Paper.AmbientCoefficientPullbackIso": "fb62c05c01ce8a9ec4aa5ddb02c4edcd10131f89", "Sheaf.Paper.AmbientCoefficientSequencePullbackIso": "a8bdb0104200ec57a04e65646825a55c2a1a7781"}, "results": {}, "time": "2026-10-28T06:34:55+0800", "transitive": 0, "version": 1}
```

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
