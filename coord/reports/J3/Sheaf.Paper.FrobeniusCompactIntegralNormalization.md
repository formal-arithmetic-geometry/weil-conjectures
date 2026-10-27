## What changed

Added the proof-only module `Sheaf.Paper.FrobeniusCompactIntegralAmbientNormalization`, which isolates the ambient underlying-morphism comparison. The item module imports it privately and converts the underlying heterogeneous equality to the constructible-wrapper equality with `ObjectProperty.hom_ext`.

## Proved and sorry left

The original `frobeniusCompactIntegral_normalization` is proved. The new ambient comparison theorem `frobeniusCompactIntegral_ambient_normalization` remains one named `sorry`, recorded by node `lem-pur-frobenius-compact-integral-ambient-normalization`.

## No longer needed

No imports or declared proof dependencies were pruned; all original imports remain needed by the target statement or the ambient comparison.

## Where the brief, the DAG or earlier work was wrong

The original DAG placed the full proper/open mate calculation directly in the component theorem. The ambient underlying-morphism comparison is a separate strictly lower interface, while the item theorem only performs the constructible hom-extensionality conversion.

## New nodes

`lem-pur-frobenius-compact-integral-ambient-normalization` records the ambient comparison theorem and its proper/open mate proof plan.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FrobeniusCompactIntegralAmbientNormalization": "d425309e7588c6ef21330465061e380d33a728ba", "Sheaf.Paper.FrobeniusCompactIntegralNormalization": "6f663ab6188909db4621106220b3137423c7efc8"}, "results": {}, "time": "2026-10-28T07:30:34+0800", "transitive": 0, "version": 1}
```

## Second reading by J3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
