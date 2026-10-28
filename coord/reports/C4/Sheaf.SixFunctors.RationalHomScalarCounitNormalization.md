## What changed

Added the intermediate theorem `normalizedCounit_localized_integral`, isolating the
objectwise rational localization normalization. The main theorem now reduces arbitrary
rational objects to their unchanged integral representatives and combines this theorem
with `HomIdentification.integral_evaluation`.

## Proved and sorry left

`homIdentification_counit_normalized` is proved. One strictly smaller normalization
statement remains as `sorry`: `normalizedCounit_localized_integral`.

## No longer needed

No imports or declared proof dependencies were removed. The proof uses the existing
`HomIdentification.integral_evaluation` field and the new localized-integral
normalization statement.

## Where the brief, the DAG or earlier work was wrong

The original node treated the rational extension of the integral evaluation as if it
were already available from the imported declarations. The current library exposes the
rational closed transpose normalization only through its defining existence theorem;
the objectwise localization step therefore had to be recorded as a separate, strictly
smaller theorem.

## New nodes

`lem-sf-rational-hom-counit-normalized-localized-integral` records the objectwise
localized-integral normalization used by the completed theorem.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.RationalHomScalarCounitNormalization": "19371c2a95c4c1f969551e69074c5bfa2d79ed21"}, "results": {"Sheaf.SixFunctors.RationalHomScalarEvaluationCore": {"hash": "85cd7fc86cc0d6b1a77d8a945304e39e1a3616d4", "status": "OK"}}, "seconds": 17, "time": "2026-10-28T10:05:43+0800", "transitive": 0, "version": 1}
```

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
