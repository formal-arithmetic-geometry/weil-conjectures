## What changed

Proved `AlgebraicGeometry.etaleBrownImageRealization_exists` by constructing the
ordinary, derived, and inverse comparison fields and assembling their coherence
proofs. The construction was split into three strictly smaller named existence
lemmas, each in its own module, and the parent imports those modules.

## Proved and sorry left

Closed the parent hole in `etaleBrownImageRealization_exists`.
The following three strictly smaller construction lemmas remain as named `sorry`s:

- `etaleBrownImageRealization_ordinaryRight_exists`
- `etaleBrownImageRealization_right_exists`
- `etaleBrownImageRealization_inverse_exists`

## No longer needed

None. The parent still needs `EtaleBrownProjectionRealization`; all three
construction modules are used by the proof.

## Where the brief, the DAG or earlier work was wrong

The parent DAG step described the whole construction as one proof obligation,
although its ordinary, derived-unit, and inverse-mate clauses can be stated as
three independent strictly smaller existence obligations. No mathematical
statement was changed.

## New nodes

- `lem-pur-etale-brown-image-realization-ordinary`
- `lem-pur-etale-brown-image-realization-derived`
- `lem-pur-etale-brown-image-realization-inverse`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.EtaleBrownImageRealization": "a1af2861356f635b6919b07b83842d362bba1cfc", "Sheaf.Paper.EtaleBrownImageRealizationDerived": "e05593f38b3c7c7b385bcbd14c310d10597ee8b0", "Sheaf.Paper.EtaleBrownImageRealizationInverse": "7ddba057865b4fca14b976166cbc8bbb20c3bf58", "Sheaf.Paper.EtaleBrownImageRealizationOrdinary": "63216ff9842e0c9b653ac9ede2eb14dafa035438"}, "results": {}, "time": "2026-10-28T03:58:58+0800", "transitive": 0, "version": 1}
```

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
