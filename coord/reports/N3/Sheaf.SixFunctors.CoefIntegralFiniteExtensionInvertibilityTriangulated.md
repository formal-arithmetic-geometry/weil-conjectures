## What changed

Added the selected-shift triangulatedness theorem
`comparison_invertibility_triangulated_isTriangulated` to the assigned module. The original
existential theorem now obtains the coherent shift from
`integralScalarExtensionWellDefined` and applies this named reduction. Added the matching
DAG node `lem-sf-integral-finite-extension-triangulated-isTriangulated` and updated the
assigned node's proof route and dependencies.

## Proved and sorry left

The existential theorem `comparison_invertibility_triangulated` is proved by extracting the
canonical `CommShift` and applying the named reduction. One sorry remains in
`comparison_invertibility_triangulated_isTriangulated`; it is the strict Roos cone,
signed-shift, and localization transport argument described by its new DAG node.

## No longer needed

No imports were removed. The original route's direct dependency list was replaced by the
new reduction node plus the scalar-extension construction used to obtain its shift; the
unneeded direct imports of the two broad supporting statements are no longer listed in the
assigned node's proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The prior node treated the entire ambient triangulatedness assertion as one unsplit step,
while the public construction already exposes the coherent shift separately. The remaining
work is specifically the strict Roos cone and localization transport for a chosen shift.

## New nodes

`lem-sf-integral-finite-extension-triangulated-isTriangulated` records the remaining
strictly lower-level selected-shift triangulatedness step and its source proof plan.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibilityTriangulated": "221c3d81835f67663a1d8953829c83d5dd714ca6"}, "results": {"Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility": {"hash": "bc6d2cee3ee60dda8a76937e86a1e840f78ccc55", "status": "OK"}}, "seconds": 13, "time": "2026-10-28T06:46:42+0800", "transitive": 0, "version": 1}
```

## Second reading by N3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
