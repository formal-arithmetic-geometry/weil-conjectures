## What changed

Added the canonical shift-core interface module and used it in
`etaleHomComparison_reversedExact_shiftData`. The assigned theorem now proves
the omitted left component equation with
`Functor.commShiftIso_comp_hom_app`, while packaging the core's normalized data,
right component equation, and triangulated structures.

## Proved and sorry left

- Proved `etaleHomComparison_reversedExact_shiftData` (1 assigned sorry closed).
- Added the strictly smaller public theorem
  `etaleHomComparison_reversedExact_shiftCore` with one sorry; its proof obligation
  is the model construction of the normalized Hom shifts, scalar composition, and
  cone exactness, with the left component identity isolated in the parent.

## No longer needed

- The original direct proof dependency `lem-coef-etale-tensor-model-comparison`
  is no longer imported by the assigned module itself; it is retained only by the
  shift-core interface theorem.
- No Mathlib or existing library declarations were pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof route placed the full K-injective/K-flat model construction in
one declaration. The available library has the canonical `CommShift` composition
identity, so the left component equation is a short parent-level proof. The
remaining model and cone argument is isolated as a strictly smaller core
statement.

## New nodes

- `lem-coef-etale-hom-transpose-exact-shift-core`, realized by
  `Sheaf.SixFunctors.EtaleHomTransposeExactShiftCore`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.EtaleHomTransposeExactShiftCore": "9455ae374e3314c5984099c122460626adb1abc6", "Sheaf.SixFunctors.EtaleHomTransposeExactShiftData": "431ecbcf5acdc6c8027848ba871a78621ea1d558"}, "results": {}, "time": "2026-10-28T08:36:57+0800", "transitive": 0, "version": 1}
```

## Second reading by D9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
