## What changed

The target theorem now applies a two-stage proof decomposition.  The representative
stage is recorded in `ScalarHomZeroCompatibilityOnQ`, and the resolution/naturality
transport is recorded in `ScalarHomZeroCompatibilityResolutionDescent`.  The target
module supplies the representative theorem to the descent theorem and contains no
`sorry`.

## Proved and sorry left

`SheafOfModules.ScalarHomZero.scalarHomZeroCompatibility` is proved by the real
application of the two stage statements.  The following strictly simpler stages
remain as named obligations:

- `scalarHomZeroCompatibility_onQ` (chosen complex representatives);
- `scalarHomZeroCompatibility_resolution_descent` (transport from representatives).

## No longer needed

No declared proof dependency from the original route was removed; all four original
imports remain required by the representative statement and its context.

## Where the brief, the DAG or earlier work was wrong

The original node presented a full arbitrary-derived-object calculation as one Lean
obligation, while its proof plan already separates representative normalization from
resolution descent.  The local DAG copy records these as two genuine intermediate
nodes.

## New nodes

- `lem-coef-scalar-hom-zero-compatibility-on-q`
- `lem-coef-scalar-hom-zero-compatibility-resolution-descent`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.CategoryTheory.ScalarHomZeroCompatibility": "73796e9bad4fda5a27f7a84257caadc36a3d7e44", "Sheaf.CategoryTheory.ScalarHomZeroCompatibilityOnQ": "66eba25ddf1046f0e1ae7584bf459b1c9d32e666", "Sheaf.CategoryTheory.ScalarHomZeroCompatibilityResolutionDescent": "223849ca4896b3ad68603961fd4714d7ee9277cc"}, "results": {}, "time": "2026-10-28T06:48:51+0800", "transitive": 0, "version": 1}
```

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
