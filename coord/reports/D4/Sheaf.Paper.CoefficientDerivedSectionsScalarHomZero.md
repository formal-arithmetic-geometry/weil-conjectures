## What changed

The assigned module remains the published H-zero scalar normalization statement with
its original proof hole.  I added one strictly smaller statement module,
`CoefficientDerivedSectionsScalarHomZeroRepresentative`, isolating the representative
transpose step for a chosen K-flat complex and quotient-image inputs.  Its proof is
left for the next worker; the new module compiles with the documented `sorry`.

## Proved and sorry left

No original hole was closed.  The existing theorem
`coefficientDerivedSectionsScalarHomZero` remains a `sorry`.  One lower named
obligation was added:

- `coefficientDerivedSectionsScalarHomZero_representative`, in the new representative
  module, remains a `sorry` for the K-flat/K-injective representative transpose.

No definition contains `sorry`.

## No longer needed

None.  The assigned module still needs its evaluation-data import.  No declared
proof dependency was removed.

## Where the brief, the DAG or earlier work was wrong

The downstream construction theorem `coefficientDerivedSystemResolutionModels` already
packages the desired representative calculation, but it imports the parent
normalization module and therefore cannot be imported here without closing an import
cycle.  The representative calculation must be proved below this item and transported
upward separately.

## New nodes

`lem-coef-derived-sections-normalization-scalar-hom-zero-representative` records the
chosen K-flat representative transpose as a strict substatement of the assigned
arbitrary-derived-input theorem.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CoefficientDerivedSectionsScalarHomZero": "53d6c881999373d0fe1e7f9e76050ba9587ddbfc", "Sheaf.Paper.CoefficientDerivedSectionsScalarHomZeroRepresentative": "901ea4e5942b41251b2af111bb3aecbd2131854e"}, "results": {}, "time": "2026-10-28T09:48:21+0800", "transitive": 0, "version": 1}
```

## Second reading by D4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
