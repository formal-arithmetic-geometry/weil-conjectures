## What changed

Proved `finiteDualizingRealizationRestriction_transport` by appending the final normalized restriction component to a comparison-site transport core. Added the split-off module `FiniteDualizingRestrictionTransportCore` for the comparison and intrinsic factors before that final component.

## Proved and sorry left

The original theorem `finiteDualizingRealizationRestriction_transport` is proved. One strictly simpler intermediate theorem remains as `sorry`: `finiteDualizingRealizationRestriction_transport_core`, which isolates the comparison-site and intrinsic transport before the final normalized restriction map.

## No longer needed

No imports or declared dependencies were pruned. The proof uses finite dualizing data and the new comparison transport core.

## Where the brief, the DAG or earlier work was wrong

The original DAG proof text treated the comparison pasting and the final normalized component as one step. The delivered proof makes the required factorization explicit; no statement was weakened.

## New nodes

`new-finitedualizing-restriction-transport-core` records the split-off comparison-site transport core.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteDualizingRestrictionTransport": "24e6f8a67b06ce663e08cea7768d261a649fe612", "Sheaf.SixFunctors.FiniteDualizingRestrictionTransportCore": "cf6780a1875937b21dd6a4c85170f19c8ddd859e"}, "results": {}, "time": "2026-10-28T08:16:00+0800", "transitive": 0, "version": 1}
```

## Second reading by X8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
