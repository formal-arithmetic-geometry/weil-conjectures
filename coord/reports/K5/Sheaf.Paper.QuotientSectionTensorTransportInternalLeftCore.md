## What changed

The original core theorem now delegates its categorical paste to the new intermediate
module `Sheaf.Paper.QuotientSectionTensorTransportInternalLeftCorePaste`.

## Proved and sorry left

The original declaration is closed (1 of 1 original holes). The intermediate declaration
`section_tensor_transport_internal_left_paste` remains a named proof step with one `sorry`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The direct categorical reassociation is not reducible through the opaque derived-category
abbreviations in the current interface; it is recorded as a separate paste step.

## New nodes

`lem-sfb-quotient-section-tensor-transport-internal-left-paste` records the intermediate
categorical paste step.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.QuotientSectionTensorTransportInternalLeftCore": "92e2301587db99c303a55c5644075081ddf1c8d2", "Sheaf.Paper.QuotientSectionTensorTransportInternalLeftCorePaste": "07de165da579fd53a11def9d51bae3cf3df38854"}, "results": {"Sheaf.Paper.QuotientSectionTensorTransportInternalLeft": {"hash": "b7f0bf88f63eeb6cafc10d354aa2bcb2aed5433f", "status": "OK"}}, "seconds": 129, "time": "2026-10-28T08:08:32+0800", "transitive": 0, "version": 1}
```

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
