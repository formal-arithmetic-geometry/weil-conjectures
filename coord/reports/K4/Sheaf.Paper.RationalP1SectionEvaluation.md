## What changed

The core pre-unitor evaluation is now proved by composing two strict categorical
substeps. The first substep reduces kernel insertion, path comparison and inverse
projection to the normalized supported arrow. The second substep composes that
arrow with the native first functional. The existing terminal theorem remains
proved by its original postcomposition helper.

## Proved and sorry left

Closed the `first_section_tensor_evaluation_core` sorry. The existing
`first_section_tensor_evaluation` theorem remains proved. Added two named strict
substeps with `sorry`: `first_section_tensor_evaluation_prefix` and
`first_section_tensor_evaluation_postprefix`; each has a DAG node in this
 delivery.

## No longer needed

None. All existing imports and declared proof dependencies remain used.

## Where the brief, the DAG or earlier work was wrong

The core proof plan omitted the object-level transport between the explicit
canonical first-projection functor and `moduleObjectDerivedPushforward`. The
Lean proof therefore needs the prefix to expose that transport before the
native functional is composed. The two new statements isolate that transport
and the subsequent functional cancellation as strictly smaller obligations.

## New nodes

- `lem-sfb-rational-p1-section-evaluation-prefix`
- `lem-sfb-rational-p1-section-evaluation-postprefix`

## Related modules compiled before delivery

5 related module(s) compiled against this delivery by deliver3.py: 5 OK.

```json
{"capped": false, "direct": 5, "left_out": 0, "own": {"Sheaf.Paper.RationalP1SectionEvaluation": "e69ff200d91d2ca9c2a3e01076a66ad12f9fcf2c"}, "results": {"Sheaf.Paper.RationalP1FirstTraceTransport": {"hash": "770dd6623b95b679aa7caada85cca47687899add", "status": "OK"}, "Sheaf.Paper.RationalP1FirstTraceTransportCore": {"hash": "25a633feefafb9e4b99d6c68a26dab6e33476922", "status": "OK"}, "Sheaf.Paper.RationalP1FirstTraceTransportCounit": {"hash": "17b4be0247261f96e1c916c21d11384a8bce7055", "status": "OK"}, "Sheaf.Paper.RationalP1FirstTraceTransportCounitExpanded": {"hash": "21900cefaa0338b7f0d62f5053a4261d6a41cc2a", "status": "OK"}, "Sheaf.Paper.RationalP1UnitFactorization": {"hash": "21abb0b9c01c4e35b602a4ac2ed1c59b6fb3eb1a", "status": "OK"}}, "seconds": 73, "time": "2026-10-28T09:06:17+0800", "transitive": 0, "version": 1}
```

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
