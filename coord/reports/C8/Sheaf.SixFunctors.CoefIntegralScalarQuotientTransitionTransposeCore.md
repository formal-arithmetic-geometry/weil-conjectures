## What changed

Restored the assigned module with its two required import source modules and isolated the
residual finite reduction and tensor square calculation as the named theorem
`residual_mate_transport`. The core transpose theorem is proved by adjunction naturality
and this residual theorem.

## Proved and sorry left

`quotient_reduction_transition_transpose_core` is proved. The strictly lower theorem
`residual_mate_transport` remains one `sorry`, recorded by node
`lem-sf-integral-scalar-quotient-residual-mate-transport`.

## No longer needed

None.

## Where the brief, the DAG or earlier work was wrong

The previous delivery had the correct reduction but its required import source modules
were absent from the delivery base after quarantine. They are included unchanged here.

## New nodes

None; the residual theorem node was already created by the earlier delivery and is
included in this packet.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.SixFunctors.CoefIntegralScalarQuotientTransitionTransposeCore": "b166d2ccd963e3c03de0db3e946e45bdbc69aba0"}, "results": {"Sheaf.SixFunctors.CoefIntegralScalarQuotientTransitionTranspose": {"hash": "048db70dc88ca6f7757a358c64f98dfce3eff3a0", "status": "OK"}}, "seconds": 27, "time": "2026-10-28T09:53:31+0800", "transitive": 0, "version": 1}
```

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
