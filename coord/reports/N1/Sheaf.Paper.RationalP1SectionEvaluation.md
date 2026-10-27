## What changed

Added the named strict pre-unitor reduction `first_section_tensor_evaluation_core` to the assigned module and updated the item DAG proof to cite it. The original terminal theorem remains unchanged.

## Proved and sorry left

`first_section_tensor_evaluation_core` remains `sorry`; it is the strict pre-unitor part of the assigned proof. The original `first_section_tensor_evaluation` theorem remains `sorry` pending the final categorical unitor normalization.

## No longer needed

None. The original imports are retained because the definitions and the core reduction use them.

## Where the brief, the DAG or earlier work was wrong

The final unitor normalization repeatedly exceeded the compiler's 120-second cutoff when expressed by reassociated rewrites. The strict pre-unitor reduction compiles and isolates the remaining work without changing the target statement.

## New nodes

`lem-sfb-rational-p1-section-evaluation-core` records the strict pre-unitor section/projection paste and is attached to `first_section_tensor_evaluation_core`.

## Related modules compiled before delivery

3 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 2 OK.

```json
{"capped": false, "direct": 3, "left_out": 0, "own": {"Sheaf.Paper.RationalP1SectionEvaluation": "42e3286916da82d23d0ace988be21dbf948c8b3c"}, "results": {"Sheaf.Paper.RationalP1FirstTraceTransport": {"hash": "770dd6623b95b679aa7caada85cca47687899add", "status": "INFRA"}, "Sheaf.Paper.RationalP1FirstTraceTransportCore": {"hash": "3de2d7b6e14eef21c9de683ac5b8efc17a803857", "status": "OK"}, "Sheaf.Paper.RationalP1UnitFactorization": {"hash": "ebd85bb5534aacc7b92d7da4fe366407464707bd", "status": "OK"}}, "seconds": 95, "time": "2026-10-28T03:54:22+0800", "transitive": 0, "version": 1}
```

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
