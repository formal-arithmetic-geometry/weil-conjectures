## What changed

The item theorem now applies two strictly smaller lemmas: `section_tensor_transport_kflat`,
which states the conjugation equation on flat-term K-flat representatives, and
`tensor_section_condition_of_kflat`, which extends that representative equation to all derived
pairs by resolving-class uniqueness. The two lemmas are in new modules
`Sheaf.Paper.QuotientSectionTensorTransportKFlat` and
`Sheaf.Paper.QuotientSectionTensorTransportExtension`; their proofs remain named split-off
statements with complete proof plans in their docstrings.

## Proved and sorry left

The item declaration `section_tensor_transport_condition` is proved from the two split-off
lemmas. Two `sorry`s remain, one in `section_tensor_transport_kflat` and one in
`tensor_section_condition_of_kflat`; each has a corresponding DAG node.

## No longer needed

No imports or declared proof dependencies were removed. The original low-level comparison
nodes listed in the blueprint are no longer direct dependencies of this item because their
argument is encapsulated by the two strictly smaller split-off statements.

## Where the brief, the DAG or earlier work was wrong

The original node treated the flat-term representative calculation and the resolving-class
extension as one indivisible theorem. They are independent proof steps, so the delivery splits
them into two named intermediate statements while preserving the item statement unchanged.

## New nodes

`lem-sfb-quotient-section-tensor-transport-kflat` records the normalized conjugation equation
on flat-term K-flat representatives, sourced from Stacks Tags 06YY, 07A4 and 07A6.

`lem-sfb-quotient-section-tensor-transport-extension` records the resolving-class extension
from those representatives to arbitrary derived pairs, sourced from Stacks Tags 06YS and 06YU.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.QuotientSectionTensorTransportCondition": "33e1e7d40352d54f1bd84641f7214bbab68aa1b3", "Sheaf.Paper.QuotientSectionTensorTransportExtension": "c463cf247d387bea9248a0af220091d6875b2dfe", "Sheaf.Paper.QuotientSectionTensorTransportKFlat": "c81431c4b82a5a614295c6062d7a82db51e64ab3"}, "results": {}, "time": "2026-10-28T00:58:34+0800", "transitive": 0, "version": 1}
```

## Second reading by K4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
