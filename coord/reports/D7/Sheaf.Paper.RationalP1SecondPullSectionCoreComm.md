## What changed

The item theorem now rewrites the diagonal pullback of the inverse ambient comparison using
`second_pull_section_core_conjugate` and cancels the first pull-section isomorphism. A new
module `Sheaf.Paper.RationalP1SecondPullSectionCoreConjugate` states the strictly simpler
conjugated comparison used by that proof. The new theorem remains a named proof obligation
with its source and blueprint recorded in its docstring and DAG node.

## Proved and sorry left

The original `second_pull_section_core_comm` hole is closed by a real categorical cancellation
proof. One strictly simpler hole remains in
`second_pull_section_core_conjugate`; it is the compositor expansion and diagonal restriction
calculation described in the blueprint proof.

## No longer needed

No existing imports were removed. The proof does not use `PullSectionCompatibility` or any
additional declaration from `ProjectivePullSectionCompatibility`; that public import remains
because the item module's statement is part of that interface. No DAG dependencies were
pruned; the new proof dependency is the conjugated comparison node.

## Where the brief, the DAG or earlier work was wrong

The original item was too coarse for the available categorical interfaces: its comm field is
immediately a cancellation of the first section isomorphism after the conjugated comparison.
The compositor expansion itself is a strictly smaller intermediate obligation, so it is split
off as a new named theorem rather than left inside the parent proof.

## New nodes

`lem-sfb-rational-p1-second-pull-section-core-conjugate` is stated in
`lean/Sheaf/Paper/RationalP1SecondPullSectionCoreConjugate.lean` and recorded in the matching
DAG node. It is the ambient comparison restriction before composing with the first section
isomorphism.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.RationalP1SecondPullSectionCoreComm": "470033acb61cd09af25101bbbb38ab0a9a973624", "Sheaf.Paper.RationalP1SecondPullSectionCoreConjugate": "31998e23e49db2184a63e6c40d8ccea0e0740bcf"}, "results": {"Sheaf.Paper.RationalP1SecondPullSection": {"hash": "13e5e99df87c55e153ea18475d00218137c0ad91", "status": "OK"}}, "seconds": 21, "time": "2026-10-28T12:20:11+0800", "transitive": 0, "version": 1}
```

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
