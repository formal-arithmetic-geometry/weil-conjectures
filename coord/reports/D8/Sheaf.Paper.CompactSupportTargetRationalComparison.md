## What changed

The target theorem in `Sheaf.Paper.CompactSupportTargetRationalComparison` is now
assembled from two strictly smaller named statements. The first isolates the
stagewise rational isomorphism family; the second isolates its transition square.
The target proof supplies the concrete `rationalOperationTransition` isomorphisms
to the coherence theorem. The two new theorem modules are imported privately.

## Proved and sorry left

The target hole
`WeilConjectures.ConstructibleExceptionalCoefficients.compact_support_target_rational_comparison`
is closed by the real assembly proof. Two strictly simpler proof obligations remain:

- `compact_support_target_rational_iso_family` (node
  `lem-sf-compact-support-target-rational-iso-family`), the stagewise family;
- `compact_support_target_rational_coherence` (node
  `lem-sf-compact-support-target-rational-coherence`), the transition square for a
  supplied family and transition data.

No sorry occurs in a definition. Holes closed: 1. Holes added: 2 (a decomposition).

## No longer needed

No original public import or DAG dependency was removed. The target proof uses the
new family and coherence nodes and the existing `rationalOperationTransition`
definition; all other original statement dependencies remain in the split theorem
statements.

## Where the brief, the DAG or earlier work was wrong

The original proof plan bundled the integral construction, localization, and all
transition bookkeeping into one theorem. The delivery records the two genuine
interfaces separately so that the stagewise construction and its coherence can be
proved independently; no target statement or hypothesis was changed.

## New nodes

`lem-sf-compact-support-target-rational-iso-family` records the stagewise rational
family and is implemented by `Sheaf.Paper.CompactSupportTargetRationalIsoFamily`.
`lem-sf-compact-support-target-rational-coherence` records the transition square for
a supplied family and transition isomorphisms and is implemented by
`Sheaf.Paper.CompactSupportTargetRationalCoherence`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportTargetRationalCoherence": "a8415990ec2d0539173c03b752cbe0000d1aae94", "Sheaf.Paper.CompactSupportTargetRationalComparison": "e13b8312b2e2d7788761b30c6cf6e0dd560a149a", "Sheaf.Paper.CompactSupportTargetRationalIsoFamily": "fe06060fc64088040a29800f0929ebaa39e397e2"}, "results": {}, "time": "2026-10-28T05:27:09+0800", "transitive": 0, "version": 1}
```

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
