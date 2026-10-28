## What changed

Imported the new proof-only module
`Sheaf.Paper.CompactSupportTargetRationalCanonicalSquare`. The item theorem now
rewrites `b` and `b'` using `hb` and `hb'`, then applies the canonical square
statement. The rewrite and assembly are complete Lean proof steps.

## Proved and sorry left

Proved `WeilConjectures.ConstructibleExceptionalCoefficients.compact_support_target_rational_coherence`.
One strictly smaller statement remains as a named sorry:
`WeilConjectures.ConstructibleExceptionalCoefficients.compact_support_target_rational_canonical_square`
(node `lem-sf-compact-support-target-rational-canonical-square`). No definition
contains a sorry. Holes closed: 1. Holes added: 1 (decomposition).

## No longer needed

The item proof no longer uses `lem-sf-compact-support-target-rational-iso-family`
or its module `Sheaf.Paper.CompactSupportTargetRationalIsoFamily`; that module
remains needed by the parent comparison theorem, but is not needed for this
coherence assembly. The original self-dependency of the item node was removed
and replaced by the canonical-square node.

## Where the brief, the DAG or earlier work was wrong

The supplied transition isomorphisms are only usable after replacing them by
the canonical rational comparison composites. The earlier split treated that
canonical square as the whole supplied-transition theorem. This delivery makes
the canonical square an explicit strictly smaller proof obligation and proves
the original interface from it by the stated equalities `hb` and `hb'`.

## New nodes

`lem-sf-compact-support-target-rational-canonical-square` is implemented by
`Sheaf.Paper.CompactSupportTargetRationalCanonicalSquare`. It states the same
component square with the arbitrary transition parameters removed and the
canonical composites substituted directly.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportTargetRationalCanonicalSquare": "705fd65afb2f73ff9b585ca03c22d9250c961cac", "Sheaf.Paper.CompactSupportTargetRationalCoherence": "e8532d861661e50e0f6e4a2149a7db4102d4bf68"}, "results": {}, "time": "2026-10-28T08:10:02+0800", "transitive": 0, "version": 1}
```

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
