## What changed

Marked `WeilConjectures.ConstructibleExceptionalCoefficients.compact_support_target_rational_canonical_square` `STATEMENT-DISPUTED` and preserved its original proof hole. Added and proved the private diagnostic `iso_postcompose_nontrivial`, which shows that postcomposing any supplied component isomorphism with a nontrivial target automorphism produces a distinct isomorphism with the same endpoints. The diagnostic isolates the missing normalization/naturality assumption in the displayed transition square. No public imports, definitions, or theorem signatures were changed.

## Proved and sorry left

Proved private `iso_postcompose_nontrivial`. The original theorem
`WeilConjectures.ConstructibleExceptionalCoefficients.compact_support_target_rational_canonical_square`
remains `:= by sorry` (node `lem-sf-compact-support-target-rational-canonical-square`).
No definitions contain `sorry`. Holes closed: 0. Holes added: 0.

## No longer needed

None. The existing imports and DAG dependencies remain needed by the disputed statement and its consumers.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the theorem quantifies over an arbitrary family `a` of natural
isomorphisms, while the conclusion requires that family to be compatible with the
stage transitions and the two rational comparison composites. The hypotheses impose
no such condition. For any component `a i`, `iso_postcompose_nontrivial` permits
replacement by `a i ≪≫ u` for any nontrivial automorphism `u` of its target. This
preserves the stated source and target but changes the component occurring in the
square, so the universal assertion cannot follow from the current hypotheses.
The valid repair must construct the canonical family together with its transition
naturality, or add an independent compatibility hypothesis; changing only the proof
cannot establish the current statement.

The item was compiled successfully with `lcompile.py` (16.9 seconds). No related
module was changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportTargetRationalCanonicalSquare": "f9f3adf820faf4ade67bd9296ffe87dc104f148e"}, "results": {"Sheaf.Paper.CompactSupportTargetRationalCoherence": {"hash": "e8532d861661e50e0f6e4a2149a7db4102d4bf68", "status": "OK"}}, "seconds": 36, "time": "2026-10-28T12:17:32+0800", "transitive": 0, "version": 1}
```

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
