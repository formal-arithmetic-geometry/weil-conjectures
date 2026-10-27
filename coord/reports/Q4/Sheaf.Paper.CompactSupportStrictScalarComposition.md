## What changed

Restored the published `compactSupportStrictScalarComparison` declaration and its
source/node attachment. Removed the rejected `_core` declaration and node: that
statement was equivalent to the item after cancelling the completion isomorphism.
The composition theorem is now assembled from the image-tower comparison and the
new support-realization coherence theorem, which takes the comparison equation as
an explicit hypothesis and carries it through support models, reduction balancing,
and retained subsequences. The preparatory associator declarations remain in the
Prelude module. The original source module compiled in 52.9 seconds in import
order; the Prelude compiled in 23.1 seconds.

## Proved and sorry left

`compactSupportStrictScalarComposition` is proved from
`compactSupportStrictScalarComparison` (at the reduced object), naturality of the
tower associator, and `supportRealization_coherence` (which, after review, has no
comparison hypothesis).
`compactSupportStrictScalarComparison` and
`compactSupportStrictScalarIdentity` are the two pre-existing sorries. The new
`supportRealization_coherence` theorem is one split-off support-realization
statement, with node
`lem-pur-compact-support-strict-scalar-composition-support-realization`.

## No longer needed

The rejected `_core` declaration, its node, and its proof dependency are removed.
The Prelude no longer imports CompactSupportCompleteRestrictionFaithful,
ConstantCompletedScalarAssociativity, ScalarLimitTensorComposition or
ScalarLimitTensorRestriction (reviewer correction); the support module imports only the Prelude; the item no longer imports Mathlib.CategoryTheory.Adjunction.CompositionIso or Sheaf.Paper.StrictProperRestrictionComposition. The Prelude is a compile-time
split of preparatory declarations that remain publicly available; its
`constantMap_composition` node is tied to that declaration.

## Where the brief, the DAG or earlier work was wrong

The item proof passes `compactSupportStrictScalarComparison` as the explicit
equation hypothesis to the support-realization declaration. Its DAG edge is kept
acyclic because the published comparison node already reaches this item through
the integral coefficient comparison route; the pointwise comparison is visible
in the Lean proof term.

The prior repair route treated postcomposition by an inverse completion
associator as a strictly weaker theorem, but cancelling that isomorphism makes
it equivalent to the item. The returned instructions correctly require the
image-tower comparison plus support realization. The published comparison hole
was present on current main and is restored here rather than deleted.

## New nodes

`lem-pur-compact-support-strict-scalar-composition-support-realization` records
the support-model transport theorem. The Prelude node
`lem-pur-compact-support-strict-scalar-composition-prelude` records the concrete
`constantMap_composition` declaration. The Prelude split and its original
compile-time justification are recorded in
`coord/changes/Sheaf.Paper.CompactSupportStrictScalarComposition.md`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportStrictScalarComposition": "0d5d8c77b8ff81db4a827fc596116cdc21dc5408", "Sheaf.Paper.CompactSupportStrictScalarCompositionPrelude": "034d212820d02d418269113c5de8eec88e90ef05", "Sheaf.Paper.CompactSupportStrictScalarCompositionSupportRealization": "ed781154b84dd47c06788a55a7b5e12a399a7c04"}, "results": {"Sheaf.Paper.CompactSupportCompletedScalarArrow": {"hash": "73c483bef93f72ac36528e891cf333b01f03f36a", "status": "OK"}}, "seconds": 11, "time": "2026-10-28T04:47:11+0800", "transitive": 0, "version": 1}
```

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

## Reviewer corrections (cc, 2026-10-28)

See the change record: the unused `hcomparison` hypothesis was removed, imports were
trimmed, and the node records (Prelude declarations; item proof steps, proof_deps and
Prelude stmt_dep; support stmt_deps) were repaired. Corrected set compile times:
Prelude 12.0 s, SupportRealization 4.7 s, item 28.5 s; importer CompactSupportCompletedScalarArrow 3.3 s.

