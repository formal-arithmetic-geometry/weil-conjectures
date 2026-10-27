## What changed

Proved `WeilConjectures.IntegralSupportNormalization.openAdjunctionTransposeNormalization`
without changing its statement or public imports. The proof restricts the recorded
whole-system open adjunction along coherent reduction. Reconstruction units make
reduction fully faithful on constructible objects; effectivity gives the pullback
comparison, and the prescribed finite-reduction realization detects invertibility
of the compact-operation comparison. Finite evaluation is used only to detect an
isomorphism, never to infer equality of system morphisms.

Ordinary open pullback preserves constructibility by the existing ordinary
recollement realization, transported through uniqueness of the module pullback
adjoint. Uniqueness of right adjoints then chooses the existential comparison `p`
so that restriction of the ordinary adjunction is exactly the system restriction.
The restriction Hom formula and cancellation prove the required whole-system
equality. The helper arguments are private and proved.

## Proved and sorry left

Closed the sole original hole:
`WeilConjectures.IntegralSupportNormalization.openAdjunctionTransposeNormalization`
(node `lem-sf-open-support-adjunction-transpose`). No holes are added or left in
the delivery. This is a proof from existing stated dependencies, some of which
remain unproved elsewhere, not an assertion that the entire dependency closure
is axiom-free.

## No longer needed

The new proof does not use the proposed transport-square argument from
`lem-sf-integral-immersion-pullback-normalization` and
`lem-sf-integral-open-reduction-comparison`. These are removed from this node's
proof dependencies. The ordinary operation and support-normalization definition
nodes are retained because the proof uses their recorded functors and adjunctions. The current public data module
still imports some of these modules, so no whole module is claimed as pruned.
No original import was removed. No source-library declaration was removed.

## Where the brief, the DAG or earlier work was wrong

The recorded build failure was a bad import of
`Sheaf.Paper.IntegralSupportNormalizationData`; that source is present in the
current shared snapshot. The repaired item retains this import and its Lean
attachment. The earlier plan required a separate identification of a fixed
pullback comparison. The actual statement existentially quantifies that
comparison, so uniqueness of right adjoints supplies it with the exact needed
adjunction normalization. No additional transport-square theorem is necessary.
The construction treats identity and empty opens and zero objects by the same
adjunction identities, without any nonemptiness hypothesis.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IntegralOpenAdjunctionTransposeNormalization": "107a1c3be9d4e4dea3ff86ecf5087d58e074d5c8"}, "results": {"Sheaf.Paper.IntegralOpenSupportNormalization": {"hash": "11be195fd04eb6eb1c10cf93311a61f0c1640984", "status": "OK"}}, "seconds": 131, "time": "2026-10-28T01:05:24+0800", "transitive": 0, "version": 1}
```

## Second reading by S7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
