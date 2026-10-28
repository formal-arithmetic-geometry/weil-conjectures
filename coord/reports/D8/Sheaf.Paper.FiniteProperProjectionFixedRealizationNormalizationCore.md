## What changed

Proved the proper component's fixed-realization coordinate projection equation. The proof
first normalizes the identity-open projection using adjunction triangles, the canonical
identity pullback comparison and identity tensor coherence derived from the existing pullback tensor-composition theorem. It then removes
the identity open factor from the proper compactification and pastes the coefficient
comparison with `finiteProperNormalization`. Realization-unit naturality, the existing
`fixed_component_realization` calculation and tensor-coordinate naturality finish the
cancellation.

All added helpers are private and proved. A private endpoint wrapper exposes the direct
projection map's domain and codomain before coefficient specialization, avoiding costly
kernel comparisons through derived tensor and localization constructions. The public theorem's statement is unchanged;
no shared definition or adopted source-library declaration was changed. The item's node
now records the actual three-part proof and the existing helper modules it uses.

## Proved and sorry left

Closed the single original hole:
`WeilConjectures.CompactSupportFiniteProjection.properComponent_fixed_realization_coordinate_projection`.

Holes added: none. Holes remaining: none. This is a proof, not a decomposition into new
obligations. The complete proof compiled in 52.3 s against the published build. The delivery tool
performs the final compile and axiom probe. An unnecessary heartbeat override on the
finite specialization helper was removed after this check.

## No longer needed

Removed the redundant direct proof import `Sheaf.Paper.ConstructibleProjectionMates`;
its definitions remain available through the public import of
`Sheaf.Paper.FiniteProjectionFixedCoordinates` and remain necessary.

The direct proof import of `Sheaf.SixFunctors.AmbientProperOpenPasting` is unnecessary:
the proof uses `Sheaf.SixFunctors.ProEtaleDerivedPullbackTensorComposition` directly and
the generic curried tensor-unit lemma in `RefinementProjectionLocalTensor`. The ambient
pasting module remains a transitive dependency of that existing lemma.

No mathematical node or module is pruned. All original statement dependencies remain
necessary. No additional unproved normalization theorem is needed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The original one-step plan suppressed the identity-open
projection calculation needed to identify the compactification projection with the direct
projection. Existing proved coefficient-identity and tensor-composition calculations suffice
for that calculation; the obligation need not be split off again. The proof establishes
the identity-open calculation for an abstract coefficient category before specializing,
which avoids costly unfolding of concrete derived module-category constructions. A proved
transport lemma reindexes the complete expanded diagram, including its implicit intermediate
scheme; reindexing its factors separately leaves expensive comparisons of derived data in
the kernel. A private direct-projection wrapper exposes its tensor-coordinate type before
coefficient specialization, avoiding kernel unfolding of the derived constructions. No shared definition, transparency policy or compile-time limit
is changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.FiniteProperProjectionFixedRealizationNormalizationCore": "b1d81622aaa7cced4ec95cf5e2b4e486a4d1aa87"}, "results": {"Sheaf.Paper.FiniteProperProjectionFixedRealizationNormalization": {"hash": "dd25e0772ac0122e55cc904440d0515146db3120", "status": "OK"}}, "seconds": 165, "time": "2026-10-28T14:37:18+0800", "transitive": 0, "version": 1}
```

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
