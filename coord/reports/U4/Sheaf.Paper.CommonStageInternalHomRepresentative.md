## What changed

Added `Sheaf.Paper.CommonStageInternalHomCoherence`, isolating the missing normalized Hom
comparison coherence between operation-stage transition, scalar Hom comparison, and the
stage-system associators. The item theorem `value_transport` now unfolds the representative
and applies that coherence square. The representative-independence theorem is unchanged. The change record is [coord/changes/U4-common-stage-internal-hom-representative.md](coord/changes/U4-common-stage-internal-hom-representative.md).

## Proved and sorry left

`WeilConjectures.CommonStageInternalHom.value_transport` is proved from
`commonStageHomComparison_hom_square`. One sorry remains in the new intermediate declaration
`WeilConjectures.CommonStageInternalHom.commonStageHomComparison_hom_square`; it is the
coherence calculation described by its docstring and DAG node.

## No longer needed

Removed the unused imports `Sheaf.Paper.SpecifiedHomScalarTower` and
`Sheaf.Paper.SpecifiedHomScalarRationalNaturality`. The retained scalar-tower import adaptation
was unnecessary once the proof was factored through the coherence node, so it is absent from the
delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery left the only item hole unchanged and imported two scalar-comparison
modules without using them. The missing operation-stage/comparison coherence is now represented
as a strictly lower intermediate theorem, while the item proof performs the actual categorical
combination.

## New nodes

- `lem-weil-common-stage-internal-hom-coherence`: normalized Hom comparison transport square,
  with its proof deferred as the single remaining coherence sorry.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.CommonStageInternalHomCoherence": "e3dad3f6bf032b8f60c4cff351eac25b28bd23e9", "Sheaf.Paper.CommonStageInternalHomRepresentative": "f31368609b9b9d7e2ce4c71602e17e5f46a29bcb"}, "results": {}, "time": "2026-10-28T08:42:51+0800", "transitive": 0, "version": 1}
```

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
