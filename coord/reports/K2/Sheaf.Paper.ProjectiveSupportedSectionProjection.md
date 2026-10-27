## What changed

Added two strictly smaller proof obligations for the canonical regular-source
section/projection coherence and the normalized supported source arrow. The assigned
`supported_section_projection` theorem now rewrites by the source-normalization identity
and applies the canonical section/projection identity.

## Proved and sorry left

Proved `AlgebraicGeometry.ProEtale.RationalP1.supported_section_projection`.
Two strictly smaller statements remain `sorry`: `canonical_section_projection` in
`ProjectiveCanonicalSectionProjection.lean` and `supported_source_normalization` in
`ProjectiveSupportedSourceNormalization.lean`.

## No longer needed

No imports were removed. The proof does not use the ringed projection theorem,
ModuleRingedComparison, trace, delta, integration, or twist declarations directly; the
remaining work is isolated in the two lower statements.

## Where the brief, the DAG or earlier work was wrong

The build error recorded a stale bad import during the red global build. The current
`RationalP1SecondPullComparison` dependency compiles. The original DAG proof plan omitted
an explicit source-arrow normalization step, so that step is represented by the new lower
node `lem-sfb-projective-supported-source-normalization`; the canonical coherence is the
new lower node `lem-sfb-projective-canonical-section-projection`.

## New nodes

- `lem-sfb-projective-canonical-section-projection`
- `lem-sfb-projective-supported-source-normalization`

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ProjectiveCanonicalSectionProjection": "36e982bc4f4dd69d71bb940517fcc83bc9b5ee9b", "Sheaf.Paper.ProjectiveSupportedSectionProjection": "1f4e9827eddc9de852380fd0121d596fc2cea5e4", "Sheaf.Paper.ProjectiveSupportedSourceNormalization": "35a87dd5a91089498d1312a3043626f0057c8ff3"}, "results": {}, "time": "2026-10-28T02:56:20+0800", "transitive": 0, "version": 1}
```

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
