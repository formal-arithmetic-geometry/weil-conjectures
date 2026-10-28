## What changed

Completed the planned reduction of the supported-source derived comparison. The
item proves `supported_source_arrow_derived_core` from the diagram-unit and
residual-target declarations, then proves `supported_source_arrow_derived` by
associativity, functoriality, and cancellation. The proof imports only the
single-complex comparison modules used by this route. The residual steps that
are not yet proved are recorded as named public statements with DAG nodes.

## Proved and sorry left

Closed the original target hole `supported_source_arrow_derived`; its core
identity was already proved in the item. The following strictly smaller
statements remain as `sorry`:

- `projective_supported_normalization`
- `projective_pull_section_single`
- `projective_section_single`
- `projective_diagram_single`
- `projective_residual_target`

The helper declarations `derivedAdj`, `ordinarySection`, and `derivedSection`
are concrete definitions and contain no `sorry`.

## No longer needed

No declared proof dependency was pruned. The imported single-complex and
residual modules are all used by the item proof.

## Where the brief, the DAG or earlier work was wrong

The earlier attempt left the item as an unresolved residual compatibility. The
DAG's residual argument decomposes into ordinary support normalization,
single-complex section coherence, diagram-unit identification, and the
residual target equation. Those are now explicit declarations and the item
combines the two latter declarations by a real categorical calculation.

## New nodes

Added nodes for `lem-sfb-projective-supported-normalization`,
`lem-sfb-projective-pull-section-single`, `lem-sfb-projective-section-single`,
`lem-sfb-projective-diagram-single`, `lem-sfb-projective-residual-target`,
`def-sfb-projective-derived-adj`, `def-sfb-projective-ordinary-section`, and
`def-sfb-projective-derived-section`.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.ProjectiveDiagramSingle": "6ad5606a6f1cade2c01b0967220d970ad290c420", "Sheaf.Paper.ProjectivePullSectionSingle": "50c192a1e0da065507379d83ca945a123f2ca40d", "Sheaf.Paper.ProjectiveResidualTarget": "7f00058a513e6f1f2bc465915af19ca9a5bd3515", "Sheaf.Paper.ProjectiveSectionSingle": "5f2ce3a0f4c924dba0a97680dcc2078028dd7f67", "Sheaf.Paper.ProjectiveSupportedNormalization": "6a47c0544d258a47d5d9fe06dd3b668399834a84", "Sheaf.Paper.ProjectiveSupportedSourceArrowDerived": "923ec046be0a2473f96768b772bd2b6f640bee7d"}, "results": {}, "time": "2026-10-28T13:54:07+0800", "transitive": 0, "version": 1}
```

## Second reading by C1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
