## What changed

Proved the assigned theorem from two strictly simpler section-comparison interfaces. The
item now obtains a normalized natural transformation, upgrades its components to
isomorphisms, and assembles the natural isomorphism. Added the two split-off theorem
modules and their DAG nodes. The proof-only imports are the two new modules.

## Proved and sorry left

The assigned declaration `scalar_section_ordinary_comparison_exists` is proved. The two
new interface declarations remain sorry-backed and are recorded by their nodes:
`scalar_section_ordinary_normalized_map` and `scalar_section_ordinary_normalized_isIso`.
No sorry occurs in a definition.

## No longer needed

None beyond the two declared split interfaces; the existing `QuotientSectionTensorData`
import remains required for the statement.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated the sectionwise change-of-rings comparison as directly
available from the model fields. Those fields provide only object and map equations, so
the canonical normalized map and its invertibility are separate strict steps.

## New nodes

`lem-sfb-quotient-scalar-section-ordinary-normalized-map` records existence of the
normalized natural transformation. `lem-sfb-quotient-scalar-section-ordinary-normalized-iso`
records componentwise invertibility of such a transformation. The change record is `coord/changes/quotient-scalar-ordinary-proof-imports.md`. Both are under
`sec-six-functors-basics` and have corresponding Lean modules in `lean/Sheaf/Paper/`.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.QuotientScalarSectionOrdinaryComparisonExistence": "279f5d3d393c03ba4cd4d8ca99038fc3ea99228c", "Sheaf.Paper.QuotientScalarSectionOrdinaryNormalizedIso": "6b4213faf3fd42e382187d5fa37d37207bc14762", "Sheaf.Paper.QuotientScalarSectionOrdinaryNormalizedMap": "76e746d34d60a5d481c4aa84d52f250667c2d821"}, "results": {"Sheaf.Paper.QuotientScalarSectionComparisonExistence": {"hash": "ff6b6bf4e2e3db18aca732b71e5b2c021fc05b6a", "status": "OK"}}, "seconds": 81, "time": "2026-10-28T03:56:17+0800", "transitive": 0, "version": 1}
```

## Second reading by W3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
