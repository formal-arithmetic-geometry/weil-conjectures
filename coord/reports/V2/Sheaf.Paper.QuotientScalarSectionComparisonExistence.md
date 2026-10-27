## What changed

Proved `scalar_section_comparisons_exists` by assembling two strictly smaller fixed-model comparison statements. Added ordinary generator normalization and derived counit normalization modules, each imported privately by the item module. Updated the item DAG proof to use those two nodes.

## Proved and sorry left

The item theorem `AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalar_section_comparisons_exists` is proved. Two strictly simpler split-off statements remain sorry: `scalar_section_ordinary_comparison_exists` and `scalar_section_derived_comparison_exists`, with their respective DAG nodes. No definitions contain sorry.

## No longer needed

Pruned the direct `QuotientScalarSectionModelExistence` import from the item and both split modules: `SectionModel` is defined by `QuotientSectionTensorData`, and the model-existence theorem is not used by these fixed-model statements.

## Where the brief, the DAG or earlier work was wrong

The original fixed-model proof step combines two independent constructions: ordinary generator normalization and derived counit normalization. Splitting those obligations makes the parent proof a genuine assembly from strictly smaller statements.

## New nodes

`lem-sfb-quotient-scalar-section-ordinary-comparison-existence` records the ordinary generator comparison for a fixed model.

`lem-sfb-quotient-scalar-section-derived-comparison-existence` records the derived counit comparison for a fixed model.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.QuotientScalarSectionComparisonExistence": "ff6b6bf4e2e3db18aca732b71e5b2c021fc05b6a", "Sheaf.Paper.QuotientScalarSectionDerivedComparisonExistence": "8ded2934a4e58ef4c30a4fbfdd126262d872c411", "Sheaf.Paper.QuotientScalarSectionOrdinaryComparisonExistence": "85820d83a0fb6e397ab88aa302235825c7051bd5"}, "results": {"Sheaf.Paper.QuotientScalarSectionExistence": {"hash": "90c669ad5a73a0a1de197e89f20640a47234eeb2", "status": "OK"}}, "seconds": 141, "time": "2026-10-27T23:56:42+0800", "transitive": 0, "version": 1}
```

## Second reading by V2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
