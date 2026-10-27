## What changed

The item module now composes two explicitly stated comparison interfaces. The first
identifies chart homology of the actual finite quotient layer with chart homology of
the transported derived constant tensor model. The second identifies that derived
model homology with the ordinary constant realization of
`finiteQuotientLayerTensorComplex`. The item imports both new modules and composes
their isomorphisms degree by degree.

## Proved and sorry left

The original `finiteQuotient_layer_tensor_homology_comparison` declaration is
proved by composition. Two strictly intermediate statements remain as named
`sorry`s:

- `finiteQuotient_layer_tensor_derived_homology_comparison` in node
  `lem-weil-pbc-finite-quotient-layer-tensor-derived-homology-comparison`;
- `finiteQuotient_layer_tensor_model_homology_identification` in node
  `lem-weil-pbc-finite-quotient-layer-tensor-model-homology-identification`.

This is a decomposition of one hole into the two derived-tensor and ordinary
homology interfaces described by the node's proof steps.

## No longer needed

None. Both proof-dependency interfaces are used by the composed proof.

## Where the brief, the DAG or earlier work was wrong

The original DAG treated the derived-tensor descent, exact chart restriction,
and ordinary homology identification as one unexposed proof step. The current
library has no theorem combining those interfaces, so the proof had to expose the
two intermediate comparison statements above.

## New nodes

`lem-weil-pbc-finite-quotient-layer-tensor-derived-homology-comparison` records
the derived chart homology interface.

`lem-weil-pbc-finite-quotient-layer-tensor-model-homology-identification` records
the ordinary homology identification for the transported constant tensor model.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.FiniteQuotientLayerTensorDerivedHomologyComparison": "d8c50f54a10b4e1fc2a5126df81dcddac155f6c9", "Sheaf.Paper.FiniteQuotientLayerTensorHomologyComparison": "b21fe3d461e5020a8a54a36c398d26abf7649bb9", "Sheaf.Paper.FiniteQuotientLayerTensorModelHomologyIdentification": "616cb14f1b4f0d6876c2425c03a7c666612919a2"}, "results": {}, "time": "2026-10-28T06:32:59+0800", "transitive": 0, "version": 1}
```

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
