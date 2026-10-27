## What changed

The parent module now proves `pullbackTensorCompositionCoherence` by assembling three
strictly smaller coefficient-level component theorems. I added
`PullbackTensorIntegralCompositionCoherence`,
`PullbackTensorRationalCompositionCoherence`, and
`PullbackTensorCommonStageCompositionCoherence`. Their statements isolate the
integral, rational, and algebraically closed common-stage conclusions respectively;
their docstrings record the quotient-tower, localization, and finite-stage
representative proof routes. The parent DAG node now records these three component
nodes as its proof dependencies.

## Proved and sorry left

The original conjunction theorem
`WeilConjectures.pullbackTensorCompositionCoherence` is proved from the three
component declarations. This is a decomposition: the three component theorem
proofs remain `sorry`, each with its own node:

- `WeilConjectures.pullbackTensorIntegralCompositionCoherence`, node
  `lem-pur-pullback-tensor-integral-composition-coherence`;
- `WeilConjectures.pullbackTensorRationalCompositionCoherence`, node
  `lem-pur-pullback-tensor-rational-composition-coherence`;
- `WeilConjectures.pullbackTensorCommonStageCompositionCoherence`, node
  `lem-pur-pullback-tensor-common-stage-composition-coherence`.

No definition contains `sorry`.

## No longer needed

No imports were removed. The original parent proof dependencies are represented by
the three component nodes, and the component modules retain the declarations needed
for their documented proof routes.

## Where the brief, the DAG or earlier work was wrong

The direct definitions of the three canonical composition predicates do not reduce
by simplification: their chosen completed, localized, and common-stage comparison
maps are irreducible constructions. A proof therefore requires the three distinct
normalization arguments described in the module documentation. The parent node's
single proof step was too coarse for a compiling delivery, so it was replaced by a
strict coefficient-level decomposition.

## New nodes

`lem-pur-pullback-tensor-integral-composition-coherence` isolates the integral
quotient-tower equation and its coherent-reduction/full-faithfulness argument.
`lem-pur-pullback-tensor-rational-composition-coherence` isolates localization and
bilinear coefficient descent. `lem-pur-pullback-tensor-common-stage-composition-coherence`
is the finite common-stage representative descent. Each node has a corresponding
module and declaration in this delivery.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.PullbackTensorCommonStageCompositionCoherence": "dd75407ee2c5c7af0d6ca68ce9e323a4d92ec09b", "Sheaf.Paper.PullbackTensorCompositionCoherence": "d76c6e6b4b555f3c5799a14f929dbdd77b749070", "Sheaf.Paper.PullbackTensorIntegralCompositionCoherence": "23a380a04a332fe7e44037284ac3ad26ae087015", "Sheaf.Paper.PullbackTensorRationalCompositionCoherence": "b6afeb0fcc58b3a07a1b8443a979647183b2e295"}, "results": {}, "time": "2026-10-28T02:27:49+0800", "transitive": 0, "version": 1}
```

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
