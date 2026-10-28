## What changed

Filled `projectionTensorComparisonCompatible_component_of_representative_formula` preserving its hypotheses and conclusion up to unfolding the explicit generic component-square predicate, retaining the existing public imports, and preserving the meaning of every existing definition. The proof transports the supplied operations to the canonical tensor and the literal coherent stage-system pullback, then proves the resulting square on the included finite-stage objects.

Added proved supporting declarations in eight modules: the generic `TensoratorFromModelNaturality` and `CommonProjectionPullbackStages`, `CommonProjectionPullbackCoherence`, `CommonProjectionPullbackStageNormalization`, `CommonProjectionPullbackTensorTransport`, `CommonProjectionTensorComparisonNormalization`, `CommonProjectionPullbackTensorModelMap`, and `CommonProjectionPullbackTensorModels`. They construct the prescribed stage morphism, identify its normalization, transport the component square, compute the image of the finite tensor model, and cancel the coefficient-unit maps using rational tensor/pullback naturality. All supporting theorems are proved. Small proved private categorical lemmas keep elaboration from repeatedly unfolding the coefficient constructions.

The existing universal bridge retains its statement and proof route; its call to the component now supplies the existing invertibility instances explicitly. The existing `CommonStageInclusionTensorNaturality` module also constructs the same inclusion tensorator directly from its component isomorphisms. This preserves its signature, attributes, and component maps while avoiding expensive kernel reduction of nested natural-isomorphism compositions. The generic naturality theorem proves its naturality field. The change record is `coord/changes/common-inclusion-tensor-comparison-components.md`; the existing naturality node records this construction. The direct importers `CommonProjectionTensorComparison` and `AdicCompletedTensorStageComponent`, and the indirect named consumer `AdicCompletedTensorStageNaturality`, compile unchanged against this repair. To meet the per-file serialization limit, the four existing operation definitions move verbatim to `CommonProjectionPullbackTensorOperations`, and the proved existing component theorem moves to `CommonProjectionPullbackTensorComponent`. The original item publicly re-exports both and retains the universal bridge and final theorem; no existing name, statement, definition body, or attribute is changed by this split. The component node attachment follows its declaration. The original node lists only the two declarations that remain in the facade; the operations node lists all five declarations in its module. The generic `projectionTensorComparisonComponent` spells out exactly the previous expanded conclusion and keeps serialization of the auxiliary theorem manageable; no target statement changes. All twelve delivery modules compile with profiling removed. The four direct importers `CommonProjectionProperFactor`, `HigherTensorIdentityComposition`, `CommonProjectionProperTensorCompatibility`, and `ProjectionIdentityTensorUnit` compile unchanged against the split. The additional indirect user `ProjectionIdentityProperCounit` also compiles unchanged (47.8 seconds). The component and facade compile in 40.1 and 30.5 seconds respectively. No module in the adopted `WeilConjectures` source tree changes.

## Proved and sorry left

Closed the item's one hole: `WeilConjectures.projectionTensorComparisonCompatible_component_of_representative_formula` (node `lem-sf-common-projection-pullback-tensor-compatibility-component`).

Added zero holes. There are zero `sorry` occurrences in the twelve delivered Lean modules. In particular, `WeilConjectures.commonProjectionInclusionPullbackTensorSquare`, which was unfinished in the retained attempt, is now proved from the finite representative, stage coherence, rational tensor naturality, and the coefficient-unit identity. This is a proof of the original obligation, not a decomposition into new holed statements. Existing imported obligations are unchanged.

## No longer needed

None. No existing import, declaration, node, module, or unit-route step is withdrawn. The original representative and supplied-operation dependencies remain needed. Development probes are retained outside `lean/` and are not delivery modules.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement correction was needed. The auxiliary component conclusion is written through its definitionally equal generic equation predicate to avoid the expensive serialization of the expanded signature. The earlier attempt stopped at the finite-model square and ran into expensive unfolding. Its report incorrectly described that square as proved. The present proof supplies the categorical cancellation: first compare the finite tensor models, then move the source coefficient units through the rational pullback/tensor comparison and identify their pullbacks with the target units. Generic proved lemmas and local reducibility controls avoid repeating the large concrete elaborations; no time or heartbeat limit is raised.

## New nodes

`def-sf-common-projection-pullback-stages` constructs the prescribed stage morphism directly from its given functors, transitions, and coherence proof.

`lem-sf-common-projection-pullback-stage-coherence` extracts only the coherence proof supplied by normalized descent.

`lem-sf-common-projection-pullback-stage-normalization` identifies the common pullback with the literal stage morphism for any coherence proof, using proof irrelevance.

`lem-sf-common-projection-tensor-component-normalization` proves the general categorical transport calculation for a component square.

`lem-sf-common-projection-tensor-comparison-normalization` removes the supplied tensorator transports by heterogeneous equality.

`lem-sf-common-projection-pullback-tensor-model-map` computes the image of the inclusion tensor model using the stage-morphism coherence law.

`lem-sf-common-projection-inclusion-pullback-tensor-square` proves the finite-stage square, including the repeated-stage coefficient units. None of these nodes leaves a proof hole.

`lem-sf-tensorator-from-model-naturality` proves naturality of the inverse corrected-model components by assembling the corresponding natural isomorphism. It supports the definition repair described above.

`def-sf-projection-pullback-tensor-operations` records the explicit generic component-square predicate and the four pre-existing operation definitions in their separate serialization module; it introduces no mathematical assumption.

## Related modules compiled before delivery

7 related module(s) compiled against this delivery by deliver3.py: 7 OK.

```json
{"capped": false, "direct": 6, "left_out": 0, "own": {"Sheaf.CategoryTheory.TensoratorFromModelNaturality": "3a266d1d93d0f7710ebeeaba9a86017f985f3325", "Sheaf.Paper.CommonProjectionPullbackCoherence": "52bb3b2ce6c23c0fe3c9f476388df0bb3fb5f8a1", "Sheaf.Paper.CommonProjectionPullbackStageNormalization": "91b54629d5c9e5efd8289455a508b7ed0739182a", "Sheaf.Paper.CommonProjectionPullbackStages": "547e4d4d11a9bb4e7a62021974a99ca1d02c5700", "Sheaf.Paper.CommonProjectionPullbackTensorCompatibility": "82e3ac8caf57b788cb042b15fb1b9f3b99591d34", "Sheaf.Paper.CommonProjectionPullbackTensorComponent": "c647ea85134e2ed475ee74d8b4c7934da68ce595", "Sheaf.Paper.CommonProjectionPullbackTensorModelMap": "974c239565333ecaaf2ef9b6264b9870f9544e04", "Sheaf.Paper.CommonProjectionPullbackTensorModels": "aac07a752e8f0912cc727d7accbbf418b28e75ea", "Sheaf.Paper.CommonProjectionPullbackTensorOperations": "1284c3c4b106b33752b06c0a2e6d935791429f33", "Sheaf.Paper.CommonProjectionPullbackTensorTransport": "86634cd69d95dabaed78f8d5f55c402a55fa1e1c", "Sheaf.Paper.CommonProjectionTensorComparisonNormalization": "0d1d9d949a4e8cb8f4fa538ee43b53b963f03729", "Sheaf.Paper.CommonStageInclusionTensorNaturality": "23b64da5a61756e677806706647a1eb2222dd69d"}, "results": {"Sheaf.Paper.AdicCompletedTensorStageComponent": {"hash": "a0a6a7776ce22a6fc0be13ba40a27eb35b9427ba", "status": "OK"}, "Sheaf.Paper.AdicCompletedTensorStageNaturality": {"hash": "66b2976c461d52226b517511bbb0c9efbf126ad6", "status": "OK"}, "Sheaf.Paper.CommonProjectionProperFactor": {"hash": "eba01af110fb75b567393cb1e300f0a0019c6839", "status": "OK"}, "Sheaf.Paper.CommonProjectionProperTensorCompatibility": {"hash": "a4cce18c3ad4668db3247df3786e965ded3ba52c", "status": "OK"}, "Sheaf.Paper.CommonProjectionTensorComparison": {"hash": "ec6b038de8cdbd64e7ae19e9bb8dcda65aa4ed43", "status": "OK"}, "Sheaf.Paper.HigherTensorIdentityComposition": {"hash": "80eb8845d12127857a560ddb4b747c41d4e660b9", "status": "OK"}, "Sheaf.Paper.ProjectionIdentityTensorUnit": {"hash": "f37accc1e6db179957c87198eef73eeb8b60cd01", "status": "OK"}}, "seconds": 372, "time": "2026-10-28T14:33:46+0800", "transitive": 1, "version": 1}
```

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
