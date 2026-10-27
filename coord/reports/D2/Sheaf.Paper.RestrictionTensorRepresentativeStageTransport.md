## What changed

Proved `WeilConjectures.restrictionTensorRepresentativeStageTransport` from the existing
normalized stage comparisons. The proof identifies each conjugate with the transition
image of one actual morphism at the compositum, then applies `StageSystem.tr_map`.
All existing theorem signatures and the item's public import remain unchanged.

Four new helper modules contain complete proofs: `MixedTensorStageComponent`,
`CommonStagePullbackEndpoint`, `CommonStageTensorEndpoint` and
`RestrictionTensorNormalizedSquare`, all under `Sheaf.Paper`. They calculate the mixed
square with coherent endpoints, identify the two common-stage endpoints, and normalize
the assumed scalar square. They are proof imports of the item. The generic component
and functor-equality substitution calculations are private helpers in these new modules.

Proof imports with `all` expose the existing cached category definitions needed for
definitional equality. Local reducibility settings keep these interfaces compatible
while leaving the large rational operations abstract. No shared definition was changed.
The DAG records the proof and the four proved helper statements.

## Proved and sorry left

Closed the sole hole: `WeilConjectures.restrictionTensorRepresentativeStageTransport`
(node `lem-pur-restriction-tensor-representative-stage-transport`).
Holes closed: 1. Holes added: 0. No declaration in this delivery contains `sorry`.
`WeilConjectures.pairRepresentative_eq_of_stage_transport` remains proved.

Also proved `WeilConjectures.mixedTensorStageComponent`,
`WeilConjectures.commonStagePullback_endpoint`,
`WeilConjectures.commonStageTensor_endpoint` and
`WeilConjectures.restrictionTensorNormalizedSquare`, including their two private helpers.
These are fully proved module extractions, not split-off obligations.

## No longer needed

No pre-existing imports were removed and no modules were withdrawn.
The proof does not reprove the integral scalar tower or scalar associator cocycle directly:
the existing pullback stage coherence theorem supplies the endpoint equations, and the
existing stage transport lemma provides the last step. Thus the original direct proof
dependencies `lem-pur-integral-operations-scalar-extension` and
`lem-weil-scalar-extension-composition` are replaced by the normalized stage interfaces.
Their modules remain transitive dependencies; no global pruning of them is claimed.
The tensor stage tower theorem is not needed; its normalized comparison definition and
existing elementary endpoint expansion are used.

## Where the brief, the DAG or earlier work was wrong

The stronger intermediate formula `c_K = T_{K/H}(d)` avoids expanding both scalar towers
and associator cocycles again. The original statement is unchanged, including reflexive
transitions. Empty schemes, repeated coefficient stages and zero objects are covered by
the same categorical argument, without assuming strict unit laws or faithfulness.

Local irreducibility settings reduced unfolding costs, and the complete single-file
proof compiled in 46.5 seconds. The instrumented delivery check nevertheless took
80.8 seconds. After improving the large-definition interfaces, the proved helpers were
extracted into modules as allowed by the worker brief's compilation instructions.
The time limit was not changed. All five modules subsequently compiled in import order:
pullback endpoint 16.2 s, tensor endpoint 24.0 s, mixed component 3.7 s, normalized
square 48.1 s, and the original module 58.0 s. The final transport rewrite was then
replaced by direct equality composition to reduce checking overhead before delivery.

## New nodes

`lem-weil-mixed-tensor-stage-component`: the generic coherent endpoint component
calculation, proved in `Sheaf.Paper.MixedTensorStageComponent`.

`lem-weil-common-stage-pullback-endpoint`: identifies the normalized pullback comparison
with the existing pair endpoint, proved in `Sheaf.Paper.CommonStagePullbackEndpoint`.

`lem-weil-common-stage-tensor-endpoint`: expands the normalized tensor comparison with
input associators, proved in `Sheaf.Paper.CommonStageTensorEndpoint`.

`lem-pur-restriction-tensor-normalized-square`: transfers the assumed mixed scalar square
to the recorded transitions, proved in `Sheaf.Paper.RestrictionTensorNormalizedSquare`.
No change records are needed: no other existing module or existing public interface changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 OK.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CommonStagePullbackEndpoint": "4fd15e3bc210a64186b5c2fe08970281b70469db", "Sheaf.Paper.CommonStageTensorEndpoint": "064d2a12b0754d0e9ec93c60edb961d0ddc7e2e1", "Sheaf.Paper.MixedTensorStageComponent": "ea217b96fe5ff8de02425f74dc172e4464a25ef1", "Sheaf.Paper.RestrictionTensorNormalizedSquare": "312fe855c536df0bb8bca95772a36848f4503ec2", "Sheaf.Paper.RestrictionTensorRepresentativeStageTransport": "7aedc61f9f3489e121da9d5887719ec3f50b7378"}, "results": {"Sheaf.Paper.RestrictionTensorRepresentativeTransport": {"hash": "4af5c650e22ec798cf7c3c9b5a5db990f11edbe6", "status": "OK"}}, "seconds": 56, "time": "2026-10-28T05:36:42+0800", "transitive": 0, "version": 1}
```

## Second reading by D2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
