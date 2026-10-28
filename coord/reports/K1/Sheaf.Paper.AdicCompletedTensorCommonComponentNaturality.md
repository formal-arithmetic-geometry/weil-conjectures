## What changed

Replaced the hole in `completedTensorCommonComponent_naturality` by simultaneous
finite-stage representatives. The proof represents both input arrows over a common
coefficient field, transports both endpoint components there, applies fixed-field
naturality, and cancels the endpoint isomorphisms. The generic cancellation lemma and
this representative argument are complete Lean proofs.

Added the real definition `completedTensorStageComponent`, using the existing
integral component and natural inclusion tensor comparison. Proved
`completedTensorIntegralComponent_natural_iso` by pasting the integral realization,
ordinary tensor, quotient-completion and integral-to-rational comparisons. Its last
naturality square follows from the prescribed bilinear rational tensor action at
scalar coefficients 1 and 1. Proved `completedTensorStageComponent_naturality` by
full faithfulness of precomposition with the product scalar localization and then
composition with `commonInclusionTensorComparison`.

The integral proof is in `AdicCompletedTensorIntegralNaturality`; rational descent is
in `AdicCompletedTensorStageNaturality`. Profiling first identified expensive
conversion of the chosen rational tensor and localization data. Private
proof lemmas, local irreducibility of large functors, and a generic localization
descent lemma avoid repeated unfolding. The two self-contained proofs were then
separated to keep each file within the per-file compile limit.

The item adds proof imports of the fixed-field naturality and objectwise transport
modules. The new integral module publicly imports the existing common-component
module because its statement uses that component. The finite-stage definition
publicly imports the existing inclusion-comparison module because its body uses it.

## Proved and sorry left

Closed the original one hole:
`WeilConjectures.AdicQbarRealization.completedTensorCommonComponent_naturality`
(node `lem-sf-adic-completed-tensor-common-component-naturality`).

The following new auxiliary theorems have complete proofs and zero holes:
`WeilConjectures.AdicQbarRealization.completedTensorIntegralComponent_natural_iso`
and `WeilConjectures.AdicQbarRealization.completedTensorStageComponent_naturality`.
The new finite-stage component is a genuine construction with zero holes.

Added exactly one hole:
`WeilConjectures.AdicQbarRealization.completedTensorCommonComponent_stage_transport`
(node `lem-sf-adic-completed-tensor-component-stage-transport`, module
`Sheaf.Paper.AdicCompletedTensorComponentStageTransport`). This is the objectwise
coefficient-enlargement equation, with no arbitrary arrow. Its source and full
K-flat/pure-section proof are in its docstring and node. It remains needed at the
two endpoints in the proved representative argument.

Thus the item has zero holes, and the delivery has one hole in total: one upper hole
closed and one strictly smaller lower step added. This is a decomposition, with net
hole reduction zero, not a claim of an unconditional proof of the original theorem.

Validation: `lcompile.py --all` compiled all five files in import order with no
errors or development-option warnings. The integral naturality module took 34.4 s,
the rational naturality module 31.5 s, the transport statement 3.6 s, and the item
6.5 s; the finite-stage definition reused its successful 4.1 s compile. Every file
is below 60 s. Exact-signature checks preserve the original theorem statement and
match each new node's Lean attachment; proof-dependency unions and node references
also agree. Only the named transport theorem contains `sorry`.

## No longer needed

No original imports are removed, and no existing modules or nodes are withdrawn.
The original realization, finite-model, common-stage tensor and coherence
dependencies remain needed through the finite-stage arguments. None is claimed
as pruned. No common-lift agreement theorem is imported. The integral proof does
not need coefficient enlargement or ringed tensor coherence; the rational
naturality proof needs no comparison between two finite models.

## Where the brief, the DAG or earlier work was wrong

The original plan described naturality of individual integral comparisons but did
not supply the integral or fixed-field equations as callable Lean declarations.
These are now proved, including the passage from integral to arbitrary rational
arrows. Naturality of the individual natural isomorphisms alone does not identify
the independently specified finite-model comparisons after coefficient enlargement;
that separate objectwise equation is the remaining hole.

The replacement node records the actual representative-and-cancellation proof.
Every existing declaration signature, definition, instance, public attribute and
public import is preserved. The unit route is preserved. Edge cases use no nonzero
objects or maps, nonempty scheme, strict coefficient enlargement, or faithful
realization; reflexive extensions retain their specified scalar unitor.

## New nodes

`def-sf-adic-completed-tensor-stage-component` defines the explicit component at one
rational coefficient stage, using the existing natural inclusion tensor comparison.
It contains no data chosen from an unproved existence statement.

`lem-sf-adic-completed-tensor-integral-naturality` records the proved natural
isomorphism on integral pairs and the equation specifying each component.

`lem-sf-adic-completed-tensor-stage-naturality` records the proved naturality at
one fixed rational field, obtained by localization descent and the natural
inclusion comparison.

`lem-sf-adic-completed-tensor-component-stage-transport` records the remaining
objectwise equality between the compositum component and the formula at a larger
field, conjugated by the actual `isoToStage` maps. It is a coefficient-normalization
step, not the arbitrary-arrow naturality statement under another name.

All new nodes have source context, Mathlib searches, proof plans, exact Lean
attachments, and the original chapter and unit. No change record is required:
only the item, new modules, and their own node files are changed.

## Related modules compiled before delivery

1 related module(s) compiled against this delivery by deliver3.py: 1 INFRA.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.AdicCompletedTensorCommonComponentNaturality": "c70a8ac3419adcbb0ed799b6b4119d67044d7820", "Sheaf.Paper.AdicCompletedTensorComponentStageTransport": "ff8e87001d0fd0ac1183892bef7873f1bc18d557", "Sheaf.Paper.AdicCompletedTensorIntegralNaturality": "12ef880870ab6428da7dd2f9d0f1d10597eca620", "Sheaf.Paper.AdicCompletedTensorStageComponent": "a0a6a7776ce22a6fc0be13ba40a27eb35b9427ba", "Sheaf.Paper.AdicCompletedTensorStageNaturality": "66b2976c461d52226b517511bbb0c9efbf126ad6"}, "results": {"Sheaf.Paper.AdicCompletedTensorCommonLiftTensorUnit": {"hash": "25a7a8461dc37dc61806529e6accea3fd35ab7e9", "status": "INFRA"}}, "seconds": 85, "time": "2026-10-28T11:27:40+0800", "transitive": 0, "version": 1}
```

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
