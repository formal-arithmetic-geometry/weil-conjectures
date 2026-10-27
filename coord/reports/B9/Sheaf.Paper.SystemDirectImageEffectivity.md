## What changed

Replaced the hole in `WeilConjectures.systemDirectImage_effective` by a complete Lean
argument from a projection-compatible Roos presentation and the existing finite
reduction clause of `sfIntegralDirectImage_constructible`. A proved private categorical
lemma transports invertibility of adjunction transposes across the two comparison
isomorphisms. The counit projection equation then identifies the actual evaluated
counit, and conservativity of evaluation gives the whole-system result.

Added the proof-only import `Sheaf.Paper.SystemDirectImageRoosPresentation`. This new
module isolates the geometric model comparison needed before finite reduction can be
applied. Updated the item's proof and dependencies to match the Lean argument.
Existing signatures and public imports are unchanged; no other existing module changes.
Both delivered modules compile without warnings, individually in import order (3.7 s
and 5.1 s in the final compile).

## Proved and sorry left

Closed the original hole in `WeilConjectures.systemDirectImage_effective`
(`lem-weil-system-direct-image-effectivity`). Its combining argument is complete.
Added one named hole: `WeilConjectures.systemDirectImage_roosPresentation`
(`lem-weil-system-direct-image-roos-presentation`). The item has zero remaining holes;
the new module has one. This is a decomposition: one hole closed, one added, net zero.
The remaining assertion constructs a projection-compatible Roos model for arbitrary
ambient complexes; it asserts no counit invertibility and uses no completeness or
constructibility. The finite reduction and actual-counit argument are proved here,
not included in that remaining assertion.

## No longer needed

No existing imports were removed and no modules were withdrawn. The item's direct
proof dependency on `def-sp-varying-ring-operations` is replaced by the smaller actual
system evaluation/model comparison in the new node. The separate direct dependency
on `lem-sf-complete-direct-image-reduction` is unnecessary: its finite reduction result
is already supplied by `lem-sf-integral-direct-image-constructible` used in the proof.
`lem-trf-integral-pullback-comparison-realization` is no longer a proof dependency;
its coefficient-data interface remains a statement dependency. These observations
concern this proof, not a claim that their modules are globally unused.

## Where the brief, the DAG or earlier work was wrong

The stated dependencies provide finite direct-image reduction and the normalized
coefficient counit formula, but none directly states the projection-compatible Roos
presentation for the actual `integralComparisonSequenceDirectImage` at an arbitrary
coefficient calculus. A finite evaluation isomorphism alone does not provide the
necessary projection equality. The new node isolates that missing model comparison.
The main proof uses conservativity of evaluations, not faithfulness, and does not
infer equality of derived system morphisms from their finite components.

Read the current server queue before working: this is a stage-3 proof row with one
hole, not a zero-hole rework assignment. The older quarantine record is retained;
no archive or attachment is removed. Zero complexes and empty schemes are covered
by the Roos presentation and the existing finite reduction theorem; no nonemptiness
or positive-dimension hypothesis was added. The blueprint unit's statements and
realized steps are unchanged.

The existing DAG metadata also has a cycle already present before this delivery:
`lem-weil-system-direct-image-effectivity` ->
`lem-sf-integral-direct-image-constructible` ->
`lem-sf-complete-direct-image-reduction` -> `def-weil-derived-direct-image` ->
`lem-sf-rational-direct-image-adjunctions` ->
`lem-sf-integral-pullback-linear-adjunction` ->
`def-weil-system-operation-exchange-realization` -> the item. The
`def-weil-derived-direct-image` record currently combines the finite/integral
`SfDerivedDirectImage` declarations with a common-stage primary attachment and
common-stage proof dependencies, despite its ownership-repair lead note. The new
presentation refers only to the existing finite/integral definitions. Its actual
Lean imports have no cycle and both files compile. This pre-existing ownership/
dependency inconsistency is reported for the maintainer; no unrelated node is edited.

## New nodes

`lem-weil-system-direct-image-roos-presentation` records
`WeilConjectures.systemDirectImage_roosPresentation` in
`Sheaf.Paper.SystemDirectImageRoosPresentation`. Its docstring and node spell out the
single-resolution finite evaluation, restriction-transition comparison, and transport
of the normalized Roos triangle with every actual projection. It follows Zheng,
Construction 4.1 and Lemma 4.10, and the ringed-sequence inverse limit of Stacks 0941.
The existing direct-image evaluation, restriction-transition and constant-tower Roos
comparison nodes are used as tools; no unit route is replaced. The theorem is strictly
a model-comparison step and does not repackage the original effectivity assertion.
No definition or statement repairs and no change records are needed.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
