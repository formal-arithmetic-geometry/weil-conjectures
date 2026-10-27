## What changed

Reduced all three original holes in `Sheaf.Paper.PodReindexingEvaluationShiftComposition`.
The item now proves the evaluation consequences (uniqueness among all arrows, transport
of transpose and both-variance naturality), and derives the Hom composition and identity
equations from the corresponding tensor equations. The generic private calculations
use the closed adjunction, evaluation naturality, tensor-comparison naturality, and
cancellation of isomorphisms. They do not assume either Hom coherence equation.

Moved the existing presentation declarations, with the same signatures and bodies,
into `Sheaf.Paper.PodReindexingCoherenceData`. The item publicly re-exports that module.
This permits four smaller theorem modules to import the presentations without a cycle:
`PodReindexingEvaluatedComparison`, `PodReindexingSignedShifts`,
`PodReindexingTensorCompositor`, and `PodReindexingTensorIdentity`.
Existing representative-evaluation, comparison-uniqueness and symmetry proofs remain.
Local elaboration attributes in the data module keep structure auxiliaries from
expanding the derived reindexing presentations when comparing different parameters.
These attributes are scoped to this file and change no exported definition or attribute.
The target statements and the mathematical statements of every existing declaration
are unchanged. The item node records the actual proof and the moved declarations.

Validation: all six delivery modules and both direct importers compiled cleanly
with `lcompile.py --all` (result `a8fdcc04cfd4163f40bc974f`). The data module took
33.3 seconds and the item took 59.0 seconds. Both direct importers,
`Sheaf.Paper.PodReindexingCompletedEvaluationReflection` and
`Sheaf.Paper.ReindexingSystemHomReductionSquare`, compiled unchanged. Their temporary
copies were removed after checking; no consumer source change is delivered. All 24
original public declaration signatures and all old public imports are preserved.
All profiling options were removed before this check.
Change record: `coord/changes/K8-pod-reindexing-coherence-data.md`.

## Proved and sorry left

This is a decomposition, not a sorry-free proof. The three original holes closed are:

- `WeilConjectures.PodReindexingCoherence.comparison_exists`;
- `WeilConjectures.PodReindexingCoherence.composition`;
- `WeilConjectures.PodReindexingCoherence.identity`.

There are zero textual holes in the item module and four new holes, each the entire
proof of a public named theorem in its own module:

- `WeilConjectures.PodReindexingCoherence.evaluated_comparison_exists`, node
  `lem-pod-reindexing-evaluated-comparison`: construct Comparison and its evaluation
  equation; omits uniqueness, transposition, naturality and every shift assertion.
- `WeilConjectures.PodReindexingCoherence.signed_shift_laws`, node
  `lem-pod-reindexing-signed-shifts`: construct the signed chain shifts and prove the
  chain and derived shift squares for an already supplied Comparison.
- `WeilConjectures.PodReindexingCoherence.tensor_compositor_exists`, node
  `lem-pod-reindexing-tensor-compositor`: construct the canonical site/localization
  compositor and prove its tensor equation; no Hom equation.
- `WeilConjectures.PodReindexingCoherence.tensor_identity_exists`, node
  `lem-pod-reindexing-tensor-identity`: construct the canonical site/localization
  identity and prove its tensor equation; no Hom equation.

The data module has zero holes. No definition or private helper contains `sorry`.
Net textual hole count for this delivery: three closed, four added (minus one net).

## No longer needed

No old public import is removed: the item continues to expose its previous public API.
All new proof imports are used. No module is withdrawn or globally pruned.
The parent no longer proves the concrete comparison construction, signed-shift
calculation, or tensor compositor and identity construction inline: these are exactly
the four new nodes, with their existing source dependencies recorded below them.
The parent derives the Hom compositor/identity laws solely from evaluation, so the
abstract source-library `ihomComparison_comp_app` theorem and any additional Hom
compositor-construction lemma are unnecessary for this implementation. The tensor
normalization dependency remains necessary in the new construction nodes. The old
parent dependencies `def-pur-hom-complex`, `def-pur-kinjective-complex`,
`lem-pod-reindexing-hom-resolution-model` and
`lem-sfb-ringed-derived-monoidal-comparisons` move to the corresponding smaller
construction/shift nodes; none is globally pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement defect was found. The newest blueprint places
`prop-pod-dual-tate-data-compatibility.proof.md` under `sk-thm-frobenius`, rather than
the older `sk-lem-finite` source path recorded by the parent. The new nodes cite the
current `literature/blueprint/latest/` path. The unit route is retained.

The already stated Hom-resolution-model theorem supplies its chain comparison only
for K-injective targets, while Comparison requires all target complexes. Its ordinary
product-factor construction extends to those targets, but this construction and the
tensor-model glue still require proof. They are explicitly retained in
`evaluated_comparison_exists`, rather than assumed to follow just by applying the
existing theorem. Likewise, the general monoidal-comparison theorem does not directly
supply this sectionwise reindexing presentation; its concrete compatibility is retained
in the tensor compositor/identity nodes.

## New nodes

`def-pod-reindexing-coherence-data` records the relocated, pre-existing presentation
definitions (Comparison, EvaluationLaws, signed shifts, Compositor, Identity and their
category abbreviations). It introduces no new mathematical object or existence claim.

`lem-pod-reindexing-evaluated-comparison` is the concrete construction and evaluation
step (parent Steps 1--2), with a complete source-based proof in words and the exact
finite/completed coefficient universes.

`lem-pod-reindexing-signed-shifts` is the independent signed chain calculation and
localization step (parent Steps 7--8), with the full signed calculation in words.

`lem-pod-reindexing-tensor-compositor` is the site/termwise/localized tensor part of
the parent's composition step. Its Hom consequence is proved in the item.

`lem-pod-reindexing-tensor-identity` is the corresponding identity construction and
tensor equation. Its Hom consequence is proved in the item. Identity schemes, empty
schemes, finite stage zero (exponent one), completed coefficients, arbitrary unbounded
complexes and positive/negative shifts introduce no exceptions to these arguments.

Searches covered LeanSearch, LeanFinder/Loogle, Mathlib grep, and both library roots.
The abstract source-library Hom composition result exists, but does not construct the
specified concrete tensor/site comparisons. The new nodes record these searches. Searches of the entire imported blueprint for
reindexing, evaluation, tensor and Hom shifts found no duplicate of the new steps.

## Second reading by K8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
