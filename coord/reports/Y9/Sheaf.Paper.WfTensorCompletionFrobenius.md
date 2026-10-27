## What changed

The target theorem `wfTensorCompletionFrobenius` is assembled from two named
intermediate statements in the item module: existence of a package satisfying its
entire non-uniqueness conjunct, and uniqueness of any two such packages. The helper
predicate `WfTensorCompletion.FullProperty` packages that strict existence conjunct.
The target statement and existing public definitions are unchanged. The common-field
theorem remains at its original hole. The parent DAG node records the two split
dependencies.

## Proved and sorry left

The target `WeilConjectures.wfTensorCompletionFrobenius` is proved by a real Lean
combination of the two intermediate statements. Two strictly simpler intermediate
holes were added:

- `WeilConjectures.wfTensorCompletionFrobenius_exists` — existence conjunct;
  node `lem-wf-tensor-completion-frobenius-existence`.
- `WeilConjectures.wfTensorCompletionFrobenius_unique` — uniqueness conjunct;
  node `lem-wf-tensor-completion-frobenius-uniqueness`.

`WeilConjectures.wfTensorCompletionCommonField` remains sorry. Net: one target hole
closed; the two split declarations and this common-field declaration remain sorry.

## No longer needed

The attempted direct scalar-localization construction was withdrawn before delivery;
no planned imports or existing nodes are pruned.

## Where the brief, the DAG or earlier work was wrong

The original target proof plan is substantially larger than the time-bounded module
check. Splitting its existence and uniqueness obligations gives strictly simpler,
independently reviewable statements while preserving the exact target statement.

## New nodes

`lem-wf-tensor-completion-frobenius-existence` and
`lem-wf-tensor-completion-frobenius-uniqueness` are recorded under
`dag/nodes/sec-six-functors/`; both are intermediate obligations with complete source
and proof descriptions, and both use the unchanged target definitions.

## Second reading by Y9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
