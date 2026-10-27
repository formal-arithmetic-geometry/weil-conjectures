## What changed

Added the proof imports `Sheaf.Paper.QcqsCompactSupportOpenComplete` and
`Sheaf.Paper.QcqsCompactSupportProperComplete`. The target theorem now composes the
open-extension and proper-direct-image completeness statements. Added the two DAG
nodes listed below for these strictly smaller proof steps.

## Proved and sorry left

`WeilConjectures.sfQcqsCompactSupport_image_complete` is proved by composition.
The two strictly smaller preservation statements remain as named `sorry`s:

- `WeilConjectures.sfQcqsCompactSupport_open_complete` in
  `lem-qcqs-compact-support-image-complete-open`.
- `WeilConjectures.sfQcqsCompactSupport_proper_complete` in
  `lem-qcqs-compact-support-image-complete-proper`.

Thus one target hole was closed and two lower holes were added as a decomposition.

## No longer needed

No imports or declared dependencies from the original target module were removed.
The original DAG proof had no listed proof dependencies.

## Where the brief, the DAG or earlier work was wrong

The DAG described the whole proper/open transport in one step and provided no
intermediate declarations. Existing public modules expose the component
constructions but no theorem with the exact `IsSfDerivedComplete` conclusion, so the
argument was split into its open and proper factors. The target statement itself is
unchanged.

## New nodes

`lem-qcqs-compact-support-image-complete-open` records completeness after the
quasi-compact completed open extension, stated in
`Sheaf.Paper.QcqsCompactSupportOpenComplete`.

`lem-qcqs-compact-support-image-complete-proper` records completeness after the
proper completed direct image, stated in
`Sheaf.Paper.QcqsCompactSupportProperComplete`.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
