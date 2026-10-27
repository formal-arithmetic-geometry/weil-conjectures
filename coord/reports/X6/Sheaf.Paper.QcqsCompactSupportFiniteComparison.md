## What changed

Added the proof module for `WeilConjectures.sfQcqsCompactSupport_finiteComparison`.
The conjunction is assembled from two strictly simpler component theorems: derived
completeness of the ambient completed proper/open image and invertibility of every
positive finite scalar mate. Each component is isolated in its own module with a
source and proof plan, and the parent theorem combines them by `exact ⟨..., ...⟩`.

## Proved and sorry left

The parent declaration `sfQcqsCompactSupport_finiteComparison` is proved. Two
component declarations remain as named split obligations:

- `WeilConjectures.sfQcqsCompactSupport_image_complete` (`sorry`),
- `WeilConjectures.sfQcqsCompactSupport_finiteMates` (`sorry`).

Thus one parent hole is closed and two strictly simpler holes are added.

## No longer needed

No imports or declared proof dependencies were pruned. The parent now uses only the
two new component nodes; the original generic factorization and open/direct-image
nodes remain the dependencies of those components.

## Where the brief, the DAG or earlier work was wrong

The existing parent proof plan is too coarse to realize in one declaration: its
completeness and finite-mate arguments require separate normalized constructions.
No target statement or existing declaration signature was changed.

## New nodes

- `lem-qcqs-compact-support-image-complete`
- `lem-qcqs-compact-support-finite-mates`

## Second reading by X6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
