## What changed

Added the proof of `WeilConjectures.PurCompactSupport.openProjectionFactor_coefficient_change`.
The proof composes the open projection isomorphism square with the compactification pullback
compositor transport. Added `Sheaf.Paper.OpenProjectionIsoCoefficientChange` and
`Sheaf.Paper.OpenProjectionFactorCompositorTransport` as the two strictly simpler split-off
steps, and imported them from the item module. Updated the item DAG proof route accordingly.

## Proved and sorry left

Proved the item theorem `openProjectionFactor_coefficient_change` (one hole closed).
The delivery adds the strictly simpler split-off statements
`openProjectionIso_coefficient_change` (node `lem-sf-open-projection-iso-coefficient-change`)
and `openProjectionFactor_compositor_transport` (node
`lem-sf-open-projection-factor-compositor-transport`); both remain `sorry` for parallel proof.
The actual hole count is: 1 closed, 2 added by decomposition.

## No longer needed

No imports or proof dependencies were pruned beyond removing the exploratory
`RingedExchangeTensorCoherence` import from the item module; the final item proof uses only
the two split-off modules and the coefficient data imported by them.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated the open factor as directly covered by the generic tensor mate
lemma. That lemma is formulated for pullback adjunctions, whereas the open projection is defined
using the extension-by-zero adjunction. The proof therefore needs a separate open projection
square and a separate pullback-compositor transport step.

## New nodes

`lem-sf-open-projection-iso-coefficient-change`: the coefficient square for the open projection
isomorphism before compactification compositors; source Tags 0E8I and 07A6.

`lem-sf-open-projection-factor-compositor-transport`: transport of source and target composites
through the c.i then c.g pullback compositor; source Tags 0D6D and 07A6.

## Second reading by D6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
