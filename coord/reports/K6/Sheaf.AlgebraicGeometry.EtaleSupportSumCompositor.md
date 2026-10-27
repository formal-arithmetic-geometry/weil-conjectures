## What changed

Added the proof-only component module `Sheaf.AlgebraicGeometry.EtaleSupportSumCompositorComponent`.
The original module now proves the natural-transformation equality by extensionality and applies the
objectwise component theorem. The component theorem is a named split-off statement with the
geometric support/sum calculation left as its single `sorry`.

## Proved and sorry left

The declaration `AlgebraicGeometry.Etale.etaleSupportSumCompositor` is proved. One strictly
smaller objectwise statement remains as `sorry`: `AlgebraicGeometry.Etale.etaleSupportSumCompositor_app`
in `lem-pur-etale-support-sum-compositor-component`.

## No longer needed

No imports were removed. The target proof uses only the new component node directly; the seven
geometric proof dependencies remain attached to that split-off component statement.

## Where the brief, the DAG or earlier work was wrong

The original proof plan requires a long graph-normalized support calculation. It was reduced to
one objectwise statement plus the real extensionality proof of the natural-transformation equality.

## New nodes

`lem-pur-etale-support-sum-compositor-component` records the objectwise support/sum compositor
calculation and its source, proof dependencies, and Lean declaration.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
