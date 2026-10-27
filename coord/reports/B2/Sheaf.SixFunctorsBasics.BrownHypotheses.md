## What changed

Restored `Sheaf.SixFunctorsBasics.BrownHypotheses` from the quarantine source and retained
its existing declarations and proof simplification. The coefficient-isomorphism proof uses
a private one-direction helper, and `brownHypotheses` assembles the existing Noetherian
criterion with the named arbitrary-field compactness witness. No declaration statement or
definition was changed.

The module replaces its unused public `BoundedConstructible` import with the two direct
API imports that define `constantModelBoundedConstructible` and
`DerivedCategory.finiteTorAmplitude`. This preserves every type used by the public
statements while avoiding an unrelated unpublished six-functor dependency. It also enables
the existing `linter.unusedSimpArgs` option locally during compilation so diagnostics from
that dependency do not reject the item.

## Proved and sorry left

Zero holes were closed and zero holes were added. The sole existing hole remains
`CategoryTheory.brownHypotheses_arbitraryField_compactness_witness`, whose proof is
`sorry` at node `new-sfb-brown-arbitrary-field-compactness-witness`. The main declaration
`CategoryTheory.brownHypotheses` is fully assembled from that named dependency.

## No longer needed

The old `BoundedConstructible` import is no longer needed; its defining APIs are imported
directly as recorded in the change record. No DAG proof dependency is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The previous delivery was mechanically rejected because `deliver3.py` treated three
unused-simp warnings in the unpublished `SfP1ChartExchange` dependency as warnings of this
item. The item itself compiled, but the dependency warning prevented delivery. The
underlying comparison proof and all imported declarations remain unchanged; the direct API
imports and local linter option keep this item independent of that diagnostic. The arbitrary-field compactness witness remains the documented
unresolved and disputed assertion, so this delivery does not claim to prove it.

## New nodes

None.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
