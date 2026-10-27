## What changed

Proved `AlgebraicGeometry.ProEtale.PurityTransport.scalarPull_isIso` in
`Sheaf.SecSmoothPurity.TransportCompact`. Added the proof-only import
`Sheaf.SixFunctors.ScalarSixDerivedPullbackNormalization`. Obtain its existing
`scalarSixPullbackData_exists` witness, rewrite the published mate backwards by
`thetaNormalization`, and use invertibility of the hom of `theta`.

Updated `def-pur-transport-compact-support-coordinates` with this implemented
proof and its one proof dependency. All declaration signatures, definition
bodies, public imports, and the unit's statement and realized steps are unchanged.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.ProEtale.PurityTransport.scalarPull_isIso`
(node `def-pur-transport-compact-support-coordinates`).

Original holes: 1. Closed: 1. Added: 0. Remaining in the delivered module: 0.
No split-off statements and no decomposition.

Validation: the required `lcompile.py` single-file compile passed (exit 0,
24.0 seconds), including the launcher's private overlay of unpublished
transport-coordinate dependencies.

## No longer needed

None. No imports, nodes, modules, or declarations were removed. The existing
normalized scalar pullback theorem supplies the mathematical argument, so no
new K-flat comparison lemma or coherence theory is needed for this item.

## Where the brief, the DAG or earlier work was wrong

The item's node had no proof steps or proof dependencies despite its Lean
invertibility hole. The existing theorem
`CondensedRing.scalarSixPullbackData_exists` already supplies the precise
normalized comparison needed here. Its normalization equation identifies the
actual published arrow, so an arbitrary isomorphism or a flatness hypothesis
is unnecessary.

`lem-sfb-scalar-six-derived-pullback-normalization`, filed under
`sk-prop-scalar-six`, is used as a generic coefficient-comparison tool, not as
a replacement for any step of `sk-thm-purity-transport`. No change record is
needed because this delivery changes only a theorem proof, its private proof
import, and the corresponding DAG proof fields.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
