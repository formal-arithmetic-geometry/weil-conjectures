## What changed

Removed the returned `IntegralResidueTensorRouteNormalization` module and its DAG node because
it restated the transport target with a redundant tensor presentation parameter. Restored the
published imports and the `letI := residueExchangePullMonoidal ...` statement in
`IntegralResidueTensorRouteModel`.

Replaced the redundant split with two strictly smaller components: the tensor-route calculation
on representatives whose ordinary pullback is K-flat, and the independent descent from those
representatives to arbitrary homotopy complexes. The transport theorem is now proved by applying
those two components, and the ordinary target theorem remains proved by specialization.

## Proved and sorry left

Proved: `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorRoute_model_transport`
and `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorRoute_model`.

Sorry left: `AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorRoute_kFlat` in
`lean/Sheaf/Paper/IntegralResidueTensorRouteKFlat.lean`, and
`AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_tensorRoute_descend` in
`lean/Sheaf/Paper/IntegralResidueTensorRouteDescent.lean`.

## No longer needed

Deleted `lean/Sheaf/Paper/IntegralResidueTensorRouteNormalization.lean` and its node
`new-integral-residue-tensor-route-normalization`. The previous normalization import and change
record are no longer needed. No other imports or existing nodes were pruned.

## Where the brief, the DAG or earlier work was wrong

The returned normalization theorem was not a genuine component: its explicit `tY` and hypothesis
`htY` only repackaged `residueExchangeTensorIso ℓ E Y`, so the transport target remained unproved.
The transport proof is instead decomposed at the resolving-class calculation and the subsequent
naturality/descent step.

## New nodes

`new-integral-residue-tensor-route-kflat` records the K-flat resolving-class calculation.
`new-integral-residue-tensor-route-descent` records the derived-category descent step.

## Second reading by B3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
