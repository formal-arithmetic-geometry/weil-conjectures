## What changed

Proved `WeilConjectures.IntegralSystemRealization.systemPushIdentityPair` by adjoint
conjugation. The proof uses the normalized pullback identity data supplied by the
new lower-level `systemPushIdentityPullUnit` statement, applies the generic
right-adjoint conjugate unit calculation, transports along `1_X ≫ 1_X = 1_X`,
and evaluates the resulting natural-isomorphism equality at `M`. Added the
required `StrictTowerDirectImageCoherence` proof import for the generic mate lemma.

## Proved and sorry left

Closed `systemPushIdentityPair` (one original `sorry`). Added one strictly lower
intermediate obligation, `systemPushIdentityPullUnit`, whose proof remains
`sorry` and records the ordinary section-normalization and bridge-mate argument.
No definition contains a `sorry`.

## No longer needed

No existing dependency node or module was pruned. Finite evaluation, constructibility,
compactification data and localization-faithfulness arguments are not used by the
completed direct-image calculation; they remain outside this module's imports.

## Where the brief, the DAG or earlier work was wrong

The original item was missing the inverse-image identity normalization needed to
instantiate the generic adjunction mate lemma. This is a genuine lower-level
statement, so it is split into its own module rather than duplicating the target
statement under another name. No target signature or adopted source declaration
was changed.

## New nodes

Added `lem-sf-system-push-identity-pair-pull-unit`, for
`systemPushIdentityPullUnit` in `Sheaf.SixFunctors.SystemPushIdentityPullUnit`.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
