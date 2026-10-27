# WeilConjectures.RationalPurityCoherence.commonSupportComposition_exists

## Reason
The uniqueness wrapper for the common support compositor now uses a separately named
existence theorem. This exposes the finite-stage descent obligation as a strictly simpler
stage-3 node while allowing the wrapper's componentwise uniqueness to be proved.

## Old
The module had no declaration named `commonSupportComposition_exists`; the existence and
uniqueness obligation was one theorem with a single `sorry`.

## New
A public theorem `commonSupportComposition_exists` states existence of the common support
isomorphism with the prescribed finite-stage component formula. The existing theorem
`commonSupportComposition_existsUnique` derives uniqueness by `Iso.ext` and component
extensionality.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.SecSmoothPurity.RationalPurityCommonComparisons | M5 | defines the wrapper from the new existence theorem |

## Status
landed 20261027T210138-L-1662835 2026-10-27 (merge of deliver/M5/Sheaf.SecSmoothPurity.RationalPurityCommonComparisons)
