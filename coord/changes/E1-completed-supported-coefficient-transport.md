# Sheaf.Paper.CompletedSupportedCoefficientTransport

## Reason

The transport proof uses a new ordinary normalization theorem as a strictly
simpler split-off step. The item imports that theorem privately and retains the
existing public imports and declarations. The target theorem signature and the
coefficient isomorphism definitions are unchanged; the added local comparison
lemmas and linter options affect only this proof module.

## Changes

- Added `Sheaf.Paper.CompletedSupportedCoefficientTransportNormalization` with the
  ordinary normalization statement and its documented proof obligation.
- Added a private import of that module to the target proof.
- Added private comparison lemmas and the exact-square transport proof in the
  target module.

No source-library module was changed and no existing consumer requires adaptation.
