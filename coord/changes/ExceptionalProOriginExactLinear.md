# Sheaf.Paper.ExceptionalProOriginExactLinear

## Reason

The quarantined module is restored and its theorem is proved from the recorded
exact derived comparison and adjunction structures. The scalar-action construction
is a separate strictly smaller theorem in `Sheaf.Paper.ExceptionalProScalarActions`
so the remaining proof obligation is isolated in its own node. The public theorem
signatures are unchanged; the new import is private to the proof.

## Users

- `Sheaf.Paper.ExceptionalSystemTransport`
- `Sheaf.SixFunctors.ExceptionalIntegralSystemExistence`

## Changes

The proof constructs additive, integer-shift, and triangulated structures using
existing exact comparison factors and adjunction APIs, then combines them with the
new scalar-action theorem. No existing definition or target statement is changed.
