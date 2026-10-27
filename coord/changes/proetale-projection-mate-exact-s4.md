# Native pro-etale projection mate decomposition

## Reason

The target uses native pro-etale functors with distinct site-object, site-morphism,
and coefficient universes. The generic ringed projection-mate theorem cannot be
applied at these universes, so the proof needs two native intermediate interfaces.

## Old

`Sheaf.Paper.ProEtaleProjectionMateExact` contained one `sorry` theorem. No
existing library declaration or module was modified by this delivery.

## New

Two new public modules provide `proEtaleProjectionMateShiftData` and
`proEtaleProjectionMateData`; the item combines them to prove the original target.
The data theorem takes the two shift structures as typeclass hypotheses because
Mathlib's `NatTrans.CommShift` requires those instances.

## Users

The item module is the only current consumer. Future proof consumers use the
original target declaration; the two intermediate declarations are available for
their own proof work.

## Status

Pending independent review and landing with this stage-3 delivery.
