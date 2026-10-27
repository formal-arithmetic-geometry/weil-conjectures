# WeilConjectures.IntegralSystemRealization.FiniteCoordinates.rhsCore

## Reason

Add the strictly smaller finite proper/open mate transport statement needed to prove
`rhsNormalization` after the canonical bridge factors are cancelled. This is a new
public theorem in `Sheaf.Paper.SystemFiniteRefinementMateRhsCore`; no existing
source-library declaration, definition, signature, attribute or target statement is
changed.

## New

The new theorem has the exact signature recorded by
`lem-sf-system-finite-refinement-mate-rhs-normalization-core`. Its proof is left as a
named stage-3 split with the source and proof sketch in its docstring.

## Users

`Sheaf.Paper.SystemFiniteRefinementMateRhsNormalization` imports this module privately
and uses `rhsCore` in the proof of `rhsNormalization`.
