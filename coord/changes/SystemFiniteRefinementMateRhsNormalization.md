# Sheaf.Paper.SystemFiniteRefinementMateRhsNormalization

## Reason

Close the existing `rhsNormalization` proof using canonical evaluation, a private
categorical cancellation helper, and the new `rhsCore` intermediate theorem. The
module gains one proof-only import and a private helper; its public theorem signature
and all existing declarations remain unchanged.

## New

The proof-only import is `Sheaf.Paper.SystemFiniteRefinementMateRhsCore`.
No source-library declaration, definition, signature, attribute or target statement is
changed.
