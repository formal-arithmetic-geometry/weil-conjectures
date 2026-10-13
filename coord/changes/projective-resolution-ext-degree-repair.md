## Reason

Upstream review #1428 classifies this theorem as a duplicate of Mathlib's
`hasProjectiveDimensionLT_iff`.  The interfaces differ: this project’s
`HasProjectiveResolutionLE` existentially packages an actual
`ProjectiveResolution`, while Mathlib’s `HasProjectiveDimensionLE` is an
Ext-vanishing typeclass.  The callers unpack the former, so deleting this
bridge is not type-correct.

## Old

The theorem stated the Ext degree as `n + 1`.

## New

The theorem states the same degree as `Nat.succ n`.  These are definitionally
equal, and the proof and caller behavior are unchanged.

## Users

- `Sheaf.AlgebraicGeometry.AffinePolynomialResolutionOfStalkwise`: obtains an
  explicit bounded resolution from the theorem.
- `Sheaf.RingTheory.ProjectiveResolutionExtAllDegrees`: invokes the theorem in
  its degree induction.
- `Sheaf.RingTheory.ProjectiveResolutionExtCharacterization`: includes the
  theorem in its conjunction.

## Status

landed 20261013T190135-L-3214396 2026-10-13 (merge of deliver/C1/Sheaf.RingTheory.ProjectiveResolutionExtDegree)
change is definitionally equal.
