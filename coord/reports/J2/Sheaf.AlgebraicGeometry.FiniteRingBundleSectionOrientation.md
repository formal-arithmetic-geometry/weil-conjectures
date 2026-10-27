## What changed

The signatures and public imports of all four item theorems are unchanged. The previously
proved existence/uniqueness and valuation theorems keep their proofs.

Naturality now reduces the inverse-map equality to affine frames using the existing
bundleSectionOrientation_map_ext. A frame supplied by the linearity hypothesis has the
same zero-section lift by Cartesian uniqueness. The generic section-comparison pasting
law identifies the actual comparisons. The two normalization equations give the same
local arrow. A proved private equality-transport helper handles their proof-dependent
section equations, and inverse cancellation proves the desired forward-map equality.

Rank zero uses the existing proved VectorTraceGeometry.zero_isIso to construct e=asIso π.
Cancellation proves e.inv=z. Open exceptional base change at the identity base proves
the canonical identity comparison invertible. Its one-frame identity-counit equation
gives a normalized orientation, which equals the supplied orientation by uniqueness.

Added two proof-only imports for the two component equations, plus a proof-only import
of VectorTraceGeometry. Added their nodes, and updated the parent proof and dependencies.
Change record: coord/changes/J2-bundle-section-comparison-steps.md.

## Proved and sorry left

Closed both original upper holes:
AlgebraicGeometry.Etale.finiteRingBundleSectionOrientation_naturality and
AlgebraicGeometry.Etale.finiteRingBundleSectionOrientation_rankZero.

Added two strictly smaller holes:

- AlgebraicGeometry.Etale.bundleSectionComparison_iso_pasting
  (lem-trf-bundle-section-comparison-iso-pasting).
- AlgebraicGeometry.Etale.bundleSectionRankZero_affineNormalization
  (lem-trf-bundle-section-rank-zero-affine-normalization).

This is a decomposition of 2 holes into 2 component-equation holes, not a net proof gain.
The item module has zero sorry left. No sorry is added to a definition or private helper.
Existing upstream holes remain in imported modules; they are not modified in this delivery.

Validation: all three sandbox modules compiled through lcompile.py. The final parent
compile passed in 13.1 seconds without warnings. Delivery preflight is run by deliver3.py.

## No longer needed

No existing import or module is removed. All three previous proof imports remain used.

The parent's direct proof dependencies lem-amb-etale-adjoint-locality,
def-weil-pbc-adjunction-conjugate, lem-weil-pbc-mate-pasting, and
def-weil-pbc-composite-adjunction are replaced by the precise component equations used by
the Lean proof. Mate/conjugate/identity-adjunction infrastructure remains needed in the
new component-equation nodes. EtaleAmbientAdjointLocality itself is not needed on this
route: comparison invertibility uses the already-defined exceptional open base-change map,
and naturality uses comparison pasting directly. No library withdrawal is proposed.
The rank-zero geometric dependency def-pur-vector-trace-geometry is now explicit.

## Where the brief, the DAG or earlier work was wrong

The parent plan called rank-zero normalization elementary but the exact identity-adjunction,
coefficient and compact-support comparison equation was not separately stated. It is now
isolated at one affine frame, while the geometric isomorphism, invertibility and uniqueness
assembly are proved in the parent. Naturality similarly needed an exact section-comparison
pasting equation beyond the general abstract mate law. No statement was changed and no
unit route was bypassed.

The source-library boundary is respected. Empty schemes, zero rings and N=1 require no
new hypotheses: Cartesian uniqueness, canonical invertibility, identity adjunction laws
and the existing affine-frame detector all include these cases.

## New nodes

lem-trf-bundle-section-comparison-iso-pasting records the generic source-isomorphism
pasting equation for the specified section comparisons. Library and whole-blueprint
searches found no statement of this component equation; Mathlib supplies mate pasting
as a tool. Its module is BundleSectionComparisonIsoPasting.

lem-trf-bundle-section-rank-zero-affine-normalization records the rank-zero comparison's
one-frame inverse-map equation. It does not assert the parent rank-zero theorem: the
parent still constructs e, proves its inverse and comparison invertibility, then uses
normalization and equality detection. Its module is BundleSectionRankZeroAffineNormalization.

## Second reading by J2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
