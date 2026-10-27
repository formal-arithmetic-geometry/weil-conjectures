# Bundle section naturality and rank-zero proof steps

Status: all three sandbox modules compile; delivery preflight and global build verification
are performed by the delivery and maintainer workflows.

The existing four theorem signatures and the public imports of
Sheaf.AlgebraicGeometry.FiniteRingBundleSectionOrientation are unchanged. The two remaining
proof holes are reduced to smaller, separate component equations; no definitions change.

New public theorem interfaces:

- Sheaf.AlgebraicGeometry.BundleSectionComparisonIsoPasting declares
  AlgebraicGeometry.Etale.bundleSectionComparison_iso_pasting. It is the section-level
  component of exceptional base-change pasting for a source isomorphism over an identity
  base. It mentions no Tate coefficient, bundle frame, or orientation.
- Sheaf.AlgebraicGeometry.BundleSectionRankZeroAffineNormalization declares
  AlgebraicGeometry.Etale.bundleSectionRankZero_affineNormalization. For an existing
  rank-zero geometric identification and invertible canonical comparison, it gives that
  comparison's inverse-map equation on one affine frame. It does not construct the
  identification or compare with an arbitrary normalized orientation.

Each new module has one named theorem hole and a node with a complete proof plan.
Their only consumer is this delivery's item module, through private proof imports. Existing
consumers continue to see precisely the same four statements and the same definitions.
The item uses the already-proved VectorTraceGeometry.zero_isIso to construct its geometric
identification, proves the inverse is the zero section, proves comparison invertibility,
and invokes normalized-orientation uniqueness. For naturality it proves equality of the
frame zero sections, pastes the actual comparisons, applies both given normalizations,
uses the existing affine-frame equality detector and cancels the inverse isomorphism.

No other module is adapted. No source-library declaration is changed or removed.
