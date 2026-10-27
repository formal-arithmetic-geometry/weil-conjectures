## What changed

Replaced the proof hole in
`AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorIntegrationLocalTrace_exponentTransition`
by a composition of two smaller, ordinary-etale equations, preserving its signature,
public imports, coefficients, arbitrary Noetherian base and arbitrary normalized datum families.

The private `coefficient_square_core` proves the cancellation calculation for a natural
inverse-image comparison; `coefficient_square` expresses it in the three-comparison
form used by the actual chart. The private `compact_comparison_naturality` proves naturality
of the actual compact-support comparison by assembling its three bounded-below natural
isomorphisms. The private `paste_trace_square` composes the four resulting squares using only
functoriality and associativity. The main proof applies coefficient pullback compatibility
along the frame open, naturality of inverse-frame compact-support exchange, and the ordered affine
counit equation. New dependencies are private proof imports. No existing shared
interface, definition, consumer or target statement changes.

Validation: the launcher compiled both new statements and the completed main proof.
The profiled main file completed in 31.8 seconds, including the four proved helpers.
Development profiling and diagnostic markers were removed before delivery. The
delivery tool recompiles the clean files and performs the final preflight.

## Proved and sorry left

Original hole closed:
`AlgebraicGeometry.ProEtale.VectorIntegrationSite.vectorIntegrationLocalTrace_exponentTransition`
(node `lem-pur-vector-local-trace-exponent`). No sorry remains in the item module.
All four private helpers are proved.

Two holes added in new modules:

- `AlgebraicGeometry.ProEtale.VectorIntegrationSite.baseExponentComparison_pullback`
  in `Sheaf.Paper.OrderedTateExponentPullback`, node
  `lem-pur-ordered-tate-exponent-pullback`.
- `AlgebraicGeometry.ProEtale.VectorIntegrationSite.affineTraceCounit_exponentTransition`
  in `Sheaf.Paper.OrderedAffineTraceExponent`, node
  `lem-pur-ordered-affine-trace-exponent`.

This is a decomposition, not a completed proof or net hole reduction: one original
hole is replaced by two holes. The first new theorem concerns only coefficient
pullback, with no trace, support functor or bundle. The second concerns only the
ordered affine counit, with no bundle, frame, exchange prefix or global integration.
They are distinct steps of the original proof, not renamed copies of the item.
Their docstrings and nodes give full natural-language proofs and sources.
Edge cases checked in those arguments: zero tensor power and identity tower,
empty schemes, equal exponents and arbitrary finite ramified coefficient quotients.

## No longer needed

No existing import was removed and no module is withdrawn or claimed pruned.
The new modules each need only the public import of FiniteSiteCoordinates; redundant
direct imports of VectorBundleIntegrationCharts and AffineLinearTraceAction were
removed from those new files, since FiniteSiteCoordinates already exports their APIs.
The item no longer directly invokes `def-amb-p1-trace`,
`lem-amb-cartier-kummer-map`, `lem-amb-finite-tate-site-descent`, or
`lem-amb-affine-space-top-trace`: these are retained as dependencies of the new
ordered-affine or coefficient obligations, where their normalizations belong.
The two definitions `def-pur-finite-site-coordinates` and
`def-pur-vector-integration-adjunction-arrows`, and the local vector-integration
chart construction (`def-amb-vector-integration-charts`), remain in the parent proof
dependencies. The global `def-amb-vector-integration` is no longer a direct proof
dependency; its original statement dependency and public import are preserved.

The proof does not import `IntegrationExponentTransposeTransport` (it reaches this
item through its parent), the finite-type pro-etale affine transpose, a global
integration gluing theorem, or a site comparison of traces. None supplies the
arbitrary-Noetherian local ordinary equation directly. The unit route is preserved;
no unit realization is removed or bypassed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The declared affine-space theorem supplies
invertibility and base change at a fixed exponent; it does not state compatibility
between different annihilating exponents. Finite Tate descent supplies the normalized
root transition but not the displayed ordered derived pullback square. These missing
interfaces are now explicit, strictly smaller obligations. Compact-support comparison
naturality needed no additional hole.

The earlier finite-type affine transpose equation cannot specialize to arbitrary
Noetherian bases. The larger IntegrationExponentTransposeTransport theorem cannot be
used as a shortcut because it imports the parent VectorIntegrationSiteComparison.

## New nodes

`lem-pur-ordered-tate-exponent-pullback` records the coefficient-only square under any
scheme pullback. Its proof is normalized root-power naturality on pure generators,
followed by the exact derived embedding, shift and ordered tensor induction.

`lem-pur-ordered-affine-trace-exponent` records the ordinary ordered affine counit
square. Its proof is Kummer-boundary naturality on the projective-line decomposition,
restriction by the open counit and induction along the specified adjunction tower.

The parent node's proof, proof dependencies and proof origin follow the actual Lean
composition. No change record is required: existing interfaces are unchanged.

## Second reading by T1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
