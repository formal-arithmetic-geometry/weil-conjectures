## What changed

Filled `integral_section_projection_normalization` in
`Sheaf.SixFunctors.ProEtale.IntegralSectionProjectionNormalization` without changing
its statement. Added two proved private transport lemmas and private proof imports
of `IntegralNormalizedRestrictionSquares` and `DerivedNakayamaResolution` with
`import all` to reuse their private calculations. No other existing module changes.

The existing `integral_projection_back` supplies the normalized finite projection
for the specified comparison e. `finiteBack_ringIso` identifies its finite map with
the inverse of the supplied encoding f. The new private lemmas identify the supplied
source equality transport with the existing identity-on-functions topology
comparison. Cancelling the finite isomorphism and forgetting ring structure then
proves the desired equality.

LeanFinder and Loogle searches found generic sheaf extensionality but no matching
normalization theorem. The local library search found the reusable proved private
calculations. The first complete proof compiled in 11.7 seconds; final clean compile
and delivery probe results are recorded by the delivery tool.

## Proved and sorry left

Closed one hole:
`AlgebraicGeometry.ProEtale.IntegralPresentation.integral_section_projection_normalization`
(node `lem-pe-integral-section-projection-normalization`).

Added zero holes. No `sorry` remains in the delivered Lean file. The two private
helpers `topology_transport` and `source_transport` are proved. No split-off theorem
or new axiom is introduced.

## No longer needed

No public imports removed and no module withdrawn. The original direct proof
plan's invocation of `sfb_integral_coefficient_limit` is unnecessary: the supplied
`he` already gives all normalization witnesses needed by the proved
`integral_projection_back`. A new clopen-fibre/separation argument is unnecessary:
`finiteBack_ringIso` already proves finite-encoding compatibility. Accordingly,
`det-prop-sfb-qlbar-colimit-x-integral-limit`,
`lem-sf-finite-discrete-normalized-encoding` (its existence assertion), and
`lem-sfb-integers-coset-basis` are removed as direct proof dependencies of this node.
They remain dependencies of the existing comparison infrastructure where used;
this delivery does not claim to prune them globally. The finite encoding definition
and all statement dependencies are preserved. The unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The node's suggested proof omitted that its substantial finite-section calculation
has already been proved privately in `IntegralNormalizedRestrictionSquares`.
Reusing it avoids another decomposition. The endpoint transports require a genuine
topology-transport argument; they are not silently discarded.

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
