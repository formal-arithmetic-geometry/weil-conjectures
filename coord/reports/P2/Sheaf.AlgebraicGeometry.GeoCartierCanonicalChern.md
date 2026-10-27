## What changed

Filled geoCartierCanonicalClass_chern using the ordinary canonical boundary class.
The ordinary Chern witness is its Yoneda precomposition with supportedConstantUnit.
Proved private helpers establish both constant-section formulas, the unit square
for the actual geoCartierSourceComparison, and generic Ext transport. The final
equation follows from
geoCartierCanonicalClass_comparison and exact-functor compatibility of Ext composition.

Added only proof imports of SupportedDerivedUnitForget (including its proved private
coefficient_unit helper), SupportedKummerChernRealization,
FinitePushforward.ConstantUnit and Comparison.LowerStarCoherence. Updated the item's
DAG proof and proof dependencies to match this argument. Local irreducibility
attributes keep the comparison inverse image and Ext operations
behind their proved APIs. A recursion-depth option scoped to the unit-square
helper permits checking its explicit constant-section conversion; no time or
heartbeat limit is raised. Existing signatures, definitions and public imports
are preserved.

## Proved and sorry left

Closed: AlgebraicGeometry.ProEtale.geoCartierCanonicalClass_chern
(lem-sfb-geo-cartier-canonical-chern), the item's one original hole.
No split-off statements; no new holes. No sorry remains in the delivered module.
Validation: lcompile.py compiled the final module without warnings in 45.1 seconds
(result 1058904f03098abc757b6ad4), below the 60-second limit. The public theorem
signature is unchanged; the node changes only proof, proof_deps and proof_origin.

## No longer needed

No existing imports were removed. The proof does not need direct use of
lem-asd-ordinary-supported-kummer (OrdinarySupportedCartierKummer): its existence and
uniqueness are already encapsulated by geoCartierEtaleClass and its specification.
It does not need the derived-map interfaces def-asd-ordinary-supported-kummer-system,
lemma-weil-pbc-finite-direct-image-exact (SixFunctors.Finite.Exact), or
sk-thm-pe-direct-image-comparison (ProEtaleDirectImageComparison) for the planned
ordinary-derived-to-Ext and bounded-below comparison detour. Their roles in this
proof are replaced by ordinary Chern realization and the underived mate unit identity.
These declarations and modules remain available and may still be needed transitively
or by other consumers; no module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement error found. The original plan's derived comparison detour is
unnecessary: both the canonical class and the required Chern equation are already
expressed in Ext, so the unit compatibility can be proved at the sheaf level.
The unit's construction-and-comparison route is preserved, including its specified
mate, constant comparisons, positive boundary, and integral normalization.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
