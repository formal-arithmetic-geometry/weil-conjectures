## What changed

Filled `WeilConjectures.PurityFiniteSetting.finiteClopen_finite_restriction_identification`
in `Sheaf.Paper.FiniteClopenDerivedDecomposition`. The proof takes the normalized finite
localization comparison, transports coefficients along its inverse ring isomorphism,
and composes the exact-derived composition and natural-isomorphism comparisons with
the actual finite pullback comparison. The equivalence retains its specified
factorization on cochain complexes. No signature, definition, or import is changed.
The item node now records this proof route.

Added two proved private helpers, `additiveComp` and `pushforwardRestrictIso`,
for ordinary additive composition and module pushforward followed by scalar restriction.
Both finite and completed restriction identifications use them to avoid repeating
large concrete definitional comparisons. The existing `commonUnitCheck` proof now
seals `ScalarLocalization.category` and `ObjectProperty.FullSubcategory.category`
only while elaborating that declaration, respects transparency, and names its
comparison object and isomorphisms explicitly. No shared definition, exported
instance, or declaration attribute changes. The existing `clopenTensorModelIso`
and `finiteClopen_tensor_and_reduction` proofs also respect transparency; the latter
passes its proved counit `IsIso` witness explicitly. The profiling version of the full file
compiled in 49.9 seconds; profiling code has been removed for delivery.

## Proved and sorry left

Closed one of the two original holes:
`WeilConjectures.PurityFiniteSetting.finiteClopen_finite_restriction_identification`.

One original hole remains:
`WeilConjectures.PurityFiniteSetting.finiteClopen_constructible_equivalences`,
owned by `lem-pur-finite-clopen-derived-decomposition`.

Zero holes added, zero statements split off, and no holes in definitions or private
helpers. This is a partial proof delivery, not a claim that the constructible integral,
rational, or common-stage equivalences have been proved.

## No longer needed

The finite identification no longer needs
`lem-pur-ring-iso-derived-transport`, whose module is
`Sheaf.Algebra.Homology.NormalizedRingIsoDerivedTransport`. The ordinary scalar
restriction equivalence and exact-derived functor APIs suffice; the full coherent
symmetric monoidal transport package is unnecessary for this comparison.
Removed that direct planned dependency from the item's proof and `proof_deps`.
It was not imported by this module. No Lean import is removed and no module is
withdrawn. Dependencies of the outstanding constructible-equivalences hole are retained.
The ordinary tensor-transport module remains needed for the existing scalar and unit proofs.

## Where the brief, the DAG or earlier work was wrong

The planned `ClopenRoosIntegralDescent` dependency imports this item. Its lower-level
`AugmentedIntegralDescent` dependency also reaches this item through
`ClopenIntegralRestriction`; neither can be imported here without a cycle. This is
an outstanding issue for the remaining original hole, not a reason to discard that
argument or its dependencies. The cycle root is the import in
`ClopenIntegralRestriction`, which uses the shared site/ring/module restriction
definitions. Factoring those definitions into an independent module would make the
existing augmented membership theorem available without this cycle; no such shared
interface refactoring is included in this partial delivery. The finite restriction
identification itself needs no new interface: the existing finite localization comparison supplies the needed ring
isomorphism and derived comparison. Edge cases n=0 (positive exponent 1), empty
schemes, and an empty partition require no extra assumptions.

## Second reading by R7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
