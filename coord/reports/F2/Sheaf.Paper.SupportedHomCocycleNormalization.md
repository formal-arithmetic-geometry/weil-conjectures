## What changed

Filled `AlgebraicGeometry.supportedHom_cocycle_normalization` in
`Sheaf.Paper.SupportedHomCocycleNormalization`, preserving all public signatures and
definitions. Private helpers construct evaluation from the two constant cokernel
presentations, compare its derived cohomology using the actual derived units, and
apply the existing RHom roof theorem. The cone clause follows from the degreewise
short exact support kernel sequence. Restriction is surjective on injective module
sheaves by the free-presheaf extension argument; forgetting coefficients is used
only as an exact functor, never asserted to preserve injectives.

The complete module compiled through `lcompile.py` in 46.4 seconds with profiling
enabled and no proof errors. Profiling options were then removed; delivery checks
the final clean packet. Generic private helpers keep the site adjunction and
derived comparisons abstract, and the final assembly constructs the cone proof
before packaging the normalization. All existing public signatures, definitions
and public imports are preserved. No other module was adapted.

## Proved and sorry left

Proved `AlgebraicGeometry.supportedHom_cocycle_normalization`
(node `lem-pur-supported-hom-cocycle-normalization`): 1 of 1 existing holes closed.
Actual holes left in the item: zero. Holes added: zero. Split off: zero.
Every private helper is proved. Existing imported theorem holes are used as
allowed stage-3 dependencies; no new statement or definition hole is introduced.

## No longer needed

The proof uses the roof-normalized RHom theorem directly, so the unnormalized
`Sheaf.Paper.SupportedCohomologyHom` proof import is unnecessary and was removed.
Its unnormalized existential comparison does not identify the cocycle map.

Removed unused proof imports:
`WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian`,
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`, and
`WeilConjectures.Algebra.Homology.KernelShiftedMappingCone`. Ordinary
`Sheaf J (ModuleCat A)` instances supply enough injectives; the existing ordinary
constant-sheaf pullback isomorphism supplies the constant comparison; the cone API
is already public in `Sheaf.AlgebraicGeometry.ClosedSupportHom`.

The proof does not require `lem-pur-ringed-site-grothendieck-abelian`,
`prop-weil-pbc-inverse-image-modules-exact`,
`lem-weil-pbc-extension-by-zero-exact`, or
`lem-weil-degreewise-epi-kernel-cocone-qis`. These four proof dependencies were
removed from this node and its proof steps. The last is replaced by the existing
`closedConeLift_quasiIso` API of `lem-amb-closed-support-hom`. The coefficient
finiteness dependency `def-weil-l-adic-coefficient-extension` is now explicit.
No module is withdrawn: the source library and other consumers retain their
existing declarations and imports.

## Where the brief, the DAG or earlier work was wrong

The cone clause is the explicit quasi-isomorphism of the support kernel into the
shifted restriction cone. Its proof only requires degreewise exactness; no proof
that open inverse image preserves injective resolutions is needed for this clause.
The unit route and all public mathematical statements are preserved.

## Second reading by F2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
