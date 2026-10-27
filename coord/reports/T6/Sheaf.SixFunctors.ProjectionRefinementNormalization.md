## What changed

Proved `WeilConjectures.ProjectionRefinementDescent.normalized_refinement_inverse`
without changing its signature. The only changed Lean file is the assigned module.
Its new proof-only import is `Sheaf.Paper.FiniteRefinementAmbientNormalization`.

The existing theorem
`WeilConjectures.CompactSupportFiniteProjection.refinementComparisonAtWitness_inv_eq`
already identifies the retained-origin inverse with the exact native finiteComparison.
The private `comparisonNat` packages that same native map as a natural transformation;
`comparisonNat_app` is reflexivity. The proved generic categorical lemma
`inverseIsoTransport` cancels the two witness transports using naturality and the
inverse-pair identity. `comparison_transport` combines those facts at a generic finite
coefficient ring. The final theorem specializes it to the specified coefficient
quotient. This keeps all large isomorphism data behind its existing interface.

LeanFinder searched for direct-image composition as the conjugate of inverse-image
composition; it returned generic sheaf comparisons. Loogle found conjugateIsoEquiv
and its hom/inverse equations. Project grep found the existing generic retained-origin
normalization, its private proof templates, and the native identityNormalize interface.
The existing normalization is used instead of duplicating those calculations.
The original unit route and all target statements are preserved. The complete
module compiled cleanly through lcompile.py in 12.8 seconds, with no warnings.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.ProjectionRefinementDescent.normalized_refinement_inverse`
(blueprint: `lem-sf-projection-refinement-normalization`).

Added zero holes and zero public declarations. No sorry remains in the delivered
module; every added private lemma is proved. This count concerns this module and
makes no claim to close the transitive holes of existing dependencies.

## No longer needed

No original public import is removed and no module or declaration is withdrawn.
The original plan's detailed site/compositor work is already supplied by the existing
`lem-sf-finite-refinement-ambient-normalization` theorem, which replaces its detailed
direct proof edges. In particular the following nodes are no longer direct proof
dependencies here, while their mathematical content remains inside the reused theorem:

- `lem-weil-pbc-proper-open-comparison-proetale`;
- `lem-cbc-proper-open-interchange-coherence`;
- `lem-cbc-finite-clopen-mate-site-transport`;
- `lem-weil-pbc-comparison-direct-image-canonical-mate`;
- `lem-pur-refinement-mate-plus-compatibility`.

Two original planned dependencies are unnecessary even as separate ingredients of
that normalization calculation: `lem-sf-proper-open-comparison-site-normalization`
(`Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization`) merely expands
the specified generic isomorphism; `lem-coef-finite-direct-image`
(`Sheaf.Paper.FiniteCoefficientDirectImage`) was only a pointer to a private
compositor calculation now supplied by the generic normalization theorem.
Neither module is imported directly by this proof. No claim is made that these
modules are globally unused by other consumers.

The restricted public purityWitnessedMateNormalization theorem is unnecessary;
its coefficient-setting and absolute separatedness assumptions are not introduced.

## Where the brief, the DAG or earlier work was wrong

The mathematical plan is correct, but its mate/compositor calculation duplicates
the generic retained-origin normalization already available under
`Sheaf.Paper.FiniteRefinementAmbientNormalization`. Reusing that theorem leaves only
the real additional step: transporting the canonical comparison along the retained
e while proving the necessary naturality cancellation. No statement was weakened,
no new geometric assumption was added, and no projection morphism was inverted.

## Second reading by T6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
