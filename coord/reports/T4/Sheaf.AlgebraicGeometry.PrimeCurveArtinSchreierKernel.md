## What changed

Proved `AlgebraicGeometry.Etale.exists_prime_curve_artinSchreier_kernel` in
`Sheaf.AlgebraicGeometry.PrimeCurveArtinSchreierKernel`, preserving its complete statement.
No adopted source-library file or other module is changed. The public-import pruning and
proof-local commands are documented in
`coord/changes/T4-prime-curve-artin-schreier-proof-interface.md`.
The downstream check lists zero current consumers. The quarantined intended parent
independently imports the removed Frobenius dependency and requires no adaptation.

Construct the Artin--Schreier maps directly on the additive structure sheaf using its canonical
lifted-function coordinates. Exactness on the base and the specified degree-zero structure
comparison show that the direct image of the difference map is epic. The universal right-derived
delta functor identifies the first direct image of constant prime coefficients with the kernel
of the first image of that difference map. The natural single-complex comparison transports this
to bounded-below derived homology.

Conjugate the induced Frobenius by the structure theorem's specified isomorphism. On restricted
cohomology, functoriality transports the sectionwise Frobenius/scalar identity. Reuse the canonical
cocycle map, its resolution-class formula, and the proved coefficient identities from
`RawRestrictedClassNormalization`. Surjectivity of the specified raw evaluation comparison
transports the structure theorem's scalar normalization to restricted cohomology. The resulting
equation on raw classes extends to all sections by local surjectivity and sheaf separation.
Finally, exact coefficient forgetting and the constant-sheaf comparison identify the required
module-valued left term. Empty bases and nonreduced characteristic-p bases require no extra
hypotheses.

All auxiliary lemmas are private and proved. Private structures package the actual associated
sheaf and scalar endomorphisms, and the actual raw classes, evaluation comparison, and canonical
cocycle map with their proved laws. These definitions explicitly construct the packages from the
specified maps; they choose no unspecified coefficient object or comparison. The generic
semilinearity argument uses their laws without repeatedly unfolding tensor-pullback and derived
cohomology constructions. Generic pointwise square and conjugation lemmas serve the same purpose
for section calculations. The remaining auxiliary definitions name the actual first abelian
higher-image functor and its scalar-linearity condition. The module/abelian comparison is the
composite of the canonical derived coefficient-forgetting isomorphisms.

Validation: the complete revised proof compiled on the project server in 44.7 seconds, with no
warnings and zero local holes. The final formatting and redundant-import cleanup are checked
again by `deliver3.py`, including its axiom and hole probe.
The DAG's proof, proof dependencies, and proof origin now describe this argument.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.exists_prime_curve_artinSchreier_kernel`
(node `lem-weil-pbc-prime-curve-artin-schreier-kernel`).

Added holes: none. Remaining holes in the delivered module: none. Split-off statements: none.
No new public declarations or modules are added. Existing declared dependencies are used as
supplied; their proofs are not changed by this packet.

## No longer needed

Removed the public import `Sheaf.AlgebraicGeometry.FrobeniusVectorBundleKernel`, replacing the
statement's finite-locally-free API dependency with
`WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree`. Removed
`lem-weil-pbc-frobenius-vector-bundle-kernel` from this item's proof dependencies: base
Artin--Schreier exactness supplies the needed epimorphy directly. This prunes this item's
reference only. The Frobenius kernel module remains needed by other parents, including the
quarantined prime-coefficient curve parent, and is not withdrawn.

The earlier tensor-unit coordinate transport and duplicate coefficient-naturality proofs are
unnecessary. The section-data module remains imported for its proved section-map constructor.
The separate class-compatibility proof import is redundant because the normalization-data
interface already publicly supplies the class API. The higher-image-presheaf and
class-compatibility nodes remain needed through the canonical normalization construction.
No other original declared dependency is discarded, no module is deleted, and no unit route is
bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned rank-one Frobenius vector-bundle argument is unnecessary for epimorphy of the
degree-zero difference map. The already stated Artin--Schreier exactness theorem on the base
gives it directly. The earlier tensor-unit coordinate transport was also redundant: the existing
section-map constructor accepts the additive structure sheaf itself.

The specified raw evaluation and canonical cocycle maps must be used with their actual
coefficient naturality. An arbitrary isomorphism of higher-image sheaves would not establish the
scalar clause. The existing normalization and resolution-class statements provide exactly these
comparisons. No statement or existing definition needed repair.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
