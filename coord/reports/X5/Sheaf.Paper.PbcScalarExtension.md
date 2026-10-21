## What changed

Change record: `coord/changes/X5-pbc-scalar-extension-proof-instances.md`.

In `Sheaf.Paper.PbcScalarExtension`, implemented the completed coefficient
structure square from naturality at every finite quotient and the limit universal
property. Added proved private helpers for the finite constant comparisons.

Implemented the direct-image composition and coefficient-tower equations from
the corresponding ordinary pullback equations using Mathlib's mates correspondence,
its pasting laws and compatibility with conjugation and whiskering. Moved each
ordinary pullback theorem before its direct-image consequence. Added the private
proof import `WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates`.
Implemented constant-section linearity of actual derived direct image and completed
pullback. The section formula follows by projecting to all finite quotients, then
passing to the adjunct coefficient map. The right-derived universal property detects
scalar endomorphisms; the K-injective model gives additivity. Adjunctions transfer
these properties to ordinary pullback and the completion reflector. All public
signatures, public imports, definitions and specified comparisons remain unchanged.
Implemented the unique rational scalar-extension Hom map by tensor balancing and
`existsUnique_semilinearHom`. Compatibility of the completed coefficient map with
constant sections gives semilinearity of exact restriction; localization and the
actual scalar adjunction give semilinearity of integral tensor. The canonical field
fraction maps identify the localized coefficient homomorphism. All new helpers are
private and proved. The full module compiled without warnings in 51.9 seconds
through `lcompile.py`.

## Proved and sorry left

Closed five of the original sixteen holes:

- `AlgebraicGeometry.Scheme.pbcScalarCoefficientStructureSquare`.
- `AlgebraicGeometry.Scheme.pbcRationalScalarHom_exists`.
- `AlgebraicGeometry.Scheme.pbcScalarDirectImage_comp`.
- `AlgebraicGeometry.Scheme.pbcScalarDirectImage_coefficients`.
- `AlgebraicGeometry.Scheme.pbcActualOperations_linear`.

No holes added and no split-off modules. Eleven original holes remain.
Validation: the full module compiled with no warnings in 51.9 seconds; the delivery
tool performs the server compile, axiom probes and preflight before pushing.

The eleven remaining holes, all attached to
`prop-weil-pbc-scalar-extension`, are:

- `AlgebraicGeometry.Scheme.pbcEmbeddingAmbientTensor_preserves`.
- `AlgebraicGeometry.Scheme.pbcStageAssociator_laws`.
- `AlgebraicGeometry.Scheme.pbcStageAssociatorShift`.
- `AlgebraicGeometry.Scheme.pbcScalarDirectImageMap_isIso`.
- `AlgebraicGeometry.Scheme.pbcScalarCompletionIso_exists`.
- `AlgebraicGeometry.Scheme.pbcScalarCompletedExchange`.
- `AlgebraicGeometry.Scheme.pbcScalarOperations_shift`.
- `AlgebraicGeometry.Scheme.pbcScalarOperations_identity`.
- `AlgebraicGeometry.Scheme.pbcScalarOrdinaryPull_comp`.
- `AlgebraicGeometry.Scheme.pbcScalarCompletedPull_comp`.
- `AlgebraicGeometry.Scheme.pbcScalarOrdinaryPull_coefficients`.

## No longer needed

None. No imports, declarations, modules or DAG dependencies are removed.
The direct-image coherence proofs use the existing pullback coherence equations;
the coefficient square uses finite quotient naturality as already planned.

## Where the brief, the DAG or earlier work was wrong

The finite-free constructible transport declaration uses unlifted valuation rings
and coefficient fields in `Type (u + 1)`, whereas this item uses `ULift` valuation
rings and fields in `Type u`. It does not apply by definitional equality; a
coefficient-presentation comparison is necessary. No statement was changed.

The compile service intermittently returned busy responses. Its newly enabled local
mode initially lacked a dependency artifact; the supported remote mode supplied
diagnostics. No tool was edited or bypassed.

## Second reading by X5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
