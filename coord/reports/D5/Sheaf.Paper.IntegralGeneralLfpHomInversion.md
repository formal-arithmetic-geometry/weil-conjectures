## What changed

The assigned theorem retains its complete signature, public imports, and all fifteen
original data values. The ring alias is an ordinary definition with the same body,
and the coefficient map explicitly states its definitionally identical source type.
Canonical local instances share the existing constructions and reduce artifact size. Its proof uses the actual integral coefficient
inclusion and unit-normalized telescopes. Three fully proved separate results supply
coefficient transport, constructible-source continuity, and the generic Hom telescope
comparison. Full restriction identifies the resulting isomorphism with the specified
evaluation transpose. Scalar cancellation proves the leg formulas for all representatives;
evaluation naturality proves the pairing equation, including stage zero.

The assertions cover empty schemes, torsion constructible inputs, and representatives
with unbounded terms. Boundedness is used only to choose one strictly bounded-below
representative for the continuity comparison. No completed category is introduced.

## Proved and sorry left

The assigned declaration originally contains one hole:
`AlgebraicGeometry.ProEtale.IntegralHomInversion.integralGeneralLfpHomInversion`.
The replacement closes that hole. The complete packet compiled successfully,
including artifact serialization; development profiling has been removed. There are zero holes in
the four production source files. Holes closed: one; holes added: zero.
The proof-local cocone interface avoids reconstructing dependent colimit data, and
backward definition matching is restricted to the continuity transport. Holes added: zero. The supporting results
have passed the complete packet compile:

- `CategoryTheory.scalarTelescope_hom_comparison`.
- `CategoryTheory.scalarTelescope_normalized_comparison_isIso`.
- `AlgebraicGeometry.ProEtale.integralSectionScalarTelescope`.
- `AlgebraicGeometry.ProEtale.integralSectionHomContinuity`.

These are proved separate lemmas, not new proof obligations. The new canonical local
derived-category instances have fully constructed bodies.

## No longer needed

No module is withdrawn. The raw-localization route is replaced by direct transport
of the actual integral inclusion. The main proof does not apply
`scalarHom_telescope_evaluation`, `derived_scalar_localization_reflection`, or the
K-injective scalar-telescope theorem. The two elementary categorical representative-square and evaluation-naturality
calculations are proved locally. ScalarHomTelescopeEvaluation is not imported or used.

Removed direct private imports from the assigned module are
`Sheaf.Paper.IntegralLfpConstantModelComparison`,
`Sheaf.Paper.ConstructibleInternalHomContinuity`,
`Sheaf.Algebra.Homology.DerivedScalarLocalizationReflection`,
`Sheaf.CategoryTheory.ScalarLocalizationTelescopeCore`, and
`Sheaf.Algebra.Homology.KInjectiveHomScalarTelescope`.
The retained attempt's private import `Sheaf.Algebra.Homology.ScalarHomTelescopeEvaluation`
is also removed; its node is not a dependency of the new proof.
Continuity and coefficient infrastructure remain transitive dependencies where used.
The assigned node's previous direct dependency
`lem-sfb-integral-general-lfp-sequential-continuity` is replaced by the actual-coefficient
continuity transport. No source-library declaration is changed or removed, and no
transitive node is asserted globally unreachable. The assigned node remains required
by its unfinished DAG parents.

## Where the brief, the DAG or earlier work was wrong

The planned localization statements concern a sectionwise localization sheaf, whereas
the assigned theorem fixes the actual integral inclusion. An explicit adjunction and
coefficient transport is necessary. The finite intermediate field has universe zero;
the original general continuity statement uses a field in the scheme universe. The
continuity transport uses the lifted spectral coefficient isomorphism and exact
module equivalences, retaining the original coefficients and statement.

## New nodes

`lem-sfb-integral-section-scalar-telescope`: actual coefficient telescope on all
complexes, full derived restriction, and rational scalar invertibility.

`lem-sfb-integral-section-hom-continuity`: finite constant-model continuity transported
to general-lfp constructibility and the actual section coefficients.

`lem-sfb-scalar-telescope-hom-comparison`: generic Hom comparison from a unit-normalized
scalar telescope and continuity of its chosen complex model.

All three are proved with zero added holes. Each node records its source, complete
argument, declarations, searches, and dependencies. No dependency path returns to the
assigned node. Change record: `coord/changes/D5-integral-hom-inversion-proof-context.md`.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
