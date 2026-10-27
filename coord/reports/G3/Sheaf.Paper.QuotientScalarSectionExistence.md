## What changed

The target theorem now assembles a sectionwise cochain model from
`scalar_section_model_exists` and normalized ordinary and derived comparisons from
`scalar_section_comparisons_exists`. The target statement and all fixed data
signatures are unchanged. Two new proof modules and their DAG nodes were added:
`Sheaf.Paper.QuotientScalarSectionModelExistence` proves existence of the actual
`DerivedChangeOfRingsCochainModel`, while
`Sheaf.Paper.QuotientScalarSectionComparisonExistence` states the strictly smaller
fixed-model comparison step. The target retains its private
`IntegralResidueDerivedMonoidal` import because its local instance cache is needed
for elaboration.

## Proved and sorry left

The target declaration
`AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalar_section_exists` is
reduced to the two named substatements and its assembly proof is complete. The
new declaration
`scalar_section_model_exists` is proved using
`SheafOfModules.nonempty_derivedChangeOfRingsCochainModel`.

One sorry remains in
`AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalar_section_comparisons_exists`
(node `lem-sfb-quotient-scalar-section-comparison-existence`). It is the fixed
model comparison and normalization step, strictly simpler because the model is a
hypothesis. No definitions contain sorry.

## No longer needed

No mathematical dependency is withdrawn. The comparison module does not import
the earlier `InternalScalarNormalizationExistence` module because the split
statement is currently independent of an implementation import; its future proof
will add only the imports it actually uses. The target still needs
`IntegralResidueDerivedMonoidal` for the local cached instances.

## Where the brief, the DAG or earlier work was wrong

The original proof plan treated the `ScalarDerivedPair` interface as if it were
already a `DerivedChangeOfRingsCochainModel`. The former has a homotopy-category
counit and adjunction normalization, whereas the latter additionally requires the
cochain-level pointwise, triangulated, preservation, and computation fields. The
model existence and fixed-model comparison therefore have to be separate steps.

## New nodes

`lem-sfb-quotient-scalar-model-existence` records the proved existence of the
actual sectionwise cochain model and is realized by
`Sheaf.Paper.QuotientScalarSectionModelExistence`.

`lem-sfb-quotient-scalar-section-comparison-existence` records the remaining
fixed-model comparison and normalization step and is realized by
`Sheaf.Paper.QuotientScalarSectionComparisonExistence`.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
