## What changed

Proved `AlgebraicGeometry.ProEtaleWeilSheaf.underlyingStandardHomRepresentatives` in
`Sheaf.Algebra.Homology.UnderlyingStandardHomRepresentatives` without changing its statement
or either existing additivity instance. Added only private proof imports and proved private
helpers. The flat-separator and source-cone argument reuses the ordinary-module portion of
`Sheaf.WeilSheaf.NativeHomPrecompositionQuasiIso` inside this module, since those helpers
are private there. Target homotopies act with the native row sign `(-1)^p`.

The derived bifunctor is constructed by `Localization.lift` after the canonical functorial
K-injective target replacement. Its representative maps are inverse augmentation maps
composed with the localization factorization. Augmentation naturality proves the full
simultaneous naturality equation. The two quasi-isomorphism invariance arguments prove the
remaining representative field. No data are chosen from an unproved existence theorem. The original theorem assumptions are
retained; its unused-section-variable linter is disabled locally at that theorem only.

Validation: the complete module compiles through `lcompile.py` without warnings in 12.7 s.
The original theorem statement is textually identical; all lines are at most 100 columns.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtaleWeilSheaf.underlyingStandardHomRepresentatives`
(node `lem-sf-underlying-standard-hom-representatives`).
Added zero holes. No `sorry` remains in the delivered module. This is a proof, not a
further decomposition. All new private helpers are proved.

## No longer needed

None. The proof uses all five declared proof dependencies: sheaf flat resolutions,
inheritance by module objects, the signed source-cone comparison, the cone acyclicity
criterion, and the K-injective homotopy-equivalence criterion. No imports or declarations
are removed and no module is withdrawn. The blueprint unit route is retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The useful ordinary-module acyclicity and
precomposition argument already existed as private helpers in
`Sheaf.WeilSheaf.NativeHomPrecompositionQuasiIso`; it was not available as a public API.

## Second reading by A6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
