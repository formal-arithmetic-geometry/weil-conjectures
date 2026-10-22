## What changed

Changed `lean/Sheaf/Paper/PbcScalarExtension.lean` and the proof route of
`prop-weil-pbc-scalar-extension`. The conservative interface-scanner change record is
`coord/changes/M1-pbc-scalar-private-proof-scopes.md`. Public statements and definitions are unchanged.

The associator shift proof identifies the unit-normalized derived scalar adjunction,
transposes exact restriction composition, and detects the equation through the full
integral inclusion and rational localization. Completed pullback composition follows
by precomposition with the actual completion units and the ordinary composition law.
The operations shift proof descends the ordinary comparison from its normalized
counit equation on flat-term K-flat resolutions. Derived adjunction mates then
preserve shifts. The completion comparison preserves shifts by its unit equation
and the reflector's uniqueness property. All added helpers are private and proved.

Proof imports expose the normalized-unit argument in
`Sheaf.CategoryTheory.CanonicalRightDerivedAdjunctionShift`, the resolution adjunction
construction in `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`, and exact
levelwise derived shift comparisons. Chosen derived functors remain folded in the
proofs to avoid expensive definitional unfolding. The pullback shift argument is
proved for general coefficient data before specializing: this avoids checking its
large normalization equation with valuation-ring constructions expanded. The
completed composition argument similarly establishes the reflection calculation
for arbitrary coefficient data and comparison functors before specializing. A private
projection lemma shares exactness of rationalization between its two uses in the
existing rational scalar exactness proof.

Validation: the complete module compiled cleanly through `lcompile.py` in 44.8 seconds.

## Proved and sorry left

Closed 3 of the 11 original holes; added 0 holes; split off 0 statements:

- `AlgebraicGeometry.Scheme.pbcStageAssociatorShift`
- `AlgebraicGeometry.Scheme.pbcScalarOperations_shift`
- `AlgebraicGeometry.Scheme.pbcScalarCompletedPull_comp`

The following eight original holes remain, all attached to
`prop-weil-pbc-scalar-extension`:

- `AlgebraicGeometry.Scheme.pbcEmbeddingAmbientTensor_preserves`
- `AlgebraicGeometry.Scheme.pbcStageAssociator_laws`
- `AlgebraicGeometry.Scheme.pbcScalarDirectImageMap_isIso`
- `AlgebraicGeometry.Scheme.pbcScalarCompletionIso_exists`
- `AlgebraicGeometry.Scheme.pbcScalarCompletedExchange`
- `AlgebraicGeometry.Scheme.pbcScalarOperations_identity`
- `AlgebraicGeometry.Scheme.pbcScalarOrdinaryPull_comp`
- `AlgebraicGeometry.Scheme.pbcScalarOrdinaryPull_coefficients`

The completion composition proof uses the existing ordinary composition and scalar
completion declarations; their remaining holes are listed above.

## No longer needed

Removed the planned dependency `lem-pur-coefficient-associator-shifts` from this
node: the shift equation is proved directly for the specified ambient associator
and then descended. `Sheaf.Paper.RingedCoefficientAssociatorShifts` is not imported.
No library module is withdrawn; no source-library declaration is removed. The
blueprint unit route and the other pending proof dependencies are retained.

## Where the brief, the DAG or earlier work was wrong

No statement is disputed. The finite-free constructible transport package is stated
for unlifted valuation-ring coefficients, whereas this module uses `PbcIntegralRing`
and `pbcIntegralDatum`. Its application needs an explicit coefficient-model transport.
The general K-flat scalar-comparison package also needs adapters to the independent
site and coefficient universes used here. The delivered proofs retain the prescribed
maps; their descent arguments supply the independent-universe adapters needed for
shift compatibility.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
