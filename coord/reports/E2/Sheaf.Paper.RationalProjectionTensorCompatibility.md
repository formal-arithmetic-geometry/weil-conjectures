## What changed

Proved the compact-support compatibility square for the same canonical tensor
comparison already used by the proper square. The proof normalizes the stage
coordinates, proves preservation of the open left-adjoint projection from the
unit equation, and pastes it with the proper counit mate and the two support
identifications. The factored-support calculation uses the specified composition,
proper-identity and open-identification comparisons. All categorical mate helpers are private and proved. The new module
`Sheaf.Paper.RationalProjectionTensorModels` proves the common normalization
calculation `WeilConjectures.rationalProjectionPullTensorSquare` for the proper
and open tensor-pullback squares.

The compact node's proof now records these calculations explicitly. Existing public
statements and definitions retain their signatures and meaning. The item publicly
imports the new tensor-model module, which now contains the unchanged named
`rationalProjectionTensorFunctorEq` and `rationalProjectionTensorComparison`.
This extraction follows local reducibility and proof improvements: the combined
file still took 86.6 seconds, over the 60-second limit. The calculation
uses only naturality, adjunction comparison equations and cancellation of the
specified isomorphisms; zero inputs, empty opens and identity proper maps require
no extra hypotheses.

Validation: `lcompile.py --all` accepted both delivery modules and all six
unchanged direct importers, with exit code 0: CommonProjectionProperTensorCompatibility,
ProjectionMateFactors, RationalProjectionComparisonEquations, CommonProjectionOpenFactor,
CommonProjectionProperFactor and CommonProjectionTensorCompatibility. The first of
these was updated upstream during the batch and its new version was rechecked
successfully. The final run compiled the two delivery modules in 56.4 and 56.6
seconds. All unchanged consumer copies were removed after checking. A verbatim
comparison verified all original public definition bodies and theorem signatures.
Both delivery modules have no holes, profiling options or lines over 100 characters.

## Proved and sorry left

Closed the one original hole:
`WeilConjectures.rationalProjectionTensorCompatibility_compactSupport`.
The already proved proper compatibility and the combined compatibility theorem
remain proved. Holes closed: 1 of 1. Holes added: 0. Actual holes remaining in the
item: 0. No split-off statements.

## No longer needed

None. No imports, nodes or modules are pruned. The proof uses the existing
operation-stage, constructible-projection-mate and canonical tensor-pullback
normalization dependencies. No source-library declarations are changed.

## Where the brief, the DAG or earlier work was wrong

None. The supplied plan is sufficient. The proof makes its open-unit transpose
and support-comparison pasting steps explicit in Lean.

## New nodes

`lem-sf-rational-pullback-tensor-localization-square` is fully proved in
`Sheaf.Paper.RationalProjectionTensorModels`. Its square depends only on the
supplied canonical integral/rational tensor-pullback normalizations and has no
properness or projection-formula hypothesis. It also owns the two moved shared
tensor-comparison declarations. No new hole is introduced. The existing three
item nodes now reference this normalization module.

Change record: `coord/changes/E2-rational-projection-tensor-models.md`.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
