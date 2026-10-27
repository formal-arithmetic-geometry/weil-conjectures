## What changed

Filled `WeilConjectures.IntegralSystemRealization.integralReductionPullFiniteSquare`
without changing its signature. The proof first proves the ordinary finite square from the
`OrdinaryLimitModel.projections` equation by transposing through the composite adjunctions.
It evaluates `RealizationModel.model` on flat-term K-flat complexes, uses the existing
completed quotient presentation and the derived evaluation normalization, and pastes the
resulting diagram. `Localization.natTrans_ext` extends this equality to all integral derived
objects.

The finite scalar cochain calculation is proved separately from the existing
`PurCompactSupport.scalarPull_complex_normalization`. Two proved normalization results
identify its scalar counits and ordinary adjunction presentations with the actual finite
scalar and intrinsic pullback presentations. The general adjunction transport calculation,
ordinary projection calculation, evaluation transport and scalar calculations have small
separate modules with their own nodes and explicit APIs.

Moved the existing `integralFiniteScalarPull` construction verbatim, with its public name,
signature, body and irreducibility unchanged, to `IntegralFiniteScalarPullCochainModel`.
The original module publicly re-exports it. This permits the lower cochain normalization to
refer to the construction without an import cycle. All other existing modules and all
source-library files are unchanged. The change record is
`coord/changes/J1-integral-finite-scalar-pull-cochain-model.md`.

Validation: all 13 delivery modules compiled individually in import order through
`lcompile.py --all`, each within 60 seconds. The unchanged direct consumers
`IntegralFinitePullbackNormalization` and `IntegralOpenScalarUnitSquare`, and the indirect
consumer `IntegralOpenFiniteEvaluation`, also compiled against the delivery. Their temporary
copies were removed. Profiling options were removed after the final cochain calculation
compiled in 18 seconds; the original theorem compiled in 17 seconds.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.IntegralSystemRealization.integralReductionPullFiniteSquare`: 1 of 1.
Added no holes. There are zero `sorry` declarations in this delivery, including the new
modules. This is a proof from the project's stated dependencies, not a decomposition into
new unproved statements.

The additional proved declarations are `ordinaryFiniteScalarPull_eq`,
`ordinaryFiniteScalarPull_transpose`,
`finiteScalarRestrictionDirect_sections`, `integralReductionPullOrdinarySquare`,
`integralReductionPullOrdinaryComplex`, `integralReductionPullEvaluationQuotient`,
`finiteScalarOrdinaryReductionIso_eq`, `finiteScalarOrdinaryReductionIso_unitComplex`,
`finiteScalarReductionCounitNormalization`,
`finiteScalarPullPresentation`, `finiteScalarPullComplexPresentation`,
`finiteScalarPullReductionComparison`, `finiteScalarPullPbcNormalization` and
`integralFiniteScalarPullCochainModel` in `WeilConjectures.IntegralSystemRealization`, and
`CategoryTheory.adjunctionSquareTransport`. The new definitions are actual adjunction or
degreewise constructions. No data is filled with `sorry`.

## No longer needed

No original import is removed. No existing node or module is withdrawn or globally pruned. The scalar and geometric
adjunction dependencies remain needed by the explicit normalization proofs. Every new
helper is used by the assigned theorem. The unit's route is preserved.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement defect was found. The scalar/pullback and quotient computation
comparisons required explicit normalization; existence of isomorphisms alone would not
identify the specified maps. The proof supplies these equalities from their adjunction-unit
normalizations. It imposes no constructibility, completeness, open-immersion or nonempty-
scheme assumption. Zero complexes and the exponent-one quotient (n=0) satisfy the same
unit/projection equations.

Profiling identified repeated unfolding of scalar and geometric presentations and
localization factors. Local unfolding control and APIs keep those constructions out of
subsequent categorical calculations; the self-contained ordinary, evaluation and scalar
arguments are separate modules. No shared definition was altered and no time limit was
raised.

## New nodes

`lem-sf-finite-scalar-pull-adjunction-transport` (`Sheaf.SixFunctors.FiniteScalarPullAdjunctionTransport`): Transport of a canonical adjunction square through presentations. The attached declarations are proved; no hole is split off.

`lem-sf-finite-scalar-pull-presentation` (`Sheaf.SixFunctors.FiniteScalarPullPresentation`): Equality of the two ordinary finite scalar pullback presentations. The attached declarations are proved; no hole is split off.

`lem-sf-finite-scalar-reduction-counit-normalization` (`Sheaf.SixFunctors.FiniteScalarReductionCounitNormalization`): Finite scalar presentation preserves the K-flat scalar counit. The attached declarations are proved; no hole is split off.

`lem-sf-finite-scalar-restriction-direct-sections` (`Sheaf.SixFunctors.FiniteScalarRestrictionDirectSections`): Section normalization of finite scalar restriction and direct image. The attached declarations are proved; no hole is split off.

`lem-sf-integral-finite-scalar-pull-cochain-model` (`Sheaf.SixFunctors.IntegralFiniteScalarPullCochainModel`): Cochain normalization of the canonical finite scalar and pullback square. The attached declarations are proved; no hole is split off.

`lem-sf-integral-finite-scalar-pull-ordinary` (`Sheaf.SixFunctors.IntegralFiniteScalarPullOrdinary`): Ordinary finite scalar and pullback comparison. The attached declarations are proved; no hole is split off.

`lem-sf-integral-reduction-pull-evaluation-quotient` (`Sheaf.SixFunctors.IntegralReductionPullEvaluationQuotient`): Transport of derived evaluation to the ordinary quotient model. The attached declarations are proved; no hole is split off.

`lem-sf-integral-reduction-pull-ordinary-square` (`Sheaf.SixFunctors.IntegralReductionPullOrdinarySquare`): Finite evaluation of the ordinary reduction and pullback mate. The attached declarations are proved; no hole is split off.

`lem-sf-finite-scalar-ordinary-reduction-iso` (`Sheaf.SixFunctors.FiniteScalarOrdinaryReductionIso`): ordinary scalar presentation by adjunction uniqueness and its proved cochain unit normalization. No hole is split off.

`lem-sf-finite-scalar-pull-complex-presentation` (`Sheaf.SixFunctors.FiniteScalarPullComplexPresentation`): The proved degreewise lift of the ordinary finite scalar presentation equation, separated to keep the cochain-model file within the per-file compile limit. No hole is split off.

`lem-sf-finite-scalar-pull-reduction-comparison` (`Sheaf.SixFunctors.FiniteScalarPullReductionComparison`): Finite scalar target comparison on a good complex. Its theorem is proved; no hole is split off.

`lem-sf-finite-scalar-pull-pbc-normalization` (`Sheaf.SixFunctors.FiniteScalarPullPbcNormalization`): Pbc scalar square on ordinary complexes. Its theorem is proved; no hole is split off.

## Related modules compiled before delivery

2 related module(s) compiled against this delivery by deliver3.py: 2 OK.

```json
{"capped": false, "direct": 2, "left_out": 0, "own": {"Sheaf.SixFunctors.FiniteScalarOrdinaryReductionIso": "566c1b31348c5d3e440c256e3667980c6ecea3bd", "Sheaf.SixFunctors.FiniteScalarPullAdjunctionTransport": "b0dc7eec2b0ed6fb7effc7c32693cf97746db850", "Sheaf.SixFunctors.FiniteScalarPullComplexPresentation": "b1fb5b21daba22ff90394c99cadd8d9c0c32dfdc", "Sheaf.SixFunctors.FiniteScalarPullPbcNormalization": "acfb45fe6e37d9e85f41a36ba0a1a5ca524a9f86", "Sheaf.SixFunctors.FiniteScalarPullPresentation": "5aaee8f578269f889b5d4827e3588502c348f976", "Sheaf.SixFunctors.FiniteScalarPullReductionComparison": "c4d3770db39e9be97bb4608d8b57df1f97591bf8", "Sheaf.SixFunctors.FiniteScalarReductionCounitNormalization": "b3920d01690328b3e7188077164ce433590346cd", "Sheaf.SixFunctors.FiniteScalarRestrictionDirectSections": "a2a80c26df46fbc6db681b1965bc89ce25dcb48c", "Sheaf.SixFunctors.IntegralFiniteScalarPullCochainModel": "9b8b57ec691664e47405ee1f17e3b116a0cc4488", "Sheaf.SixFunctors.IntegralFiniteScalarPullOrdinary": "b388f2f27a64145e6929893b54426d4effd7e56b", "Sheaf.SixFunctors.IntegralReductionPullEvaluationQuotient": "87b53355d628725de88516652134ba0b270d2d52", "Sheaf.SixFunctors.IntegralReductionPullFiniteSquare": "2f5be402f2b42300dddd79d61cf4ce34c49688a0", "Sheaf.SixFunctors.IntegralReductionPullOrdinarySquare": "3efb640435aeb3be402b1ea26b6e158b238b36bd"}, "results": {"Sheaf.SixFunctors.IntegralFinitePullbackNormalization": {"hash": "95ab216c4af6a14127da6d770a7036f564d5ac65", "status": "OK"}, "Sheaf.SixFunctors.IntegralOpenScalarUnitSquare": {"hash": "f4c93ad5a117b46f92d04aa41d4232c3f23ef079", "status": "OK"}}, "seconds": 81, "time": "2026-10-28T04:29:00+0800", "transitive": 0, "version": 1}
```

## Second reading by J1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
