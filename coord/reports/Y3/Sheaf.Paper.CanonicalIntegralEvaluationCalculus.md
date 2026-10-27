## What changed

Replaced the existence theorem's sorry by an explicit change of presentations and
assembly. The existing theorem signature and its two public imports are unchanged.
No existing module other than the assigned item is changed.

Added CanonicalCoefficientReduction: the new integral closed field is literally
IntegralOnSlice.duality.closed; the sequence and finite closed fields are fixed
normalized duality structures. Tensor-model comparisons are transported by the
canonical adjoint comparisons, with their uncurry equations proved using the same
ordinary chain maps. The reduction, adjunction, finite evaluations, strict models,
quotient adjunctions and all non-tensor data are retained. Tensor comparisons are
conjugated by mapped inverse source comparison and target comparison.

The generic baseChange_eq, enriched_eq, transpose_eq, evaluation_eq,
fiberEvaluation, tensorSquare and evaluation_transport are proved. Added
CanonicalCoefficientRepresentativeLaws, proving all five representative laws by
these calculations. In the item, the fiber calculus, quotient calculus, global
calculus and resolution coherence are concrete records. Fiber transitions and
beta evaluation follow from baseChange_eq. Gamma is the same actual morphism by
enriched_eq, so its projection, naturality and H-zero equations transfer. Mapping
composition is proved directly by adjunction and tensor-comparison naturality.

Validation: lcompile --all compiled all four modules in import order. The final
representative proof also compiled alone without warnings in 54.0 seconds after
profiling and removing unnecessary equality casts. Profiling options were removed.
The original theorem signature was compared verbatim with the shared source.

The sole residual step is isolated in CanonicalCoefficientCompositionLaws:
internal composition for normalized reduction and finite scalar extension. This
asserts only two families of morphism equations, with all functors and comparisons
already constructed. It asserts no existence, no fiber calculus and no global
coherence, so it is strictly smaller than the assigned existence theorem.

## Proved and sorry left

Original hole removed: WeilConjectures.canonicalIntegralEvaluationCalculus
(lem-pur-canonical-integral-evaluation-calculus). Its assembly proof is complete.

New hole: WeilConjectures.CanonicalCoefficient.compositionLaws
(lem-pur-canonical-coefficient-composition-laws), the only sorry in the delivery.
Its source and complete representative argument are in its docstring and node.

WeilConjectures.CanonicalCoefficient.representativeLaws and every definition and
helper in CanonicalCoefficientReduction are proved, without new holes.

This is a decomposition: one original hole removed, one strictly smaller hole
added, one hole remaining, net zero. It is not reported as a fully closed proof.
The input coherent-calculus existence theorem retains its existing dependencies.

Edge cases: the conjugation and cancellation arguments use arbitrary objects,
including zero objects, and include identity finite quotients. No nonempty-site,
boundedness, perfectness, quotient-flatness or invertibility of l is added.
Independent scheme and coefficient universes are retained throughout.

## No longer needed

No imports or modules are withdrawn. No mathematical dependency of the original
route is pruned: adjoint comparison, the existing coherent calculus and normalized
duality are all still used. Duality now enters through the explicit reduction data
and the internal-composition lemma rather than directly in the final assembly.
No source-library declaration is changed or removed.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The representative part of the plan can be made
shorter: use the old tensor-model comparison followed by the adjoint comparison
as the new model. Its ordinary uncurrying follows directly from the proved
comparison_transpose theorem. This avoids needing equality with a second chosen
representative comparison for any of the five representative laws. Comparing the
normalized associators remains necessary for the internal-composition step; no
monoidality of an arbitrary adjoint comparison is asserted.

The ancestry helper does not resolve this module-created item's ancestor, but its
current node explicitly records lem-fix-operation-reduction. The new nodes retain
that ancestor and the current node's entire intermediate ancestry. Blueprint
searches for internal composition and tensor presentation found no matching node.
The unit's realized route is unchanged.

## New nodes

- def-pur-canonical-coefficient-reduction: explicit data and proved transport
  identities; module Sheaf.Paper.CanonicalCoefficientReduction.
- lem-pur-canonical-coefficient-representative-laws: all five representative
  normalization equations, proved; module Sheaf.Paper.CanonicalCoefficientRepresentativeLaws.
- lem-pur-canonical-coefficient-composition-laws: the residual pair of internal
  composition families; module Sheaf.Paper.CanonicalCoefficientCompositionLaws.

The assigned node's proof, proof dependencies and proof origin now describe the
actual construction and assembly. No existing signature or definition is changed,
so no change record or consumer adaptation is required.

## Related modules compiled before delivery

64 related module(s) compiled against this delivery by deliver3.py: 61 OK, 3 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CanonicalCoefficientCompositionLaws": "a807cf6d8676c999173630594e58a20161cd9642", "Sheaf.Paper.CanonicalCoefficientReduction": "08cdeb44a63c799a62ca76e3cbcc94e8f631f478", "Sheaf.Paper.CanonicalCoefficientRepresentativeLaws": "a921fa32bddbb2362119f4d9db8afcb7269f1afb", "Sheaf.Paper.CanonicalIntegralEvaluationCalculus": "66920860fe2ab011996045c5dd43f7e9e3d521af"}, "results": {"Sheaf.Paper.AdicPurityScalarNaturalityData": {"hash": "28cc25b50afc3cb7b673c86c4f6d7336fa5e2b86", "status": "SLOW"}, "Sheaf.Paper.AdicUnitTraceReductionData": {"hash": "6fde2b47349c9ae9165093fb269a39ccfaf9ce1b", "status": "OK"}, "Sheaf.Paper.AdicUnitTraceScalarData": {"hash": "b9e2298d743b1e198d897f0ed6561d94c9c10346", "status": "OK"}, "Sheaf.Paper.CanonicalIntegralCompletionModels": {"hash": "161fa9ab5f8e7c01684290b480307f3004f953df", "status": "OK"}, "Sheaf.Paper.CoefficientGammaRepresentatives": {"hash": "f6dc488b023505d4045ebd97e3ceedda8581ae3f", "status": "OK"}, "Sheaf.Paper.CompactSupportProjectionFormula": {"hash": "9d8a08bf4a6d4025a7ffc9ce8b51e70bcc8ad44a", "status": "OK"}, "Sheaf.Paper.CompactSupportProjectionIntegralStages": {"hash": "9e7579cfe54e6968fbb0134e039a5f62d67399ca", "status": "OK"}, "Sheaf.Paper.CompactSupportRealizationCoordinates": {"hash": "fccef3e9fbd21b120d003aed7419ff8000e7be40", "status": "OK"}, "Sheaf.Paper.CompactSupportRealizationFactorNormalization": {"hash": "21a1fae00a5f5e376cdaca1227b75267f4c85edf", "status": "OK"}, "Sheaf.Paper.CompactSupportRealizationFactorization": {"hash": "f227ba1ecb344881322e4822cdd8a9f7bad73a67", "status": "OK"}, "Sheaf.Paper.CompletedOpenTensorContext": {"hash": "bdee846c2311982b9557a4fb3d834467074d6f93", "status": "OK"}, "Sheaf.Paper.CompletedOpenTensorRepresentatives": {"hash": "0e9b68cc2104d02715a6f702d027d56c076d6bfd", "status": "OK"}, "Sheaf.Paper.CompletedOpenTensorSystemRealization": {"hash": "3369aa5fe8939ab3c88d972c46df5f148aa11695", "status": "OK"}, "Sheaf.Paper.CondensedCompositorRealization": {"hash": "bf5692789db5a0ae189806d117c0b44ae7f79cfc", "status": "OK"}, "Sheaf.Paper.CondensedOpenCounitRealizationSupport": {"hash": "111fd16030a7b4501af4c65bee2afe0e37d3ee76", "status": "OK"}, "Sheaf.Paper.CondensedOpenCounitUnits": {"hash": "f6992093322faef0c8d2cc2c308093e13e78eae6", "status": "OK"}, "Sheaf.Paper.ConstantExtensionCompactComparison": {"hash": "8b1c3f304f9d2320ba5b0ead9c57f6779050da10", "status": "OK"}, "Sheaf.Paper.ExceptionalRefinementSystemData": {"hash": "534c11b90226f10051386950b19942fc294f4bf3", "status": "OK"}, "Sheaf.Paper.FieldWeilShriekShiftData": {"hash": "5c0b9354c99c9e73728a547bd4397bc11046c209", "status": "SLOW"}, "Sheaf.Paper.IntegralOrientedExchangeSquares": {"hash": "07b26e0002ab4b2de16e89bac7a69e976dce1fbf", "status": "OK"}, "Sheaf.Paper.IntegralProjectionFiniteEvaluation": {"hash": "e2d9151a80a1b1f7db95a6e2203057ac2e64654e", "status": "OK"}, "Sheaf.Paper.IntegralProjectionOpenFactorReduction": {"hash": "b1654c04e191f080c07732aed7c0a21befbd7b94", "status": "OK"}, "Sheaf.Paper.IntegralProjectionProperFactorReduction": {"hash": "487f1e6841880fb5493d9970148c3774910fe64f", "status": "OK"}, "Sheaf.Paper.IntegralProjectionReductionCoordinates": {"hash": "a2c07e3fb16ff1606eef14bbcc3f4d413059d45f", "status": "OK"}, "Sheaf.Paper.IntegralProjectionReductionNormalization": {"hash": "01a313e723dc37d204e0d061350584dda1cb77db", "status": "OK"}, "Sheaf.Paper.IntegralProjectionRefinementSquare": {"hash": "9f27d74be83f587cd4a1f0d2e96faf18e32b1e62", "status": "OK"}, "Sheaf.Paper.IntegralProjectionSupportEvaluation": {"hash": "cf72394a541725fec605eb0a29d8bb1f5398807d", "status": "OK"}, "Sheaf.Paper.IntegralProjectionSupportFactorCoordinates": {"hash": "c155141d262d956b48c94dedf4453c261d9a4bbf", "status": "OK"}, "Sheaf.Paper.IntegralProjectionSystemCoordinates": {"hash": "53ea01ccf46f20dd2a3004cb3af5fab60b50cc45", "status": "OK"}, "Sheaf.Paper.IntegralProperProjectionSystemNormalization": {"hash": "0ee48bbd159d7c08af8c60ee8e508d4fb85cb4e6", "status": "OK"}, "Sheaf.Paper.IntegralProperSupportReductionIdentity": {"hash": "dfc2389156a39b58cd8fdf18bd39981aecfb645c", "status": "OK"}, "Sheaf.Paper.IntegralPurityComparisonCocycles": {"hash": "f88677315b5409399d6a6c40be1c5c5844bfc678", "status": "OK"}, "Sheaf.Paper.IntegralPurityCounitReduction": {"hash": "fd3df8be2f2fe5b901eefcdcc20aa0d5b1dcf113", "status": "OK"}, "Sheaf.Paper.IntegralStageProjectionStructuralIdentities": {"hash": "58abf982f904539e76e6550c8485bc13471a5000", "status": "OK"}, "Sheaf.Paper.IntegralSupportAdjunctFiniteCoordinates": {"hash": "29822a6085d1fa21a3549b52b76ca7fd3ae0f847", "status": "OK"}, "Sheaf.Paper.IntegralSupportReductionNormalization": {"hash": "13c2c8849d429ec6a339d763cfb51f2bff6d4219", "status": "OK"}, "Sheaf.Paper.NormalizedIntegralPurityTrace": {"hash": "f4fb93ec1e6587a42edde62a87ff1896a1bb9bbe", "status": "OK"}, "Sheaf.Paper.NormalizedOrientationPerfectDuality": {"hash": "145740e6c5f67bc36ee7e1685fb1db5db7f77808", "status": "OK"}, "Sheaf.Paper.PurAdicReconstruction": {"hash": "f90b8f54db10effd1056122ba735a09dd63b6742", "status": "OK"}, "Sheaf.Paper.ReducedFrontierMixedGluing": {"hash": "5d5726d9f6bc615a22ac7b099f937058d9d9cf1f", "status": "OK"}, "Sheaf.Paper.SfCoefficientComparisonConclusions": {"hash": "a6ffb793d5941b2a35b6a2e6ad8f462561e43db2", "status": "OK"}, "Sheaf.Paper.SfRecollementReductionBoundary": {"hash": "3e5eb049e528ed51a96a3b71024b90d9c96825a0", "status": "OK"}, "Sheaf.Paper.TowerPurityRealizedData": {"hash": "48a3c43647f30e5b85d3ad06b7ebe334a902b04d", "status": "OK"}, "Sheaf.Paper.TowerPurityRealizedTranspose": {"hash": "1d0ec451ad5c56d58109e9070c4aa4514bd9a180", "status": "OK"}, "Sheaf.Paper.TwistedPullbackPbcCoordinates": {"hash": "21e9472dd858fb3e540d2489b119029ef3f515a4", "status": "OK"}, "Sheaf.SixFunctors.BasicRealizationShiftSquare": {"hash": "b01887d79c079b894b02c66acc70253ac55c7e01", "status": "OK"}, "Sheaf.SixFunctors.CanonicalTreeGeneratorShiftLaws": {"hash": "6ffd81dc38c177743891cf2395408af03b41579a", "status": "OK"}, "Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel": {"hash": "b70d2eb996233ffa48c3fa8d8d0428ea8a4b852f", "status": "OK"}, "Sheaf.SixFunctors.CompletedShriekCompositionLaws": {"hash": "a47b2735a4bdbf6d4e335cab6c7a4294f5d436a8", "status": "SLOW"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstructionEquivalence": {"hash": "ba3c7868a918eff9ff9e82173364432b81326775", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces": {"hash": "dfd7491b122f1402fa3e5e5f1ca4f2b05228ee34", "status": "OK"}, "Sheaf.SixFunctors.IntegralBasicOperationShift": {"hash": "22d03673a4ad2a1f40c1f79ecfb325b0be8aaa8e", "status": "OK"}, "Sheaf.SixFunctors.IntegralNormalizedRefinementPasting": {"hash": "b32deb85da648bb9c49ab07dff91712c562e556b", "status": "OK"}, "Sheaf.SixFunctors.IntegralOperationShiftData": {"hash": "d79d356f094f2fb511f9e0bde2182c3cf96581b4", "status": "OK"}, "Sheaf.SixFunctors.IntegralRefinementDiagramAdmissibility": {"hash": "c9ca590006ea33446458683baec90833ab6151b1", "status": "OK"}, "Sheaf.SixFunctors.IntegralRefinementTransposeRealization": {"hash": "b35036476a2b46cc15de73d5260a43370ddb5f9b", "status": "OK"}, "Sheaf.SixFunctors.OpenClosedWeilMateData": {"hash": "9630df99472a0f41c00bc0768460c09c74bc07ae", "status": "OK"}, "Sheaf.SixFunctors.OpenFactorOpenRealization": {"hash": "b0df9d461069cdec99e0f95bd996476c034fee1b", "status": "OK"}, "Sheaf.SixFunctors.OpenSupportStepBounds": {"hash": "faf44abccb6817201ba60377e6883eb48767ad73", "status": "OK"}, "Sheaf.SixFunctors.OpenTensorQuotientCochains": {"hash": "87ce5d0d62cc2097a2fb8d472226a6c55794d836", "status": "OK"}, "Sheaf.SixFunctors.OpenTensorQuotientGeometry": {"hash": "d54cdc02726063dde89125f9cc7b7c23fe42f86f", "status": "OK"}, "Sheaf.SixFunctors.RealizationAdjunctionInsertionShift": {"hash": "3cbcb65099ba8182423fd6a586d7a131dd326c67", "status": "OK"}, "Sheaf.SixFunctors.RealizationTreeShiftData": {"hash": "760e8646e65c3220770da4273fc1aa5512d19a9b", "status": "OK"}, "Sheaf.SixFunctors.SystemAdjunctionOpenMapShift": {"hash": "60941c6454e1508420d9a4118840b612aa10b28f", "status": "OK"}}, "seconds": 390, "time": "2026-10-28T04:20:47+0800", "transitive": 63, "version": 1}
```

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
