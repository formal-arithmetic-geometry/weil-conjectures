## What changed

Repaired `completed_formula_chain_data` in
`Sheaf.Paper.IsomorphismScalarCompletedFormulaChainData`: it now supplies the
actual natural tensor isomorphism on sheaves, with its pure-tensor normalization.
The proof compares completed coefficient maps after all finite projections,
constructs the identity restriction square, uses normalized ordinary scalar
adjunctions and the generic invertible adjunction-square map, and extends its
unit-tensor rule by linearity. All helpers are proved and private.

Adapted the sole caller `Sheaf.Paper.IsomorphismScalarCompletedModelFormula`
without changing its theorem statement or visibility. `NatIso.mapHomologicalComplex`
applies the comparison degreewise; whiskering restricts it to good complexes.
The component formula is then exactly `CompletedFormula`.

Change record: `coord/changes/N4-completed-scalar-chain-model-repair.md`.
The final three-file bundle passes lcompile.py in import order: item 34.7 s,
adapted parent 6.2 s, unchanged direct consumer
`Sheaf.Paper.IsomorphismScalarCompletedModel` 2.6 s. The temporary unchanged
consumer copy was removed after validation. No profiler or printing diagnostics
remain in the delivered sources.

## Proved and sorry left

The repaired `AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.completed_formula_chain_data`
is fully proved, with zero sorry left and zero sorry added. The former hole is
removed by a statement repair; it is not counted as a proof of the former HEq
statement. No existing holed declaration is proved with an unchanged statement.
No statement is split off. The unchanged `scalar_completed_formula` statement
has a complete proof from the proved sheaf comparison, with no cone-normalization
hole in its new route.

`completed_formula_chain_normalization` remains untouched in its separately
claimed module; its hole is pruned from this proof route. No sorry remains in
the delivered Lean files.

## No longer needed

Removed the item's public import `Sheaf.Paper.ScalarPullbackStrictConeData` and
private import `Sheaf.Paper.ScalarPullbackStrictConeNaturality`. Their strict
Roos data and naturality theorem are unnecessary for ordinary tensor transport;
`lem-weil-scalar-pullback-strict-cone-naturality` is removed from the item's proof
dependencies. Those modules remain needed by other library consumers, so this
delivery does not withdraw them.

Removed the parent's private import
`Sheaf.Paper.IsomorphismScalarCompletedFormulaChainNormalization` and its node
`lem-weil-isomorphism-scalar-completed-formula-chain-normalization` from the
parent's proof dependencies. The parent obtains its section formula directly
from the module comparison, so the old HEq normalization is unnecessary.
The module held by P1 is not edited or withdrawn. No other DAG node is pruned by
this argument. There are no new nodes or new sorry statements.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the former chain-data statement identifies maps on different
complexes. Its top-level node even used ordinary equality between these maps;
the Lean attachment replaced this with HEq without providing endpoint equality.
Identity scheme/scalar maps and a nonzero free module in degree zero already
exhibit the issue: a strict Roos complex also has a shifted product term, while
the original complex does not. The augmentation has zero shifted coordinate;
it is a comparison after localization under completeness conditions, not an
identity of chain models. The good subcategory does not impose completeness.
Strict cone naturality only gives strict/derived cone data, not the asserted HEq.

The mathematical comparison needed by the parent is instead the ordinary
sheafified tensor comparison of Stacks Tag 03EL, applied degreewise. The corrected
node records this, its old statement and proof, and its sole citer audit. The
parent's statement is unchanged. No unit realized statement or step names these
split nodes, and the enclosing unit route stays intact.

Searches through msearch.py (leanfinder, loogle and grep), plus the source tree,
found the proved general adjunction-square construction and normalized scalar
adjunction used here. The existing specialized ordinary-model comparison in
IsomorphismComparisonScalarExtension cannot be imported: it lies above this
module in the import graph and its equal-universe wrapper is insufficient here.
The proof uses independent site and coefficient universes throughout.

## Related modules compiled before delivery

52 related module(s) compiled against this delivery by deliver3.py: 16 INFRA, 32 OK, 4 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.IsomorphismScalarCompletedFormulaChainData": "d671fb93d49e1cd28ef8c129313db78ccacc401a", "Sheaf.Paper.IsomorphismScalarCompletedModelFormula": "f4d0506033205bc6ef83d9dcd0579db376bbdef5"}, "results": {"Sheaf.Paper.AdicCochainTensorReindexing": {"hash": "929e392d42d9e228219d2baa11a5bec9188da8ce", "status": "SLOW"}, "Sheaf.Paper.AdicIntegralReindexingMaps": {"hash": "f06cc5ab2e20c505b0fc9e143747c97d5d60bcd5", "status": "SLOW"}, "Sheaf.Paper.DerivedAutomorphismHomEvaluationContinuationB": {"hash": "26f1682872233b77da7f63ae8496a94cdfdecb31", "status": "OK"}, "Sheaf.Paper.FieldWeilShriekShiftData": {"hash": "8339b4e3e8b675fccaec54fc404987de96ebcd23", "status": "SLOW"}, "Sheaf.Paper.FiniteRestrictionDiagramNaturality": {"hash": "81365072e344a50c7cddc314c30b496374b0359e", "status": "INFRA"}, "Sheaf.Paper.FixedPresentationUniformizerReductions": {"hash": "2195e8aeb4868a9a702ababa433fe6e635c0b07e", "status": "OK"}, "Sheaf.Paper.IsomorphismScalarAugmentationCone": {"hash": "aaa3d555357354b86b6218dc52405a5f6dd9c64f", "status": "OK"}, "Sheaf.Paper.IsomorphismScalarCompletedModel": {"hash": "585dfb5ef8a5dc6abaee39f03b64c93d62846be9", "status": "OK"}, "Sheaf.Paper.IsomorphismScalarFiniteComparisonExtension": {"hash": "991e1f8dbc18672728fbe44a766a492bec6ab242", "status": "INFRA"}, "Sheaf.Paper.IsomorphismScalarFiniteComparisonFormula": {"hash": "89226d90db73db521bd78b64177865a5f7ed5324", "status": "OK"}, "Sheaf.Paper.IsomorphismScalarFiniteComparisonUnit": {"hash": "4417f9977e578ee74703b0301cb54f9f56f18fa9", "status": "INFRA"}, "Sheaf.Paper.IsomorphismScalarFiniteCore": {"hash": "795cc3dcdd6a963af756502b0d44fe227ceb25ca", "status": "INFRA"}, "Sheaf.Paper.IsomorphismScalarFiniteLeftQuotientFormula": {"hash": "75b5ec5dd371852e154e1a6a9491d85b4cebd530", "status": "INFRA"}, "Sheaf.Paper.IsomorphismScalarFiniteModel": {"hash": "3ae0a743ea9ba6265a29e448119fc038e09f3e2e", "status": "OK"}, "Sheaf.Paper.IsomorphismScalarFiniteQuotientFormulas": {"hash": "5d472b18ecab7595a9627d061838d21729270910", "status": "INFRA"}, "Sheaf.Paper.IsomorphismScalarFiniteRightQuotientFormula": {"hash": "3a6340de97a328601f05c9b051e68d304cabcac2", "status": "OK"}, "Sheaf.Paper.IsomorphismScalarFiniteSquares": {"hash": "9cb8a773a70ee46277d1936a79ca08373568b59e", "status": "INFRA"}, "Sheaf.Paper.IsomorphismScalarFiniteTransitionFormulas": {"hash": "e48ea0ba683d7c94e47b7c3d15bd741ee20f29c6", "status": "OK"}, "Sheaf.Paper.IsomorphismScalarTensorKFlatModel": {"hash": "327a4898e867eaaef95b8967d5dc5396edb734cb", "status": "OK"}, "Sheaf.Paper.NormalizedIntegralTraceData": {"hash": "f7c116653c7faa062b478b61abb0a121463a5af7", "status": "OK"}, "Sheaf.Paper.PodCompletedOrdinaryTensor": {"hash": "9003a514f8782cd680607b20b2e0e895b1d34013", "status": "OK"}, "Sheaf.Paper.PodReindexingCompletionUnitTensor": {"hash": "6f89febbb6bfe7b7a78964b1f7236b01edd9f8cf", "status": "INFRA"}, "Sheaf.Paper.PodReindexingDerivedComparisons": {"hash": "9a5c0fd4a3f946f040079b43d472c13930dcf17e", "status": "INFRA"}, "Sheaf.Paper.PodReindexingDerivedComparisonsCore": {"hash": "17a9f282d9d87372fb63f9628de9885184021152", "status": "INFRA"}, "Sheaf.Paper.PodReindexingDerivedComparisonsPullback": {"hash": "6f560f36a82f319b7b4d3106ae4a841cacd433a9", "status": "INFRA"}, "Sheaf.Paper.PodReindexingDerivedCoreData": {"hash": "41fd72fd1b0e3986c47c84ea0f95c3518119e1d1", "status": "INFRA"}, "Sheaf.Paper.PodReindexingDerivedCoreDataExistence": {"hash": "bc60cbd04cab6ef64a7cfa613914d333888b7c7c", "status": "INFRA"}, "Sheaf.Paper.PodReindexingDerivedFiniteModel": {"hash": "8a1e954c3d65a24a4cb04aaa758bf13cba7a5437", "status": "INFRA"}, "Sheaf.Paper.PodReindexingDerivedLimitModel": {"hash": "8b1390fe309fa956f4383873af5ca653f9460b9c", "status": "OK"}, "Sheaf.Paper.PodReindexingDerivedLimitProjection": {"hash": "75869baf8c5be8b87cede56e375bc5319a3872d8", "status": "OK"}, "Sheaf.Paper.PodReindexingDerivedReductionEvaluation": {"hash": "068d09648acb10ecd2cb71435130989e2d9e5ce5", "status": "OK"}, "Sheaf.Paper.PodReindexingDerivedUnit": {"hash": "4c1a848c9fd0845a2bee37680b81a40478d2a32f", "status": "INFRA"}, "Sheaf.Paper.PodReindexingGoodComplex": {"hash": "1639565d50457f123e2a0bb51daa6858403acf36", "status": "OK"}, "Sheaf.Paper.PodReindexingRestrictedTower": {"hash": "f70f8f27e327685d3590d6ac09b6d7738b098b0b", "status": "OK"}, "Sheaf.Paper.PodReindexingStrictComparisons": {"hash": "cd5a1d2c690b642f6b3a5fc6a96e241753a5fbd1", "status": "OK"}, "Sheaf.Paper.PointInverseImageCoefficientTower": {"hash": "88fc8b48e5331cf5153add72d6cd4879b17bdaa1", "status": "INFRA"}, "Sheaf.Paper.PointRestrictionOrdinaryTensorSquare": {"hash": "d52d358a6972bff176a6f3df0f55e7224434e319", "status": "OK"}, "Sheaf.Paper.ResidueCompatiblePullbackFrobenius": {"hash": "3809fb3bf7cf447f73328d73f4943b7fdf05fed4", "status": "SLOW"}, "Sheaf.Paper.SemilinearFieldOperationLifts": {"hash": "6d6a2d120d28b0ce7b932dc7e4a3827dcf34daf2", "status": "OK"}, "Sheaf.Paper.SfRecollementReductionBoundary": {"hash": "3e5eb049e528ed51a96a3b71024b90d9c96825a0", "status": "OK"}, "Sheaf.Paper.TensorHomExchange": {"hash": "220d046d5b668a7f1aaab68abea931d9b7b3f9b2", "status": "OK"}, "Sheaf.Paper.TransportIntegralCounitRealization": {"hash": "362789f01525bd317330b272608a9f8d1b5f57d3", "status": "OK"}, "Sheaf.SecSmoothPurity.RationalPurityCommonComparisons": {"hash": "2b8a76033ed0141a0c750ad88d4f804323a159e7", "status": "OK"}, "Sheaf.SecSmoothPurity.RationalPurityLineComparisons": {"hash": "7dfea4a2aa9ca58786b61db04994341c85d15175", "status": "OK"}, "Sheaf.SecSmoothPurity.RationalPurityTraceCoherence": {"hash": "0091913289529cd60ce8938cc38e96ee7a2ce7a4", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralNormalizedAdjunction": {"hash": "dc3510828603f0e52ff4d7a2249b3f08c25fa75c", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralRealizationAssembly": {"hash": "029bbfb7a3f95cade80e36f8432d666abf17022a", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstruction": {"hash": "ecfed2c7ccc5b634e5234ed5d7238a3c6e1b0b1d", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstructionEquivalence": {"hash": "ba3c7868a918eff9ff9e82173364432b81326775", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces": {"hash": "dfd7491b122f1402fa3e5e5f1ca4f2b05228ee34", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralSystemExistence": {"hash": "3a2762881292a445abf50cc8f61fb3b3c0be90cb", "status": "OK"}, "Sheaf.SixFunctors.IntegralOperationShiftData": {"hash": "d79d356f094f2fb511f9e0bde2182c3cf96581b4", "status": "OK"}}, "seconds": 271, "time": "2026-10-28T10:43:33+0800", "transitive": 51, "version": 1}
```

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
