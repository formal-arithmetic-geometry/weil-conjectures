## What changed

Proved `WeilConjectures.FrobeniusExchange.systemOpenExchangeInv_isIso` from the existing
varying-ring Cartesian open base-change calculus. The new proved module
`Sheaf.Paper.IntegralSystemCompositorNormalization` identifies the ordinary compositors
by their section-normalized uniqueness and then identifies their exact derived
compositors. The new proved module `Sheaf.Paper.IntegralSystemSquareNormalization`
identifies the resulting pullback square and supplies the private mate calculation.

The inverse-beta identity proves invertibility for the varying-ring open adjunction.
The unique comparison between left adjoints transports this property to any adjunction
on the same restriction functor. Private pullback and functor-transport lemmas handle
the integral coordinates. The final calculation takes its adjunction as a parameter;
the item then applies it to its specified adjunction, keeping that data abstract.

The changes are confined to the item, its own DAG node, and these two new proved
modules with their nodes. The existing private vertical pushforward-equality helper
moves to the compositor module to keep the item within the compilation limit.
Existing public statements, definitions and public imports are retained. Two private
proof imports supply the new calculations; the square module privately imports the
existing categorical normalization helpers.

All three files compiled through `lcompile.py` in import order within 60 seconds each
(48.8, 49.6 and 45.2 seconds). Debug profiling was removed before delivery.

## Proved and sorry left

Closed one of the six original holes:
`WeilConjectures.FrobeniusExchange.systemOpenExchangeInv_isIso`.

Added zero holes and split off zero obligations. Five original named holes remain:

- `WeilConjectures.FrobeniusExchange.systemDirectEvaluation_isIso`
- `WeilConjectures.FrobeniusExchange.systemExchange_evaluation`
- `WeilConjectures.FrobeniusExchange.systemOpenEvaluationInv_isIso`
- `WeilConjectures.FrobeniusExchange.systemOpenScalarInv_app_isIso`
- `WeilConjectures.FrobeniusExchange.compactRealization_existsUnique`

The scalar component obligation belongs to node
`lem-weil-system-open-scalar-inv-app-is-iso`; the other four belong to
`def-weil-system-operation-exchange-realization`. Their statements and source proof
docstrings are retained.

## No longer needed

None. No existing imports, public declarations, nodes or modules are removed. The
relocated private helper remains used. The existing dependencies were already in the
item's transitive Lean import closure. The only added modules
are the two proved normalization steps, which add no holes to that closure. The fixed
blueprint unit route is retained.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found. The queue assigns a proof item with six current holes.
The saved global-build error refers to an obsolete import of
`Sheaf.Paper.QcqsCompactSupportRealization`; the current source has no such import.

For Cartesian open exchange, the existing varying-ring inverse-beta calculation and
exact-localization normalization supply the sectionwise proof already, so the remaining
work is to identify the actual compositors and transport between the derived adjunctions.
The finite evaluation holes involve a further coordinate comparison: their finite
pullback is the transported fixed-scalar model, whereas the varying-ring evaluation
lemmas use the tensor model. Those original obligations remain for later work.

## New nodes

- `lem-weil-integral-system-compositor-normalization`, realized by the proved
  `WeilConjectures.FrobeniusExchange.integralComparisonSystemComposition_eq_varyingRing`
  in `Sheaf.Paper.IntegralSystemCompositorNormalization`. This is the compositor comparison
  step of the open-exchange argument, separated to keep compilation within the file limit.

- `lem-weil-integral-system-square-normalization`, realized by the proved
  `WeilConjectures.FrobeniusExchange.integralComparisonSystemSquare_eq_varyingRing`
  in `Sheaf.Paper.IntegralSystemSquareNormalization`. It identifies the pullback square
  before taking mates and contains the proved private generic inverse-mate calculation.
  It is separated to keep compilation within the file limit.

## Related modules compiled before delivery

29 related module(s) compiled against this delivery by deliver3.py: 29 OK.

```json
{"capped": false, "direct": 29, "left_out": 0, "own": {"Sheaf.Paper.IntegralSystemCompositorNormalization": "b12429eb1c5ace1df1578f77ffbc67dc3cdb1fc0", "Sheaf.Paper.IntegralSystemSquareNormalization": "38b1f38959a4b4b9e2b029da6d23aed416f8c21c", "Sheaf.Paper.SystemOperationExchangeRealization": "e142fa2f92abae3bc191381fa03ff23c7f60ef60"}, "results": {"Sheaf.Paper.CompactSupportCoefficientExchangeInvertible": {"hash": "6ce9ea1424c44fe6023543446de6388d132be3fb", "status": "OK"}, "Sheaf.Paper.CompactSupportFiniteScalarMateNormalization": {"hash": "c5574208f31a70980345a54cd2825805ed8b441d", "status": "OK"}, "Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms": {"hash": "98ab7f48c6b9e7364232dc6c6cc0a69ad97265c6", "status": "OK"}, "Sheaf.Paper.CompactSupportRealizedScalarTranspose": {"hash": "2def7613542ff16270232fc23e16acc1f2203727", "status": "OK"}, "Sheaf.Paper.CompactSupportRealizedScalarTransposeProjection": {"hash": "b7e805dec530b1dd2168503b98d957b8c8eea1e5", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarEvaluationSquare": {"hash": "4873c6b3e3219cb09a4e30281962b19eb1d15711", "status": "OK"}, "Sheaf.Paper.CompactSupportSystemRealizationNormalization": {"hash": "a910dc6d80312e2d52bf7393430c197f435555ff", "status": "OK"}, "Sheaf.Paper.CompactSupportSystemScalarFiniteInvertible": {"hash": "bf2d428065bfe5b8537e64f154bbaeaa1f0ab8f1", "status": "OK"}, "Sheaf.Paper.CompactSupportSystemTransposeNormalization": {"hash": "25b428d31c12c81a616cb1dc001f3fb83a593541", "status": "OK"}, "Sheaf.Paper.DirectImageCoefficientExchangeInvertible": {"hash": "a6852077b27718a5df36ea0a3cc6ca863848afbb", "status": "OK"}, "Sheaf.Paper.FiniteGeometricSectionsPointOrbits": {"hash": "0fab31d29c0bdb92a95201e4fbc44d95c0c78723", "status": "OK"}, "Sheaf.Paper.FrobeniusSquareExchange": {"hash": "7ebce78f7f19e0d89781a23e101d1e0957274850", "status": "OK"}, "Sheaf.Paper.FrobeniusWitnessedCompactification": {"hash": "8b4ff518f7e7437d42d31453da2d88792c735346", "status": "OK"}, "Sheaf.Paper.IdentityOpenSystemEvaluation": {"hash": "4f1c8cc9b6d10836062ce3d9d64906d4944afed1", "status": "OK"}, "Sheaf.Paper.IntegralSupportFunctorNormalization": {"hash": "fb1f160aeee91fa0adc2ea96d83edb1460a363a9", "status": "OK"}, "Sheaf.Paper.IntegralSupportNormalizationData": {"hash": "3dace0973f3366637a488ddbda4029a59b48dba2", "status": "OK"}, "Sheaf.Paper.PoincareDualityConventions": {"hash": "71d52f8104ddecbf825f8e45fb9ea089898b08b2", "status": "OK"}, "Sheaf.Paper.ProperIntegralTowerComparison": {"hash": "bf7c2dec72446cceab3c19b831e7f4a44b3de2ae", "status": "OK"}, "Sheaf.Paper.ProperSystemEvaluationTransitions": {"hash": "a35ae0970b5881ee2262cad183e016284d9c4be6", "status": "OK"}, "Sheaf.Paper.SfIntegralPullbackLinearAdjunction": {"hash": "dc5d65483588c16dfe91655ac9462f25541f31f6", "status": "OK"}, "Sheaf.Paper.SfRationalLocalizationOrthogonality": {"hash": "efe12e2c710e23b20efd7b06d071e181613b85ef", "status": "OK"}, "Sheaf.Paper.StrictDirectImageMixedUnitData": {"hash": "437c66c50994d0d9dd1839879aac7f0c5a7288df", "status": "OK"}, "Sheaf.Paper.SystemCompactExchangeEvaluation": {"hash": "bbfe912320a6f4d92e595e269de0e71a4f69677d", "status": "OK"}, "Sheaf.Paper.SystemOpenScalarEvaluation": {"hash": "049ad19fc6b6b03152b195e99050b53438e9f396", "status": "OK"}, "Sheaf.Paper.SystemOpenScalarEvaluationCore": {"hash": "c45132e368ae45d5977f5df7e92d69c891c095dc", "status": "OK"}, "Sheaf.Paper.SystemProperScalarEvaluation": {"hash": "99daba70061029e4019e2a36d43274002eaf26f6", "status": "OK"}, "Sheaf.Paper.SystemProperScalarEvaluationCompatibility": {"hash": "b655e751cf8fdf77b89111f529f6c002cdf95422", "status": "OK"}, "Sheaf.Paper.WeilBaseChangeSemilinearPasting": {"hash": "d9328ccbb02ec14ade42ff25cf4cf9f79800e5d6", "status": "OK"}, "Sheaf.SixFunctors.FiniteScalarMateData": {"hash": "6d833127857194ca1793a47e528ebd6b11472d2d", "status": "OK"}}, "seconds": 122, "time": "2026-10-28T11:31:55+0800", "transitive": 0, "version": 1}
```

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
