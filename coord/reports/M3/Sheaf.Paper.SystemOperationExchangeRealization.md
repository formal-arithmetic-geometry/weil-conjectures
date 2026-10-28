## What changed

Proved `directImage_roos` by applying `WeilConjectures.systemDirectImage_roosPresentation` and transporting its Roos triangle along the comparison isomorphism to the actual realized direct-image object. Added a private categorical helper for transporting derived-limit triangles along an object isomorphism. Added the proof-only import `Sheaf.Paper.SystemDirectImageRoosPresentation`.

## Proved and sorry left

Closed `WeilConjectures.FrobeniusExchange.directImage_roos` (one of seven original holes). The remaining six holes are unchanged: `systemDirectEvaluation_isIso`, `systemExchange_evaluation`, `systemOpenEvaluationInv_isIso`, `systemOpenExchangeInv_isIso`, `systemOpenScalarInv_app_isIso`, and `compactRealization_existsUnique`.

## No longer needed

None beyond the original imports; the Roos presentation dependency is now used directly by `directImage_roos`.

## Where the brief, the DAG or earlier work was wrong

The original proof plan for `directImage_roos` omitted the already available projection-compatible system Roos presentation. The proof uses that theorem and an explicit triangle transport instead of reproving the simultaneous-resolution construction.

## New nodes

Added `lem-derived-limit-triangle-transport`, realized by
`Sheaf.Paper.DerivedLimitTriangleTransport.derivedLimitTriangleTransport`, to isolate the
categorical transport used to build the required Roos object with the exact realized object.

## Related modules compiled before delivery

29 related module(s) compiled against this delivery by deliver3.py: 29 OK.

```json
{"capped": false, "direct": 29, "left_out": 0, "own": {"Sheaf.Paper.DerivedLimitTriangleTransport": "94d3a0732eb9f3e34f929b8d016bc323c6cd232a", "Sheaf.Paper.SystemOperationExchangeRealization": "364855c474359397666c45ba8204695b3c871d97"}, "results": {"Sheaf.Paper.CompactSupportCoefficientExchangeInvertible": {"hash": "6ce9ea1424c44fe6023543446de6388d132be3fb", "status": "OK"}, "Sheaf.Paper.CompactSupportFiniteScalarMateNormalization": {"hash": "c5574208f31a70980345a54cd2825805ed8b441d", "status": "OK"}, "Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms": {"hash": "98ab7f48c6b9e7364232dc6c6cc0a69ad97265c6", "status": "OK"}, "Sheaf.Paper.CompactSupportRealizedScalarTranspose": {"hash": "2def7613542ff16270232fc23e16acc1f2203727", "status": "OK"}, "Sheaf.Paper.CompactSupportRealizedScalarTransposeProjection": {"hash": "b7e805dec530b1dd2168503b98d957b8c8eea1e5", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarEvaluationSquare": {"hash": "4873c6b3e3219cb09a4e30281962b19eb1d15711", "status": "OK"}, "Sheaf.Paper.CompactSupportSystemRealizationNormalization": {"hash": "a910dc6d80312e2d52bf7393430c197f435555ff", "status": "OK"}, "Sheaf.Paper.CompactSupportSystemScalarFiniteInvertible": {"hash": "bf2d428065bfe5b8537e64f154bbaeaa1f0ab8f1", "status": "OK"}, "Sheaf.Paper.CompactSupportSystemTransposeNormalization": {"hash": "25b428d31c12c81a616cb1dc001f3fb83a593541", "status": "OK"}, "Sheaf.Paper.DirectImageCoefficientExchangeInvertible": {"hash": "a6852077b27718a5df36ea0a3cc6ca863848afbb", "status": "OK"}, "Sheaf.Paper.FiniteGeometricSectionsPointOrbits": {"hash": "0fab31d29c0bdb92a95201e4fbc44d95c0c78723", "status": "OK"}, "Sheaf.Paper.FrobeniusSquareExchange": {"hash": "7ebce78f7f19e0d89781a23e101d1e0957274850", "status": "OK"}, "Sheaf.Paper.FrobeniusWitnessedCompactification": {"hash": "63570bf70ad598863632179912f15aae02517c61", "status": "OK"}, "Sheaf.Paper.IdentityOpenSystemEvaluation": {"hash": "4f1c8cc9b6d10836062ce3d9d64906d4944afed1", "status": "OK"}, "Sheaf.Paper.IntegralSupportFunctorNormalization": {"hash": "fb1f160aeee91fa0adc2ea96d83edb1460a363a9", "status": "OK"}, "Sheaf.Paper.IntegralSupportNormalizationData": {"hash": "3dace0973f3366637a488ddbda4029a59b48dba2", "status": "OK"}, "Sheaf.Paper.PoincareDualityConventions": {"hash": "71d52f8104ddecbf825f8e45fb9ea089898b08b2", "status": "OK"}, "Sheaf.Paper.ProperIntegralTowerComparison": {"hash": "bf7c2dec72446cceab3c19b831e7f4a44b3de2ae", "status": "OK"}, "Sheaf.Paper.ProperSystemEvaluationTransitions": {"hash": "a35ae0970b5881ee2262cad183e016284d9c4be6", "status": "OK"}, "Sheaf.Paper.SfIntegralPullbackLinearAdjunction": {"hash": "dc5d65483588c16dfe91655ac9462f25541f31f6", "status": "OK"}, "Sheaf.Paper.SfRationalLocalizationOrthogonality": {"hash": "efe12e2c710e23b20efd7b06d071e181613b85ef", "status": "OK"}, "Sheaf.Paper.StrictDirectImageMixedUnitData": {"hash": "437c66c50994d0d9dd1839879aac7f0c5a7288df", "status": "OK"}, "Sheaf.Paper.SystemCompactExchangeEvaluation": {"hash": "bbfe912320a6f4d92e595e269de0e71a4f69677d", "status": "OK"}, "Sheaf.Paper.SystemOpenScalarEvaluation": {"hash": "049ad19fc6b6b03152b195e99050b53438e9f396", "status": "OK"}, "Sheaf.Paper.SystemOpenScalarEvaluationCore": {"hash": "c45132e368ae45d5977f5df7e92d69c891c095dc", "status": "OK"}, "Sheaf.Paper.SystemProperScalarEvaluation": {"hash": "99daba70061029e4019e2a36d43274002eaf26f6", "status": "OK"}, "Sheaf.Paper.SystemProperScalarEvaluationCompatibility": {"hash": "b655e751cf8fdf77b89111f529f6c002cdf95422", "status": "OK"}, "Sheaf.Paper.WeilBaseChangeSemilinearPasting": {"hash": "d9328ccbb02ec14ade42ff25cf4cf9f79800e5d6", "status": "OK"}, "Sheaf.SixFunctors.FiniteScalarMateData": {"hash": "6d833127857194ca1793a47e528ebd6b11472d2d", "status": "OK"}}, "seconds": 117, "time": "2026-10-28T08:24:45+0800", "transitive": 0, "version": 1}
```

## Second reading by M3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
