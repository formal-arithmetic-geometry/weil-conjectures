## What changed

Repaired the quarantined module's broken public dependency. Replaced the public import of
`Sheaf.Paper.QcqsCompactSupportRealization` with the direct public import
`Sheaf.Paper.CompactSupportFiniteAction`, which supplies every compact-support finite
functor and reduction isomorphism used in this module. The former import was unused at the
interface level and pulled in a failing Qcqs realization dependency. All declarations,
statements, definitions, and existing theorem proofs remain unchanged.

The repaired module compiled with `python3 /home/ubuntu/weil-launcher/lcompile.py` with
exit code 0 and no diagnostics.

## Proved and sorry left

No existing theorem holes were closed. The seven existing named theorem obligations remain
unchanged: `systemDirectEvaluation_isIso`, `systemExchange_evaluation`,
`systemOpenEvaluationInv_isIso`, `systemOpenExchangeInv_isIso`,
`systemOpenScalarInv_isIso`, `directImage_roos`, and `compactRealization_existsUnique`.
There are seven `sorry`s left in the item and zero new `sorry`s or split statements.

## No longer needed

Removed the public import of `Sheaf.Paper.QcqsCompactSupportRealization`; no declaration
from that module is referenced by the repaired file. The direct
`Sheaf.Paper.CompactSupportFiniteAction` import replaces the transitive symbols required by
this module's public signatures. No DAG proof dependency is removed, since the Qcqs module
was not a proof dependency of this item's node.

## Where the brief, the DAG or earlier work was wrong

The module was quarantined for a stale bad-import build failure. Its source imported the
high-level Qcqs realization solely to obtain declarations actually defined by
`CompactSupportFiniteAction`. The replacement preserves all exposed types and declarations
while removing the failing dependency. No statement or unit-route defect was found.

## Related modules compiled before delivery

23 related module(s) compiled against this delivery by deliver3.py: 23 OK.

```json
{"capped": false, "direct": 23, "left_out": 0, "own": {"Sheaf.Paper.SystemOperationExchangeRealization": "8c1deef0392a4357201d367c68ce9e10841e2a8a"}, "results": {"Sheaf.Paper.CompactSupportCoefficientExchangeInvertible": {"hash": "6ce9ea1424c44fe6023543446de6388d132be3fb", "status": "OK"}, "Sheaf.Paper.CompactSupportFiniteScalarMateNormalization": {"hash": "c5574208f31a70980345a54cd2825805ed8b441d", "status": "OK"}, "Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms": {"hash": "98ab7f48c6b9e7364232dc6c6cc0a69ad97265c6", "status": "OK"}, "Sheaf.Paper.CompactSupportRealizedScalarTranspose": {"hash": "90017bc8f4386d2424bd3b0256c00f4cf80b200f", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarEvaluationSquare": {"hash": "8d58ece576e318fe541b9b55b6c479c26adc567c", "status": "OK"}, "Sheaf.Paper.CompactSupportSystemRealizationNormalization": {"hash": "3d61967d7537aa959d68b7f6983cffadfe893a0e", "status": "OK"}, "Sheaf.Paper.CompactSupportSystemScalarFiniteInvertible": {"hash": "bf2d428065bfe5b8537e64f154bbaeaa1f0ab8f1", "status": "OK"}, "Sheaf.Paper.CompactSupportSystemTransposeNormalization": {"hash": "25b428d31c12c81a616cb1dc001f3fb83a593541", "status": "OK"}, "Sheaf.Paper.DirectImageCoefficientExchangeInvertible": {"hash": "a6852077b27718a5df36ea0a3cc6ca863848afbb", "status": "OK"}, "Sheaf.Paper.FiniteGeometricSectionsPointOrbits": {"hash": "0fab31d29c0bdb92a95201e4fbc44d95c0c78723", "status": "OK"}, "Sheaf.Paper.FrobeniusSquareExchange": {"hash": "7ebce78f7f19e0d89781a23e101d1e0957274850", "status": "OK"}, "Sheaf.Paper.FrobeniusWitnessedCompactification": {"hash": "63570bf70ad598863632179912f15aae02517c61", "status": "OK"}, "Sheaf.Paper.IdentityOpenSystemEvaluation": {"hash": "4f1c8cc9b6d10836062ce3d9d64906d4944afed1", "status": "OK"}, "Sheaf.Paper.IntegralSupportFunctorNormalization": {"hash": "fb1f160aeee91fa0adc2ea96d83edb1460a363a9", "status": "OK"}, "Sheaf.Paper.IntegralSupportNormalizationData": {"hash": "3dace0973f3366637a488ddbda4029a59b48dba2", "status": "OK"}, "Sheaf.Paper.PoincareDualityConventions": {"hash": "71d52f8104ddecbf825f8e45fb9ea089898b08b2", "status": "OK"}, "Sheaf.Paper.ProperIntegralTowerComparison": {"hash": "bf7c2dec72446cceab3c19b831e7f4a44b3de2ae", "status": "OK"}, "Sheaf.Paper.ProperSystemEvaluationTransitions": {"hash": "a35ae0970b5881ee2262cad183e016284d9c4be6", "status": "OK"}, "Sheaf.Paper.SfIntegralPullbackLinearAdjunction": {"hash": "dc5d65483588c16dfe91655ac9462f25541f31f6", "status": "OK"}, "Sheaf.Paper.SfRationalLocalizationOrthogonality": {"hash": "efe12e2c710e23b20efd7b06d071e181613b85ef", "status": "OK"}, "Sheaf.Paper.StrictDirectImageMixedUnitData": {"hash": "437c66c50994d0d9dd1839879aac7f0c5a7288df", "status": "OK"}, "Sheaf.Paper.WeilBaseChangeSemilinearPasting": {"hash": "d9328ccbb02ec14ade42ff25cf4cf9f79800e5d6", "status": "OK"}, "Sheaf.SixFunctors.FiniteScalarMateData": {"hash": "6d833127857194ca1793a47e528ebd6b11472d2d", "status": "OK"}}, "seconds": 283, "time": "2026-10-28T00:47:35+0800", "transitive": 0, "version": 1}
```

## Second reading by C7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
