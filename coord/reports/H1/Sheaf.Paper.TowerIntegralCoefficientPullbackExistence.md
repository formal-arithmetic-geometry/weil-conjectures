## What changed

Replaced the proof of `integralCoefficientPullback_exists`, preserving its complete
signature. Constructed the finite algebraic inverse images for the actual lifted
ZMod coefficient rings, proved their quotient-transition compatibility, and assembled
them using `ordinaryInverseSystem_exists`. Constructed the Kummer morphism using
`unitsPull` for both full-units components. The root square follows from adjunction
and the explicit section formulas; cartesianness makes its root component invertible.
The recorded integral Forget functor is fully faithful: uncurrying supplies the
underlying presheaf comparison, and the proved constant-torsion linearity lemma lifts
additive morphisms. The proved `undoRestriction` helper from
`SemilinearSystemIsoAssembly` transfers the finite linear maps across the evaluation
ring identification. This lifts the Kummer root isomorphism, and the composition
identities give the required root normalization.

Added `SemilinearOrdinaryInverseSystemKFlat`, proving the resolving property by
vertical evaluation, finite ringed-topos K-flat pullback, total-tensor evaluation and
componentwise exactness. Added `TowerIntegralInverseSystemNormalization` for the
remaining abelian-forgetful square and coefficient-unit normalization; it has no
Chern datum, root comparison, Kummer morphism or K-flat assertion.

All added imports of the item are proof imports. No existing signature, definition,
instance, attribute, public import or other existing module was changed.

Validation: all three modules compiled individually through `lcompile.py`. The item
compiled without errors or warnings, and its public theorem signature was compared
verbatim with the original. Development profiling options were removed.

## Proved and sorry left

Original holes: 1, in
`AlgebraicGeometry.ProEtale.SpTowerClasses.integralCoefficientPullback_exists`.
Its proof body is complete from the named lower statements.

Added holes: 1, in
`AlgebraicGeometry.ProEtale.SpTowerClasses.integralInverseSystem_normalization`
(node `lem-sp-tower-integral-inverse-system-normalization`). This is a decomposition,
replacing one upper hole by one smaller hole rather than claiming an axiom-free
proof of the upper statement. The remaining obligation is strictly smaller: only the underlying
abelian square, unit comparison and integer normalization for an already assembled
ordinary inverse system.

`WeilConjectures.SemilinearSections.ordinaryInverseSystem_kflat` is proved with zero
holes. The item's private finite-construction, full-faithfulness and Kummer helpers
also have zero holes. No other holes are added, and none occur in definitions.

## No longer needed

The old planned dependency `lem-pur-algebra-diagram-derived-comparisons`
(`Sheaf.CategoryTheory.AlgebraDiagramDerivedComparisons`) is not needed by this proof.
The K-flat argument instead uses the existing finite ringed-topos pullback theorem
and levelwise detection of exactness and tensor products. No ringed-topos realization
of the entire assembled system functor is required. The K-flat module also uses
`systemsComponentwise` directly from `SemilinearSystemsExistence`, avoiding an import
of the full `SemilinearDerivedSections` operations package for that single property.

Removed the redundant proof import of `Sheaf.Paper.SemilinearOrdinaryInverseSystem`
after the new normalization module publicly supplied the same API. The original
public import `Sheaf.Paper.TowerChernPullbackData` is retained. No existing module is
withdrawn, and no globally unused module is asserted solely from this local pruning.
All other old proof dependencies remain used directly or through the stated finite
inverse-image and normalization steps, as recorded in the revised node.

## Where the brief, the DAG or earlier work was wrong

The constant-ring convenience comparison adds a lift at a different universe from
the actual `Rlevel` rings. The proof therefore uses the general constant-sheaf
comparison at the actual single lifted ZMod ring. This is an API-universe issue,
not a change to the coefficient definition.

The Kummer morphism fields orient their commuting-square equations oppositely to
the usual displayed naturality squares; the proof reverses the equations explicitly.
The original mathematical statement and the unit route are retained.

## New nodes

`lem-sp-tower-integral-inverse-system-normalization` records the remaining source
step: lift the algebraic underlying comparisons to abelian towers, identify the
coefficient unit, and check integer normalization. It is independent of the Kummer
and resolving arguments proved in this delivery. Its docstring gives the complete
argument, including transition compatibility and local generation by integers.

`lem-coef-ordinary-inverse-system-kflat` records the proved generic evaluation
argument for flat-term K-flat complexes under ordinary inverse systems. It uses
vertical K-flat pullback, finite K-flat pullback, tensor evaluation and componentwise
exactness. Both nodes retain the item's chapter and unit. No change record is
needed: only the item proof, new modules and their node records are changed.

## Related modules compiled before delivery

90 related module(s) compiled against this delivery by deliver3.py: 87 OK, 3 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.SemilinearOrdinaryInverseSystemKFlat": "15e5ae69707e9a46793257d5274b89f67321ad48", "Sheaf.Paper.TowerIntegralCoefficientPullbackExistence": "844d2e315e8702e994de01a2fdf18c6525995715", "Sheaf.Paper.TowerIntegralInverseSystemNormalization": "4f4264fe938d476eaef87f5f1dced4925ff811fc"}, "results": {"Sheaf.Paper.CondensedIntegralEndpoints": {"hash": "dd232434d5a5e3148db6a3d554ab119400d15d77", "status": "OK"}, "Sheaf.Paper.DiagonalTraceDivisorChernAdjoint": {"hash": "99a00509714f3fea4a9ddf7d83b85a18a312fb6c", "status": "OK"}, "Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons": {"hash": "a09ffd92bfcb32abe2cfcdf4d36409c922bbff13", "status": "OK"}, "Sheaf.Paper.ExceptionalBaseChangeIntegralMaps": {"hash": "ddba29e6fa7e3139891c565fdbd1b35e93f330d1", "status": "SLOW"}, "Sheaf.Paper.FieldExceptionalFiniteCompatibility": {"hash": "f9b8c53074ee69dee3030b4890b39bb629141587", "status": "OK"}, "Sheaf.Paper.FieldExceptionalNormalizedAdjoints": {"hash": "80cf8d7bb647b2e16320fb964084659830d2762f", "status": "OK"}, "Sheaf.Paper.FieldExceptionalSystemAdjoints": {"hash": "112c3a1bf112c080324957387b9ac80f9131452a", "status": "OK"}, "Sheaf.Paper.FieldExceptionalSystemComparison": {"hash": "12e3c4e9bd5e5db433beb01a9c48f545b132c51d", "status": "SLOW"}, "Sheaf.Paper.FieldExceptionalSystemComponents": {"hash": "ef3ec6685c2d4f55c03185ce26a35fefaba277fa", "status": "OK"}, "Sheaf.Paper.FieldExceptionalSystemDomains": {"hash": "77ba13cadcce5065a7d47c6fe19e6f37ad771fa7", "status": "OK"}, "Sheaf.Paper.FieldExceptionalSystemEvaluation": {"hash": "11b104a863ddf0537f89ae769e73035cbd6a9458", "status": "OK"}, "Sheaf.Paper.FieldExceptionalSystemFiniteAdjoint": {"hash": "fa1d56ada56b4076a0ad2916494750d1a116088f", "status": "OK"}, "Sheaf.Paper.FieldExceptionalSystemFiniteComposite": {"hash": "99ff5f3aa5773183ea33fe4dc7347e629ef88596", "status": "OK"}, "Sheaf.Paper.FieldExceptionalSystemIso": {"hash": "b1030c5464b7b842874af4e1fc6a79bc66edde3b", "status": "OK"}, "Sheaf.Paper.FieldExceptionalSystemLaws": {"hash": "78cb4831b5da8f4e811ba9a761105698df829a70", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemComparison": {"hash": "e493085b773fc372045148189085652d1b924450", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemComparisonData": {"hash": "97d81f9bdad7450a1e62daa9216f167abc5a0124", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemCoordinates": {"hash": "14fe2d2274a0f77c19cbfcaa3f2fd61332279406", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemFiniteOrientation": {"hash": "eb0e96fdd2f148cfa9bfa178452d4305f8ea3ca7", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemHeart": {"hash": "9a070f47bd829208725e5f5eeee2aac22cacda63", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemNormalizations": {"hash": "e22be0a0e93d29067a2ae0db451474bb52136641", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemRigidity": {"hash": "18765b5e9e7e37f176463311133d1039cd0b9129", "status": "OK"}, "Sheaf.Paper.FieldProjectionOriginWitnesses": {"hash": "34d8d2f1cbb8b9b6675a22467568f044633ffa41", "status": "SLOW"}, "Sheaf.Paper.FieldPuritySystemTranspose": {"hash": "76d579b774387bd695951bbf5d80a728fd3f189f", "status": "OK"}, "Sheaf.Paper.FieldPuritySystemTransposeBase": {"hash": "0882a7a028b9479a0000159cb4ff3ff179ff9277", "status": "OK"}, "Sheaf.Paper.FieldPurityTransposeArrows": {"hash": "bd6e29a7c71ad614a10743bd1517519239715b5d", "status": "OK"}, "Sheaf.Paper.FieldPurityTransposeLevelWords": {"hash": "d261fe7d404f063aa06890a477215a246d53f6ac", "status": "OK"}, "Sheaf.Paper.FiniteGammaEvaluationIsIso": {"hash": "7399b04e1cb09b13b71b32a5c04292d5061883b4", "status": "OK"}, "Sheaf.Paper.FixedPresentationUniformizerReductions": {"hash": "2195e8aeb4868a9a702ababa433fe6e635c0b07e", "status": "OK"}, "Sheaf.Paper.GeometricSmoothReconstructionSetup": {"hash": "d5f8abc24f480c3f5afd7ca4f7437295faaef56c", "status": "OK"}, "Sheaf.Paper.IntegralGeometricComparisonData": {"hash": "cc2707568a162b346675b69ebc8591da39fe2c52", "status": "OK"}, "Sheaf.Paper.IntegralGeometricComparisonRealization": {"hash": "e2edc201638183226483011a57348a50acc201a4", "status": "OK"}, "Sheaf.Paper.IntegralGeometricPurityRealization": {"hash": "0b3aa89bec9034609abf2e195b105fef87d9a785", "status": "OK"}, "Sheaf.Paper.IntegralGeometricReindexingRealization": {"hash": "dc82db56836939bdf56488314584512a9aad340d", "status": "OK"}, "Sheaf.Paper.IntegralGeometricSupportRealization": {"hash": "9ba359469968ecca14a23af8cb500f18fb9dd9c6", "status": "OK"}, "Sheaf.Paper.IntegralGeometricTransposeIdentity": {"hash": "1ae653a0bbd43cc9d3515b58d0ae07ae3f6015a9", "status": "OK"}, "Sheaf.Paper.IntegralReconstructionComparisons": {"hash": "ff879e514ff031ee4466f415e7008cada241790e", "status": "OK"}, "Sheaf.Paper.NormalizedIntegralTraceData": {"hash": "f7c116653c7faa062b478b61abb0a121463a5af7", "status": "OK"}, "Sheaf.Paper.OrderedLineLevelBounds": {"hash": "5f72ca8d9be8baf15de4529cd0c1467486cdb2d3", "status": "OK"}, "Sheaf.Paper.OrderedTowerOrientation": {"hash": "99343b2d44ec92787450dc6ec2604ea4e9142b7d", "status": "OK"}, "Sheaf.Paper.OrientationScalarTowerTransport": {"hash": "322b312084978e6ab9be061d3acdf23b186ec025", "status": "OK"}, "Sheaf.Paper.PurityConjugatesTowerReduction": {"hash": "1e086facd08a557ee70cd2b11daed249cb5fb1fd", "status": "OK"}, "Sheaf.Paper.PurityFiniteReductionTransport": {"hash": "bc622c3185cb59358dd7f8e7929fd9b6f2f8afe6", "status": "OK"}, "Sheaf.Paper.PurityPullbackLevelBounds": {"hash": "6ea155b44a709e8e23091cc0afc8ce2b286335a5", "status": "OK"}, "Sheaf.Paper.PurityPullbackReductionTransport": {"hash": "49fb368f9bc4b67444caa0756750e0b77b22eef5", "status": "OK"}, "Sheaf.Paper.PurityTowerReductionComparisons": {"hash": "a116ef52274ded289b1c2ab3b825696d5255418e", "status": "OK"}, "Sheaf.Paper.SmoothPurityCoordinateCategories": {"hash": "c3dc3230c364220ceca5d590bdcf2ada9349e102", "status": "OK"}, "Sheaf.Paper.SmoothPurityCoordinateChartModels": {"hash": "cbbecb384ab14f27d70db73117f4a6349fbc05e2", "status": "OK"}, "Sheaf.Paper.SmoothPurityCoordinateFoundations": {"hash": "69c86a5fa44c433cdd8e98922e5c129704e3cb37", "status": "OK"}, "Sheaf.Paper.SmoothPurityCoordinateProjectionModels": {"hash": "89c057a40470ac325e30b82dd0fde67b69fe2821", "status": "OK"}, "Sheaf.Paper.SmoothPurityCoordinateRightComparisons": {"hash": "d506c8c30a1298b1e53af8c6e06b2cefe897d696", "status": "OK"}, "Sheaf.Paper.SmoothPurityCoordinateTensorComparisons": {"hash": "b8ae271988d02e8e639afb5418f585d92f4850f8", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerCoordinateAdjunction": {"hash": "b1a27e2ae98045d179ddbf39349b9381f84f6712", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerCoordinateAdjunctionModels": {"hash": "6cf97072e1c0ce4f30870c677072e701454433bf", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerEvaluatedRepresentability": {"hash": "ea7d26914702f1502034bac88e98fc0d6a6da444", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange": {"hash": "6f30c11dc8ec3387ce795d19d5615b4637267f9b", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerGamma": {"hash": "5acba5c62f3ee60c4f89317ea0ebbe0014833afb", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerGammaData": {"hash": "3faa678db6f55cda2c50b35f9edb2522aed87431", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerGluing": {"hash": "f6a837293f8b6948f9f8cabe3e2762c745f27919", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerGluingData": {"hash": "0bea1424c4eade65d219cb1a6fe2d5803e4702c8", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerMateEvaluationReduction": {"hash": "028e502b9e8a2cae283bbd23209bd15e7c0de3af", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerP1Adjunction": {"hash": "aec60f51a694a7a14c629f01f44b2a817c8cc559", "status": "OK"}, "Sheaf.Paper.SpecifiedTowerAdjunctionCharts": {"hash": "a48d6289d794e566bc76098a6213eef9ece33155", "status": "OK"}, "Sheaf.Paper.TensorTransposeFiniteEvaluation": {"hash": "2747fdf31112a4c3a3e19ac5d06b7568f27fdf20", "status": "OK"}, "Sheaf.Paper.TensorTransposeTowerNaturality": {"hash": "0a067dc359f6b0bbf18ecaa7a0ddd6e18fc71061", "status": "OK"}, "Sheaf.Paper.TowerAdjointCompositorRealization": {"hash": "3335de08342a2b60e780d336adf844be0a8667e1", "status": "OK"}, "Sheaf.Paper.TowerChernOrdinaryScalarPullback": {"hash": "ca1b891a82f29bd183913ad0bdba9c7316d20d9c", "status": "OK"}, "Sheaf.Paper.TowerCompositorFiniteEvaluation": {"hash": "436cdbf47d228a39559ddb67b1a40be737818db8", "status": "OK"}, "Sheaf.Paper.TowerGeometricPurityAssembly": {"hash": "0c61068a11023e1f3414c29eda621862a82991bb", "status": "OK"}, "Sheaf.Paper.TowerGeometricPurityData": {"hash": "ed87f8b9b06e73ceae670bcf6c4d5efb190ad45b", "status": "OK"}, "Sheaf.Paper.TowerGeometricPurityMate": {"hash": "5148d3e17b63f01e577b8a194970f03cbc3065cd", "status": "OK"}, "Sheaf.Paper.TowerIsomorphismPullback": {"hash": "017c2bf54510d71e12db382735abbfc2d2ac40da", "status": "OK"}, "Sheaf.Paper.TowerNormalizationPreservation": {"hash": "1885f0cb5c93f66cc64ed000402c2d6d74ce18d8", "status": "OK"}, "Sheaf.Paper.TowerOrientationEvaluation": {"hash": "8705c45aebd6d1ea6a6fe504576b8c30baaba78c", "status": "OK"}, "Sheaf.Paper.TowerOrientationWordNormalization": {"hash": "97abe3d31b6ee4ed5f46d6370e95a616eca74995", "status": "OK"}, "Sheaf.Paper.TowerP1KernelScalarNormalization": {"hash": "e96674b8d5a2ddb1dfbba3f0d4877d8b8afa2556", "status": "OK"}, "Sheaf.Paper.TowerP1KernelSplittingBaseChange": {"hash": "db5fce4539507cbbe567af91db079e78cbf83732", "status": "OK"}, "Sheaf.Paper.TowerPurityPresentationRetagging": {"hash": "b2571a7d3262d6e579352822e236d226529aac30", "status": "OK"}, "Sheaf.Paper.TowerSemilinearPurityFactors": {"hash": "8719bba6ca94b52eb9e12182c593ee391f39961d", "status": "OK"}, "Sheaf.Paper.TowerTensorPresentationRetagging": {"hash": "af1e0b391289cc4aabadff640afc28538a5a9746", "status": "OK"}, "Sheaf.Paper.TowerTensorTransposeEvaluation": {"hash": "a47c26025f99b360a1796e9227faaf10a3b816db", "status": "OK"}, "Sheaf.Paper.TowerTensorTransposeWords": {"hash": "7651e3f44fb3fedc396bf3a3849fe75be73b6b36", "status": "OK"}, "Sheaf.Paper.TransportCondensedStageRealization": {"hash": "f8323086ff6e7137688f677c6b511811ad4fe164", "status": "OK"}, "Sheaf.Paper.TransportIntegralBaseChangeRealization": {"hash": "41279c82fb72a9f1781669c5bea4f75d167c5e20", "status": "OK"}, "Sheaf.Paper.TransportIntegralChartRealization": {"hash": "88cf176d90d5ec739ff0b920c34172ef3c69e24f", "status": "OK"}, "Sheaf.Paper.TransportIntegralCompositionRealization": {"hash": "38a24cd4b0bc9510d17ddebd74c653bca11b0693", "status": "OK"}, "Sheaf.Paper.TransportIntegralCounitRealization": {"hash": "362789f01525bd317330b272608a9f8d1b5f57d3", "status": "OK"}, "Sheaf.Paper.TransportIntegralStageConstruction": {"hash": "80d4d6ba6379bc0c6e16c865a1516facb64b28ed", "status": "OK"}, "Sheaf.Paper.TwistedPullbackTowerDomain": {"hash": "707eb28c771ca3083afffa07cdfbdba735f46fe5", "status": "OK"}, "Sheaf.Paper.TwistedPullbackTowerDomainDefinitions": {"hash": "6632aecdf649f0d15eab12e57540459901c0851c", "status": "OK"}}, "seconds": 621, "time": "2026-10-28T00:58:49+0800", "transitive": 89, "version": 1}
```

## Second reading by H1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
