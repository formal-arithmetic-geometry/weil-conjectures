## What changed

Replaced the body of `AlgebraicGeometry.Scheme.lisseTower_scalar_restriction`
without changing any existing public signature, definition, attribute or public
import. The ordinary square is constructed explicitly: restrict the lower
module-sheafification unit along the commuting scalar presentations, extend it
by the upper sheafification adjunction, and prove that forgetting scalars gives
the identity. Its section normalization and uniqueness follow from the abelian
sheafification counits and faithful forgetting. The outer isomorphism equation
is reduced by a generic categorical component lemma, so concrete scalar
presentations need only the proved forgetful identity and the counit equality.

The completely proved construction is factored into
`CoefficientSheafificationSeed`, `CoefficientSheafificationIso`,
`CoefficientSheafificationForget`, `CoefficientSheafificationMapForget` and
`CoefficientSheafificationScalarSquare`, `CoefficientSheafificationSectionData` and
`CoefficientSheafificationSections`. These are new proved helper modules,
not new obligations. This factorization follows profiling and a redesign using
an abstract module presheaf, rather than expanding the finite coefficient
presentation throughout the construction.

The pulled actual tower transition is proved universal using the existing,
proved `inverseImage_mate_isIso` in
`ConstantAdicQuotientScalarComparison`. The scalar square and the fixed
realization equivalences give an equivalence of structured-arrow categories.
The supplied descent equation therefore transports the actual transition's
universality to the compared arrow. Two smaller tensor-compatibility statements
then give reflection to the etale site and preservation on an etale source.
The constant-arrow conjunct uses the already proved
`normalizationConstantArrow_isUniversal` and the same source-preservation
statement. All added imports of the item are private proof imports.

## Proved and sorry left

This is a decomposition, not a proof free of new holes. One original hole is
closed by a complete combining proof:
`AlgebraicGeometry.Scheme.lisseTower_scalar_restriction`.
There are zero holes left in the item module. Two holes are added, each in a new
module, with a full source and proof in words:

- `AlgebraicGeometry.Scheme.comparisonNormalization_reflects_universal`, node
  `lem-weil-pbc-comparison-normalization-reflects-universal`.
- `AlgebraicGeometry.Scheme.etaleSourceNormalization_universal`, node
  `lem-weil-pbc-etale-source-normalization-universal`.

The first concerns only finite fixed coefficient rings, a bounded coefficient
arrow and its specified comparison image. The second concerns only an already
universal coefficient arrow and inverse image to an etale source. Neither
contains an adic tower, fixed realization marking, the original descent
equation, the ordinary scalar square, or the original conjunction. They are
separate, strictly smaller parts of the argument. Empty schemes, zero rings and
zero complexes cause no exceptional case; no Tor bound is asserted or used.

The proved helper results include `rawMap_forget`, `rawMap_isIso`,
`rawMap_naturality`, `rawIso_forget`, `rawIso_map_forget`,
`coefficientPresheafIso_forget` and `coefficientScalarIso_forget` in namespace
`AlgebraicGeometry.Scheme.CoefficientSheafificationSquare`. Inside the item,
`finiteCoefficientIso_square`, `finiteScalarMap_square`,
`completionQuotient_square`, `scalarSquare_sections`,
`restrictedTransition_universal`, `anyScalarSquare_reflects`,
`constantLocal_universal` and `scalarSquareNormalized_unique` supply the actual
combining argument.

The seven new sheafification helper modules contain no holes. The categorical
mate calculation, universality of the actual pulled transition, conjugation,
reflection through the fixed realization equivalences, section normalization
and uniqueness are proved in Lean. Hole accounting: one upper hole closed, two
lower holes added; net closure is minus one. No arbitrary witness is selected
from an unproved existence statement.

Validation: every delivered module compiled individually within 60 seconds.
The complete item compiled cleanly in 19.5 seconds; the largest construction
module compiled in 47.9 seconds. No profiling or trace options remain. All new
Lean signatures match their node records.

## No longer needed

No original Lean import is removed, and no existing module is withdrawn or
claimed globally pruned. The item originally had only its public statement
import; it retains that import verbatim.

The item's direct proof dependencies
`lem-weil-pbc-ring-sheaf-change-adjunction` and
`thm-weil-pbc-site-comparison` are replaced by the precise dependencies of the
written proof. They remain needed transitively: the already proved scalar mate
uses the former theory, and the new comparison-reflection node cites the latter.
This is a direct-dependency simplification, not global pruning.

In particular, `Sheaf.Paper.EtaleNormalizationArrowUniversal` is not imported:
its constant-only statement does not prove the general descent-arrow case.
The constant case is instead obtained from the proved global constant-arrow
result and the source-preservation step already needed for the general case.
No unit statement or unit proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The original proof plan described the derived tensor interchanges in words but
provided no theorem for reflection through comparison or preservation on an
etale source for an arbitrary derived coefficient arrow. The existing
constant-only source theorem does not supply that generality. These two missing
steps are now stated separately with their K-flat tensor arguments.

The actual inverse-image scalar mate and the global constant-arrow universal
property are already proved in the library. They are used directly rather than
restated as new holes. The ordinary scalar square requires a real construction;
this delivery supplies that construction and its normalization instead of
choosing an unspecified square from an unproved existence theorem.

No existing statement is disputed or weakened, and no adopted source-library
file is changed. The original target and all original public definitions in the
item retain their exact text.

A dependency walk also found the existing baseline cycle between
`lem-pc-ring-hom-extension-differential` and
`lem-pc-ring-hom-extension-differential-adjacent`. The same cycle is present
before this packet; this delivery adds no dependency cycle. It is reported here
for the maintainer and is outside this item.

## New nodes

`def-weil-pbc-coefficient-sheafification-seed` records the explicit scalar-linear
unit and its adjoint extension, together with its forgetful identity. Its Lean
module is `Sheaf.Paper.CoefficientSheafificationSeed`; everything is proved.

`def-weil-pbc-coefficient-sheafification-iso` records the natural isomorphism
obtained because the forgetful functor reflects invertibility. Its Lean module
is `Sheaf.Paper.CoefficientSheafificationIso`; everything is proved.

`lem-weil-pbc-coefficient-sheafification-forget` records the proved forgetful
identity of the natural isomorphism. Its Lean module is
`Sheaf.Paper.CoefficientSheafificationForget`.

`lem-weil-pbc-coefficient-sheafification-map-forget` records the proved
forgetful formula after an arbitrary module-presheaf map. Its Lean module is
`Sheaf.Paper.CoefficientSheafificationMapForget`. This keeps the specialization
from repeatedly unfolding the full module-sheafification construction.

`def-weil-pbc-coefficient-sheafification-scalar-square` records the coefficient
presentation specialization and its identity on abelian sheaves. Its Lean
module is `Sheaf.Paper.CoefficientSheafificationScalarSquare`; everything is proved.

`def-weil-pbc-coefficient-sheafification-section-data` records the abelian
sheafification counits, identity forgetful comparisons and the abstract component
criterion for normalization. Its formulas are definitionally equal to the existing
public comparisons, as proved by the equality API in the item.

`lem-weil-pbc-coefficient-sheafification-sections` records the completely proved
section normalization for the generic constructed square. This lets the item
specialize a proved equality at the functor level, without rechecking a component
calculation after expanding actual adic coefficient data.

`lem-weil-pbc-comparison-normalization-reflects-universal` records reflection of
universal fixed-coefficient arrows through etale-to-proetale comparison. The
remaining proof identifies scalar adjuncts using K-flat tensor resolutions and
uses exact conservative comparison to reflect invertibility.

`lem-weil-pbc-etale-source-normalization-universal` records preservation of an
already universal coefficient arrow on an etale source. The remaining proof
uses the inverse-image/scalar-extension tensor comparison and its unit identity.

There are no changes to other existing modules and no change records.

## Related modules compiled before delivery

153 related module(s) compiled against this delivery by deliver3.py: 6 INFRA, 141 OK, 6 SLOW (13 more over the cap of 150 left to the landing).

```json
{"capped": true, "direct": 3, "left_out": 13, "own": {"Sheaf.Paper.CoefficientSheafificationForget": "1c1cff68dcd9085020a6106be0c7e2509d51d033", "Sheaf.Paper.CoefficientSheafificationIso": "c853ff3c97182afdb300b4aedf7c31bd6a496456", "Sheaf.Paper.CoefficientSheafificationMapForget": "09febc3b625196265b7b667d34a971faa0ba336b", "Sheaf.Paper.CoefficientSheafificationScalarSquare": "0fa761b93b184eee8754dd227865b55eb493f2e1", "Sheaf.Paper.CoefficientSheafificationSectionData": "f4b1a9d477ab9257a4167e5fd22953366689f10b", "Sheaf.Paper.CoefficientSheafificationSections": "3dbfdde91a94a70a3f57395acc853b007bb5e8af", "Sheaf.Paper.CoefficientSheafificationSeed": "fea4efd40e6d6e0c81a515be818627853d77a9fa", "Sheaf.Paper.ComparisonNormalizationReflectsUniversal": "1ce20f4c4e05ea1121e99a53aa0156aa64b78c79", "Sheaf.Paper.EtaleSourceNormalizationUniversal": "5ff3dfbec82d6a64208c307aedf613458d23da4c", "Sheaf.Paper.LisseTowerScalarRestriction": "46d6b2cfbf39ba1725dc5b9bd1fed1feb111fe4c"}, "results": {"Sheaf.DeligneLaumon.QbarCurveDuality": {"hash": "698919cd1c65cfbd98e0a94220b347ea95489629", "status": "OK"}, "Sheaf.DeligneLaumon.RawHeartAdicLisseData": {"hash": "b5fc1dcac941e8a658541909f46c73f5a5787738", "status": "OK"}, "Sheaf.Paper.A1QbarOpenClosedCohomology": {"hash": "c4393f08e5c29dcce5a8ec36b5668f487c7ac1f1", "status": "OK"}, "Sheaf.Paper.AdicCompletedTensorFiniteModels": {"hash": "c5f8e01c0e737e878997f2f5c62ec19d035201e0", "status": "OK"}, "Sheaf.Paper.AdicPurityTwistReduction": {"hash": "5b493ab008a50e7a1135367bad5f98de1e31d0a4", "status": "SLOW"}, "Sheaf.Paper.AdicSmoothDualizingComplexes": {"hash": "b7bc12fc291c8f482ac4fe6d09bf63fc202e05a6", "status": "OK"}, "Sheaf.Paper.BoundaryComparisonCompositionTransport": {"hash": "ea8d3e19ede5eb11ba97a76bf3857e2352e06243", "status": "OK"}, "Sheaf.Paper.ClassicalLisseWeilRestrictionData": {"hash": "c719a541a174b96f3e9936852275aefff4a14226", "status": "OK"}, "Sheaf.Paper.CoefficientScalarTensorRepresentativePasting": {"hash": "1ec03ab2c11da62bdb0dbe0b872c0cce1497040a", "status": "OK"}, "Sheaf.Paper.CompactSupportCondensedRealizationSetup": {"hash": "de8250bb6182922abae98dd0bb69160c8698968e", "status": "OK"}, "Sheaf.Paper.CompactSupportNativeRealization": {"hash": "4a71864fbb3ad647259d1a585a30f05780e34776", "status": "OK"}, "Sheaf.Paper.CompactSupportNormalizedRealization": {"hash": "58eb89cb700373bcccf18d953b5e270edde3d1ae", "status": "OK"}, "Sheaf.Paper.CompactSupportNormalizedTowerLimit": {"hash": "d891c8941c3f4c3a1ff1de1705a83f1b7b3ebdf0", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarLimitReduction": {"hash": "f0eba93ca050aa62762970feb3d74016b69b9b0e", "status": "OK"}, "Sheaf.Paper.CompactificationBProjectionData": {"hash": "129d619e714c40ab6ba499d20ded5bbcb84ffb2f", "status": "OK"}, "Sheaf.Paper.CompactificationBProjectionDomains": {"hash": "b29917f6369faa5a3c7a1ba8ddb5de38b72a713b", "status": "OK"}, "Sheaf.Paper.CompactificationBProjectionReduction": {"hash": "a0dae242c50d7c89e040f918a6bdabbe4c08cc32", "status": "OK"}, "Sheaf.Paper.CompletedCoefficientSystemTransport": {"hash": "868789cfc4135ae691a449ec5b25730aa7dcf7d1", "status": "OK"}, "Sheaf.Paper.CompletedOperationTowerSubstitution": {"hash": "e557195e0259c02ea2ca60e93196135c340bf36b", "status": "OK"}, "Sheaf.Paper.CondensedOpenCounitUnits": {"hash": "f6992093322faef0c8d2cc2c308093e13e78eae6", "status": "OK"}, "Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData": {"hash": "120436250c5e06a8d30545b904ea6efb84be81bf", "status": "OK"}, "Sheaf.Paper.ConstructibleExceptionalCoefficientAssemblyData": {"hash": "6742ac2d309011b0dce4dc5ff188b8ea94a56eac", "status": "OK"}, "Sheaf.Paper.ConstructibleExceptionalCoefficientCoherence": {"hash": "33eec6247ed0a12dde2d19457ea4f8beca28a6b9", "status": "OK"}, "Sheaf.Paper.ConstructibleExceptionalCoefficientConstruction": {"hash": "ecfd8306e54ee985ec1c843d4ef4edb4cf1e9f39", "status": "OK"}, "Sheaf.Paper.ConstructibleExceptionalLeftRefinements": {"hash": "4f327983ef6617b3300733e907052e229641b286", "status": "OK"}, "Sheaf.Paper.ContinuousAmbientGeometricCoherence": {"hash": "1be4b4c1e56beb66412d9085f0775d9f5297e360", "status": "OK"}, "Sheaf.Paper.ContinuousRationalDerivedRealization": {"hash": "2e9ed7ed16cdb547dfc39c20d3cb1761cdce7562", "status": "OK"}, "Sheaf.Paper.ContinuousRationalRealizationData": {"hash": "d9a50f3a32049ed022242104be024fc3ec389c92", "status": "OK"}, "Sheaf.Paper.DiagonalDncEtaleBeta": {"hash": "7a75f657ddbccd184e524fb4e109a011cdffc3bf", "status": "OK"}, "Sheaf.Paper.DiagonalEtaleSourceEndpoint": {"hash": "6813db4937373f8932d6f79f16f6ff6dc484ac88", "status": "OK"}, "Sheaf.Paper.DiagonalOrientationCompatibility": {"hash": "e1d5e6b660f6ff38b5e8f9ad329fc183bdb67f56", "status": "OK"}, "Sheaf.Paper.DiagonalOrientationRefinementData": {"hash": "1e12b94ddff14cd8a88a53e1df42c13dba8d3f1f", "status": "OK"}, "Sheaf.Paper.EmbeddedIntegralResidueTransport": {"hash": "03e41f5e3cda366c02f04f28b880f0ecc4aa100f", "status": "OK"}, "Sheaf.Paper.EmbeddedIntegralScalarKernelSquare": {"hash": "52d1a337ddbfe86e788911698be886672267fbf1", "status": "OK"}, "Sheaf.Paper.EmbeddedLatticeCoefficientComparison": {"hash": "740fedf34bc91b41575adcdf33e0781733def291", "status": "OK"}, "Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons": {"hash": "a09ffd92bfcb32abe2cfcdf4d36409c922bbff13", "status": "OK"}, "Sheaf.Paper.ExceptionalCommonStageFromRational": {"hash": "29a9766b30b9457948262ca2451b6bebab4494d2", "status": "OK"}, "Sheaf.Paper.ExceptionalFieldStageCompletion": {"hash": "b9ab72750220246aac18afbe8cc118dd4fedf308", "status": "OK"}, "Sheaf.Paper.ExceptionalFiniteScalarMatesData": {"hash": "ff81628ef42f87fe4cd72688930a2317e512939b", "status": "OK"}, "Sheaf.Paper.ExceptionalFiniteScalarOperation": {"hash": "a365ca7922e15d0e612f9438968f2551c2036e9b", "status": "OK"}, "Sheaf.Paper.ExceptionalRationalScalarComposition": {"hash": "ff89553a3c947d583ce84feab64495e603500185", "status": "OK"}, "Sheaf.Paper.ExceptionalReconstructionComparison": {"hash": "d2808d06efb721bf1bf12ac544724e77a081cd54", "status": "OK"}, "Sheaf.Paper.ExceptionalRefinementMates": {"hash": "bb351bc5b89a5fea6186ca565402287d6984dbe9", "status": "OK"}, "Sheaf.Paper.ExceptionalRefinementMatesData": {"hash": "80681bc0239420ded7d52f75c6c1fec5f4bf4016", "status": "OK"}, "Sheaf.Paper.ExceptionalRingStageAssembly": {"hash": "4a87df980c4d561050c019994e2facf132662d16", "status": "OK"}, "Sheaf.Paper.FieldExceptionalSystemDomains": {"hash": "77ba13cadcce5065a7d47c6fe19e6f37ad771fa7", "status": "OK"}, "Sheaf.Paper.FieldExtensionStrictLimits": {"hash": "0f13b9c4f2561f1d6c730cf8d797d4dc4484ab98", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemComparison": {"hash": "e493085b773fc372045148189085652d1b924450", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemComparisonData": {"hash": "97d81f9bdad7450a1e62daa9216f167abc5a0124", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemCoordinates": {"hash": "14fe2d2274a0f77c19cbfcaa3f2fd61332279406", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemFiniteOrientation": {"hash": "eb0e96fdd2f148cfa9bfa178452d4305f8ea3ca7", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemRigidity": {"hash": "18765b5e9e7e37f176463311133d1039cd0b9129", "status": "OK"}, "Sheaf.Paper.FieldProjectionOriginWitnesses": {"hash": "34d8d2f1cbb8b9b6675a22467568f044633ffa41", "status": "SLOW"}, "Sheaf.Paper.FieldProjectionSystemSquare": {"hash": "4b72add30ee79b2d358b5b82e82114855f04499d", "status": "OK"}, "Sheaf.Paper.FieldPurityTransposeArrows": {"hash": "bd6e29a7c71ad614a10743bd1517519239715b5d", "status": "OK"}, "Sheaf.Paper.FieldScalarSystemData": {"hash": "4ea15abd8389c021912e160104dbca146ab15545", "status": "OK"}, "Sheaf.Paper.FieldShriekSystemCoherence": {"hash": "226b707746899eb60e2d7006da2a1e55dc3cf24f", "status": "OK"}, "Sheaf.Paper.FieldShriekSystemComparison": {"hash": "a64b07d39146c1ade11d2aeb09c6eddfab1c213d", "status": "OK"}, "Sheaf.Paper.FieldShriekSystemMixed": {"hash": "f301afff7cce3f045fff446c5409f84a1398b268", "status": "OK"}, "Sheaf.Paper.FieldShriekSystemModels": {"hash": "2f1887ef99fc01e69d1558d52def6bac9eb48bbf", "status": "OK"}, "Sheaf.Paper.FiniteClopenDecompositionCore": {"hash": "0ecfeb796500d01e00af4db5992e499ef1f73526", "status": "OK"}, "Sheaf.Paper.FiniteClopenDerivedDecomposition": {"hash": "9e3a2103099d9d04aecdf49a810e68c2025b46ce", "status": "OK"}, "Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions": {"hash": "8818803754fe9515bf902cc1cf6fd6204835e6d9", "status": "OK"}, "Sheaf.Paper.FiniteRationalHeartComparison": {"hash": "f9138e0e66fddcbf69356c59319e700182264bdf", "status": "OK"}, "Sheaf.Paper.IntegralCoherenceData": {"hash": "a8811571094405833199a9683a744eb9f48ad707", "status": "OK"}, "Sheaf.Paper.IntegralCoherenceTower": {"hash": "dff2cb2fb9de0665ffc935a3018c17f55391495b", "status": "OK"}, "Sheaf.Paper.IntegralCompactSupportPrescribedReductions": {"hash": "59afa20f9e0874259ef6597e7639470b8cb4d1dd", "status": "OK"}, "Sheaf.Paper.IntegralCompositorLimitRealization": {"hash": "e9a370c8ea5ae90cf4c1c3a261c221affb1ff658", "status": "OK"}, "Sheaf.Paper.IntegralExceptionalInverseImage": {"hash": "64c7331a57e3878805911bfd2f624e53cce16e9f", "status": "OK"}, "Sheaf.Paper.IntegralExpressionSystemComparison": {"hash": "abb45d848f5229ac02fd60579d573bb566d3369b", "status": "OK"}, "Sheaf.Paper.IntegralGeometricComparisonData": {"hash": "cc2707568a162b346675b69ebc8591da39fe2c52", "status": "OK"}, "Sheaf.Paper.IntegralReconstructionComparisonData": {"hash": "88ad3c07a82b68901542849f4167187c1722104d", "status": "OK"}, "Sheaf.Paper.IntegralStrictExpressionRealization": {"hash": "ec137e5c640f724c37734e216a861372d93277d6", "status": "OK"}, "Sheaf.Paper.IntegralTowerLimitComparison": {"hash": "643c08a13b1737ba8549af7bfaf8169026508b24", "status": "OK"}, "Sheaf.Paper.KummerRootRankOne": {"hash": "a45aafe8fd0a8e4896285a38ed547f39dde05b17", "status": "OK"}, "Sheaf.Paper.KummerStratumScalarMateDetection": {"hash": "0bed38c5c2ad0f171f7917439cc5cab3e503e11e", "status": "OK"}, "Sheaf.Paper.KummerStrictTargetTransport": {"hash": "c3acf640e338a9800053af8db021062f6f64b52c", "status": "OK"}, "Sheaf.Paper.LissePointSectionsRealization": {"hash": "36c73c66305cd551cac15fabb6c9b1270740c2dd", "status": "OK"}, "Sheaf.Paper.LissePullbackNormalization": {"hash": "9ada3463a8cc27f3323ecc9b54a4188533bf1042", "status": "OK"}, "Sheaf.Paper.LisseRationalRealizationData": {"hash": "e86a199912d53bb7611e91bfea6bf2753bc13e44", "status": "OK"}, "Sheaf.Paper.LisseTensorNormalization": {"hash": "ea7ba69b1b30f08ff8ae722fe37f40be2cc500fa", "status": "OK"}, "Sheaf.Paper.LisseTensorPullbackRealization": {"hash": "7e032ff7dbb6f739aca3eefe04bf5ee493cd09ca", "status": "OK"}, "Sheaf.Paper.LisseTensorPullbackRealizationData": {"hash": "ba927c5dd6461ab4f21f1dc96d17aa3617231afc", "status": "OK"}, "Sheaf.Paper.LisseTowerEtaleNormalizationDescent": {"hash": "964ee6f37d157bc8c8e4bdec6183b90ea8a2363a", "status": "INFRA"}, "Sheaf.Paper.LisseTowerLocalizedRealization": {"hash": "7fc02abbc15c7911b37fc7c4d346153166d44694", "status": "INFRA"}, "Sheaf.Paper.LisseTowerPulledScalar": {"hash": "5533bee635e40ba11739ae183a19f530436e3d9e", "status": "INFRA"}, "Sheaf.Paper.LocalFrobeniusTransportNormalization": {"hash": "8e27d974b6a9b0ff80a57c15c11a4a1d68c76f02", "status": "OK"}, "Sheaf.Paper.LocallyClosedRelativeTransposeNormalization": {"hash": "0d023d969264489a018e97663f33434c61be5715", "status": "OK"}, "Sheaf.Paper.NativeAdicFiniteNormalization": {"hash": "891068305d0d87a67171418a42534d5dfc23eab0", "status": "OK"}, "Sheaf.Paper.NormalizedClassicalWeilRealization": {"hash": "e316bf919945f37e47b5d18cc76a2e0d85660aca", "status": "OK"}, "Sheaf.Paper.NormalizedInternalSupportScalars": {"hash": "3a664642e38f02b537c4bd8e7e3a513374fef90a", "status": "OK"}, "Sheaf.Paper.NormalizedRationalLeftComposition": {"hash": "386ff20d0beb9b231dd352f71607cd8f700f4af5", "status": "OK"}, "Sheaf.Paper.NormalizedRationalLeftIdentity": {"hash": "7b60b4e09579ad04bcbeb35a58b8e6e368c4b27d", "status": "OK"}, "Sheaf.Paper.NormalizedScalarAssociatorIntegralTransportCore": {"hash": "f4e81bcce22fea97ae95e8b6c4ab5280e72803d3", "status": "OK"}, "Sheaf.Paper.PurIntegralRepresentingPair": {"hash": "23dba7f89db6e6b102862ec3b949470582089706", "status": "OK"}, "Sheaf.Paper.PurIntegralRepresentingPairData": {"hash": "591fad86a7e590e125b33ad14402a74f8a3723f9", "status": "OK"}, "Sheaf.Paper.PurIntegralSupportComparison": {"hash": "ee354342d2ad136216093dabd5338e47edcf068f", "status": "OK"}, "Sheaf.Paper.PurityAffineChartExceptionalIdentification": {"hash": "6449d7608946e824fb9b2a61f92e012cf59b9a95", "status": "OK"}, "Sheaf.Paper.PurityTwistCancellation": {"hash": "e342d4577d2a620c86646989fe620a904cd4f30d", "status": "OK"}, "Sheaf.Paper.QbarCompactSupportBaseChange": {"hash": "5f8fb9970f9fd73eeb297cd970444ce0ee3930ff", "status": "OK"}, "Sheaf.Paper.QbarCompactSupportExchangeModel": {"hash": "ad4c1fa933a9b507d1a5776b66a48ba9aa7db7df", "status": "OK"}, "Sheaf.Paper.QcqsCompactSupportStrictReductionGamma": {"hash": "e1bfe18a6157dc6fcb29fd5b2ae2551bc6d8476f", "status": "OK"}, "Sheaf.Paper.RationalContinuousComparisonCoherence": {"hash": "6d7b50a3dd4cd179f3479de50e7748f6c26bc5d5", "status": "OK"}, "Sheaf.Paper.RationalContinuousOrdinaryPullback": {"hash": "ceed6f8c89cd5e24f30da005439adaee1d18022d", "status": "OK"}, "Sheaf.Paper.RationalContinuousPullbackTransport": {"hash": "e5454433450590ff49156f1cc3725dfacfbac774", "status": "OK"}, "Sheaf.Paper.RationalRealizationTensorComparisonData": {"hash": "a32c59bfea3016a706a9336ee75b25bc62e10143", "status": "OK"}, "Sheaf.Paper.RationalStratumPullbackData": {"hash": "856d8cd2f7c6ab5b1879988e1536b8620fdc2ef3", "status": "OK"}, "Sheaf.Paper.RationalStratumPullbackModels": {"hash": "8a27180dfeb0c99786fa4d5c9d9db66a6b72c4b8", "status": "OK"}, "Sheaf.Paper.ReconstructedPairRefinementCoherence": {"hash": "99eacf19cefde20a82db2edd3cc4efa87ce5f91d", "status": "OK"}, "Sheaf.Paper.ReconstructedPairRefinementData": {"hash": "7bd46425f55bf07aa501cc99d529fa096c0ffe03", "status": "OK"}, "Sheaf.Paper.ReindexingSystemHomReductionSquare": {"hash": "dcd01bbdd9a4bd06dd4a14f523ba1a03887ccf6d", "status": "OK"}, "Sheaf.Paper.RestrictedAffineDiagonalDncTrace": {"hash": "7577230f2c23058cdf619a3cfcdec5687c554ba5", "status": "OK"}, "Sheaf.Paper.ScalarShiftLineTowerTransport": {"hash": "dab59d6d3bc905afcfddeb9fd5f8c0bdd53caeea", "status": "OK"}, "Sheaf.Paper.SmoothPurityCoordinateRightComparisons": {"hash": "d506c8c30a1298b1e53af8c6e06b2cefe897d696", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerChartData": {"hash": "806e96474d46c26361718f260870666b1bd27ec8", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerGluingData": {"hash": "0bea1424c4eade65d219cb1a6fe2d5803e4702c8", "status": "OK"}, "Sheaf.Paper.SystemRefinementConstructibleDomain": {"hash": "a3fff07e75db157e2e4c1499019e0ad5c4fb939f", "status": "OK"}, "Sheaf.Paper.SystemScalarProjectionData": {"hash": "6e6a70ab41d6f19ceee232ba81eb824f4b6f89c8", "status": "OK"}, "Sheaf.Paper.TowerGeometricPurityData": {"hash": "ed87f8b9b06e73ceae670bcf6c4d5efb190ad45b", "status": "OK"}, "Sheaf.Paper.TowerIntegralCoefficientPullbackExistence": {"hash": "844d2e315e8702e994de01a2fdf18c6525995715", "status": "SLOW"}, "Sheaf.Paper.TowerRestrictedScalarAdjunction": {"hash": "64a28abb14d1843eab49d17dee2d137af703bf96", "status": "OK"}, "Sheaf.Paper.TowerScalarRootAbelianTranspose": {"hash": "30f00c53e994c9d4c38d5918f28f744215c6a8cf", "status": "OK"}, "Sheaf.Paper.TowerScalarRootAbelianTransposeComponent": {"hash": "0332fa4934e6d0e2c2b5d90bddd1eee9f710ace3", "status": "OK"}, "Sheaf.Paper.TowerScalarRootAbelianTransposeCore": {"hash": "ae26bbab61b86dc1e91a8466c4e1a733cd282e03", "status": "OK"}, "Sheaf.Paper.TowerScalarUnitAbelianTranspose": {"hash": "2cace1a9943c2a8d7d5dacdab95b22b9d4fe431b", "status": "OK"}, "Sheaf.Paper.TowerScalarUnitAbelianTransposeSection": {"hash": "973b7c9010a47802cb77c43492cbc0e357eadd01", "status": "OK"}, "Sheaf.Paper.TowerScalarUnitAbelianTransposeSectionNormalized": {"hash": "3a0fd0aa79c85f3538036f332c6136c51e3a19ba", "status": "OK"}, "Sheaf.Paper.TraceFormulaAdicSystem": {"hash": "60931b565cbc500c8fb4da977002786798171f38", "status": "SLOW"}, "Sheaf.Paper.TransportIntegralChartRealization": {"hash": "88cf176d90d5ec739ff0b920c34172ef3c69e24f", "status": "OK"}, "Sheaf.Paper.VectorBundleThom": {"hash": "24994216f1144863af07746169b823316d8a74bc", "status": "OK"}, "Sheaf.Paper.VectorBundleThomMaps": {"hash": "d34ef57ea712975602e195ffdb451068d640715e", "status": "OK"}, "Sheaf.Paper.VectorBundleThomProduct": {"hash": "a48058d7a5d2bf65c2d24feb234961c76bcc9cbc", "status": "OK"}, "Sheaf.Paper.WeilChosenDualityExchangeData": {"hash": "5cde62e4f890ccabacce5ef9c5939f73d2d2b6ee", "status": "OK"}, "Sheaf.Paper.ZlOpenDiagramComparisonTransport": {"hash": "439dd8854a850c506fa1ab129c9bb4ac67be516f", "status": "OK"}, "Sheaf.Paper.ZlOpenWeilUnitEmptyFibre": {"hash": "2c645bee0c85cdd5623a41dd36a150e0bb194e2c", "status": "OK"}, "Sheaf.SecSmoothPurity.IntrinsicCtfRefinementComparison": {"hash": "dc60cbcb0691394a569c8190648c2f377b3e93d9", "status": "OK"}, "Sheaf.SecSmoothPurity.ScalarExtensionFunctor": {"hash": "7e0d7f6cb0590e6ffa517397f62d5177bd15a9f6", "status": "SLOW"}, "Sheaf.SixFunctors.CoefQbarFiniteExceptionalCore": {"hash": "724048b4ae623baa9438865b3c724a893af8a6da", "status": "INFRA"}, "Sheaf.SixFunctors.CoefQbarFiniteExceptionalFormula": {"hash": "a1e3b69d6893c46fff72dc3d50dcd5d46d7ef81e", "status": "INFRA"}, "Sheaf.SixFunctors.CoefQbarVerdierBiduality": {"hash": "283d04c88de10f8c0ac296a94e8cc9f4246068a6", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierData": {"hash": "d25f0b76e5fc624b6b4cfe79dfbc577aef15f376", "status": "SLOW"}, "Sheaf.SixFunctors.CoefQbarVerdierExceptional": {"hash": "807b526093da108aa223c17704358fc4c6826b8c", "status": "INFRA"}, "Sheaf.SixFunctors.CoefQbarVerdierFiniteCoherence": {"hash": "0923df2ea38e9697e3eeb29190f7ff7088fc825a", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierFiniteEvaluationStage": {"hash": "ca0fb762ff05bb48a3dc5ef6f56a46c5118bed5d", "status": "OK"}, "Sheaf.SixFunctors.ConstructibleReductionGood": {"hash": "6f7ade2efe34c13d31e603253241c9525da2e1c6", "status": "OK"}, "Sheaf.SixFunctors.DiagramPullbackShiftData": {"hash": "029e0934e6b6dfed4813e75da38e9138879b1535", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstructionEquivalence": {"hash": "ba3c7868a918eff9ff9e82173364432b81326775", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces": {"hash": "dfd7491b122f1402fa3e5e5f1ca4f2b05228ee34", "status": "OK"}, "Sheaf.SixFunctors.IntegralCartesianCompactSupport": {"hash": "844e868381dea111880034c92b55780814eea6fa", "status": "OK"}, "Sheaf.SixFunctors.IntegralCompactSupportDefs": {"hash": "366a803773f3cf75606ed2c9c4352566f44db0fd", "status": "OK"}, "Sheaf.SixFunctors.NormalizedRingCompactScalarCocycle": {"hash": "648fbecf3c3ea3f595975abd71c05e6d2b1cf76d", "status": "OK"}, "Sheaf.SixFunctors.TensorHomTranspositionData": {"hash": "808bc39d21c40b865de5ef032bf3f9686e78be3b", "status": "OK"}, "Sheaf.SixFunctors.VerdierExchangeData": {"hash": "87de0c1fb2caa814366c393dd6853f34dd651a89", "status": "OK"}}, "seconds": 1187, "time": "2026-10-28T07:50:03+0800", "transitive": 150, "version": 1}
```

## Second reading by P1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
