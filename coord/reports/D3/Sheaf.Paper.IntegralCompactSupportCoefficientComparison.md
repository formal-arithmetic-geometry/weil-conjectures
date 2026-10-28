## What changed

Reduced `WeilConjectures.PurCompactSupport.integralCoefficientComparison` to the
bare proper/open derived-limit realization. Its five-conjunct signature is unchanged.
The proof supplies preservation of integral constructibility and the uniform Tor
interval, invertibility of the specified scalar comparison, and constructibility of
both output objects by the existing theorem for every derived limit of the finite
compact-support tower.

The scalar-domain argument uses the completed finite-free comparison, intrinsic
constructibility preservation and finite scalar-extension Tor preservation. It
works at equal positive quotient exponents and needs no chosen ramification index.
The proper scalar-mate argument uses the independent finite-free direct-image
coherence theorem, finite product/coproduct conversion and adjunction conjugation;
the existing open comparison and factorization finish the actual mate calculation.
The mate proofs follow the existing `FiniteFreeProperScalarComparison` argument,
whose direct import would cycle. The fully proved lower mate expression is extracted
into `FiniteFreeRestrictionDirectImageMate`, which does not mention the higher
`properComparison` declaration and therefore imports no higher comparison module. The equal-exponent reduction helper is
reused directly from `PurAdicScalarExtensionTorBound` through a proof-only
`import all`; no second copy of that helper is introduced.

Added `Sheaf.Paper.IntegralProperOpenDerivedLimit` with one named remaining
obligation and a source proof. It states only that the ambient completed proper/open
object is a derived limit of the specified finite compact-support tower. It has no
varying coefficient extension, no scalar-domain conclusion, no invertibility
conclusion, and no projection-normalized uniqueness claim. The main proof applies
it once over each coefficient field. Existing compact-support constructibility
applies to the resulting triangles directly. The theorem that any two vertices of
the same derived-limit triangle are isomorphic gives the final recorded E-value
identification.

The added imports in the item are proof-only. All existing statements, definitions,
public imports and previously completed results are preserved. The constructibility
step inside the already proved `projectionDomain_complete` now uses the derived-limit
constructibility theorem directly, instead of specializing all five comparison clauses
to the identity coefficient extension. The parent DAG route
and three new nodes record the actual reduction and the two proved scalar helpers. After
removing a duplicated expensive scalar helper and a large equality transport, a
profiled compile finished in 57.6 seconds but delivery measured 63.8 seconds. The
independent mate argument accounted for 9.84 seconds of type checking, so it was
extracted into a separate module. No shared definition was changed and the limit
was not raised. A lighter profile with the direct projection-domain argument finished
in 56.5 seconds. The fully proved scalar-preservation argument was then extracted
as `FiniteTorIntegralCompletedScalarExtension` to provide more timing margin.
After extraction, all four modules compiled in import order: the scalar-preservation
module in 11.4 seconds and the item in 56.7 seconds (the other two reused successful
results). Two instance-style warnings in the new scalar module were corrected by
using `have` for local class proofs. Profiling options and diagnostic checks were
removed before delivery.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PurCompactSupport.integralCoefficientComparison` and added the
strictly smaller hole
`WeilConjectures.integralProperOpen_isDerivedLimit`
(node `lem-pur-integral-proper-open-derived-limit`). This is one decomposition,
with net zero holes closed, rather than a completed proof of the main mathematics.
There were nine holes in the assigned source; eight remain in that file and one
is in the new module. No other holes are introduced.

The unchanged holes are all attached to
`lem-pur-compact-support-integral-coefficient-comparison`:

- `WeilConjectures.PurCompactSupport.comparison_composition`;
- `WeilConjectures.PurCompactSupport.comparison_identity`;
- `WeilConjectures.PurCompactSupport.recordedIdentification_existsUnique`;
- `WeilConjectures.PurCompactSupport.refinementProperOpen_existsUnique`;
- `WeilConjectures.PurCompactSupport.comparison_refinement`;
- `WeilConjectures.PurCompactSupport.refinementComparison_coherence`;
- `WeilConjectures.PurCompactSupport.comparison_strict_towers`;
- `WeilConjectures.PurCompactSupport.comparison_projection`.

The private mate-transport and support-factorization helpers and the public
`WeilConjectures.PurCompactSupport.finiteFreeRestrictionDirectImageMate_isIso`
and `WeilConjectures.finiteTorIntegralCompletedScalarExtension` are fully proved.
Both new scalar-helper modules have zero holes.
The imported equal-exponent reduction helper is already fully proved. In particular
the new integral mate-invertibility argument does not use `finiteProperComparison_isIso`.

## No longer needed

No existing import or module is withdrawn, and no node is globally pruned. The
coefficient-model, strict-scalar-mate and scalar-limit-reduction route is not needed
for the primary theorem's scalar-domain and invertibility clauses. Its stronger
normalizations remain relevant to the eight unfinished coherence declarations, so
those dependencies are retained in the parent node. No unit statement or unit proof
step is bypassed. The projection-domain constructibility argument no longer invokes
the scalar-preservation, comparison-invertibility or recorded-value clauses of the
main theorem at the identity coefficient extension.

The main theorem uses the independent `FiniteFreeDirectImageCoherence` interface
through the proved `FiniteFreeRestrictionDirectImageMate` module, instead of
importing `FiniteFreeProperScalarComparison`; it uses the existing
reduction helper and finite scalar Tor argument from
`PurAdicScalarExtensionTorBound`, without applying the larger ramification-indexed
preservation theorem.

## Where the brief, the DAG or earlier work was wrong

The queue snapshot lists ten holes, while the assigned source contains nine. The
older build-error record lists dependency-artifact failures; this is not a zero-hole
repair assignment. The current source retains the recently proved quotient proper
mate and reduction comparison.

Several suggested dependencies already import this item, so they cannot be used
as proof imports here: in particular `CompactSupportCoefficientModels`,
`FiniteFreeProperScalarComparison` and `QcqsCompactSupportRealization`. Their lower
independent statements are usable. This delivery preserves their declarations and
records only the narrower missing realization needed by the primary theorem.

`FiniteProperComparisonIso` explicitly disputes its unrestricted arbitrary-Change
invertibility assertion; finite freeness is essential. The new integral argument
supplies finite freeness and proves invertibility through the independent column
calculation. The pre-existing finite comparison and shift declarations and their
separate disputed dependencies are outside this partial reduction and unchanged.

The new lemma's source argument is Bhatt--Scholze Lemma 6.1.13 (open extension
commutes with homotopy limits), Definition 6.7.6 and Lemma 6.7.7 (separately derived
proper/open compact support), together with Stacks Tag 0941 for strict towers and
Roos triangles. It does not derive the composite abelian functor; Remark 6.7.8
explains why that would be wrong. Edge cases include zero input, empty open and
identity compactifications. Neither uniqueness of triangle fillers nor faithfulness
of derived finite evaluation is claimed.

## New nodes

`lem-pur-integral-proper-open-derived-limit` is realized by
`Sheaf.Paper.IntegralProperOpenDerivedLimit` and the theorem
`WeilConjectures.integralProperOpen_isDerivedLimit`. Its conclusion is a single
fixed-coefficient derived-limit assertion. The node contains the strict quotient,
open extension, proper direct image, intrinsic tower transport and Roos-triangle
steps, source citations and three recorded Mathlib searches. It inherits the item's
chapter and unit. There are no change records because no existing public interface
or other existing module is changed.

`lem-pur-finite-free-restriction-direct-image-mate` is realized by the zero-hole
module `Sheaf.Paper.FiniteFreeRestrictionDirectImageMate` and its explicit inverse
scalar-mate theorem. Its statement has no reference to the higher compact-support
comparison, so extracting the proof breaks no import direction. Its proof uses the
existing finite-free column theorem and Mathlib mate-conjugation identities.

`lem-pur-finite-tor-integral-completed-scalar-extension` is realized by the zero-hole
module `Sheaf.Paper.FiniteTorIntegralCompletedScalarExtension` and the theorem
`WeilConjectures.finiteTorIntegralCompletedScalarExtension`. It proves the ordinary
scalar-domain clause without compactification or geometric assumptions, using only
the finite-free comparison, intrinsic constructibility and finite scalar Tor theorem.

## Related modules compiled before delivery

90 related module(s) compiled against this delivery by deliver3.py: 1 INFRA, 85 OK, 4 SLOW.

```json
{"capped": false, "direct": 90, "left_out": 0, "own": {"Sheaf.Paper.FiniteFreeRestrictionDirectImageMate": "53a350ebb07a7d00743cd8329d476ba9a7600dce", "Sheaf.Paper.FiniteTorIntegralCompletedScalarExtension": "b2c8f897302b9a5f18fd8bee6fc681dff1d8eafb", "Sheaf.Paper.IntegralCompactSupportCoefficientComparison": "71ade78dbf5c283d6989e0e83cfe1b04180b389f", "Sheaf.Paper.IntegralProperOpenDerivedLimit": "7ae5082dffd414df3fd8718545423cf8b5a70f4f"}, "results": {"Sheaf.Paper.AdicOperationDomainsSourceComparison": {"hash": "2e48216f8679052116f7646d12477accfd1c91d4", "status": "OK"}, "Sheaf.Paper.CompactSupportArrowScalarTransport": {"hash": "c948fb3f2cf76d91a820583c48f339f79e90b60b", "status": "OK"}, "Sheaf.Paper.CompactSupportCoefficientModels": {"hash": "b802a913c8d344956667b3d4e8e833177a8f7f8e", "status": "OK"}, "Sheaf.Paper.CompactSupportCondensedRealization": {"hash": "cc1a66f277773a79d8bbf10c18b7f4a69c05d265", "status": "OK"}, "Sheaf.Paper.CompactSupportLimitEquationData": {"hash": "b979c703ab44901a890d483f101b28de2bf53cc0", "status": "OK"}, "Sheaf.Paper.CompactSupportProjectionCoefficientChange": {"hash": "c00de93c9b4b6108414ad0d8b28cb61441bf5751", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarGammaIdentification": {"hash": "cc025e92de95e991214780574faf9bcb451568ce", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarLimitReduction": {"hash": "f0eba93ca050aa62762970feb3d74016b69b9b0e", "status": "INFRA"}, "Sheaf.Paper.CompletedDirectImageTargetIso": {"hash": "da8f8a15ef910102b64a9c3fcb72649bbcf7181a", "status": "OK"}, "Sheaf.Paper.CompletedScalarCanonicalAssociatorFormula": {"hash": "83977b558b3041c1ee0fedd59e4abb6c5dab8d8a", "status": "OK"}, "Sheaf.Paper.ConcreteProjectionCoefficientCoherence": {"hash": "994d54d5c81ba58bd2f938207232112e3d33159e", "status": "OK"}, "Sheaf.Paper.ConcreteProjectionFactorizationData": {"hash": "05d4cda399524a24878a0d8fe63ed1416b292885", "status": "OK"}, "Sheaf.Paper.ConstantScalarTowerAdjunction": {"hash": "c66095ab37d688e21549cc946c2a755fcb4cdcd8", "status": "OK"}, "Sheaf.Paper.DegreeZeroCompactSupportSections": {"hash": "5c2846a1d8755609b53e25e16fc10e6096219c46", "status": "OK"}, "Sheaf.Paper.DirectImageLimitComparison": {"hash": "815130c16ae3175e7377df126d2417b08f12d484", "status": "OK"}, "Sheaf.Paper.ExceptionalFiniteScalarMates": {"hash": "4168aa4eb3bb039e4b8b0d4996648abd6ba56903", "status": "OK"}, "Sheaf.Paper.ExceptionalFiniteScalarMatesData": {"hash": "ff81628ef42f87fe4cd72688930a2317e512939b", "status": "OK"}, "Sheaf.Paper.ExceptionalRingScalarMates": {"hash": "a23dbcf87e0a958ebf06e1b1678408ee15b08a63", "status": "OK"}, "Sheaf.Paper.ExceptionalRingStageAssembly": {"hash": "4a87df980c4d561050c019994e2facf132662d16", "status": "OK"}, "Sheaf.Paper.FiniteFreeProperScalarComparison": {"hash": "61cdd829d8ddb24f6dd62ae165168174a5b212b4", "status": "OK"}, "Sheaf.Paper.FiniteRingRefinementCoordinates": {"hash": "bfd2cca5df6e56576d8d9a091b9207ca491852e3", "status": "OK"}, "Sheaf.Paper.FiniteRingRefinementCoordinatesCore": {"hash": "d242c55dbbb2108655615fb131147ff96ba8c533", "status": "OK"}, "Sheaf.Paper.IntegralNormalizedRingRefinementIdentityCore": {"hash": "41d9b2197500c950c07b4fe40eaad3376889227b", "status": "OK"}, "Sheaf.Paper.IntegralOrdinaryProjectionEndpointIsoData": {"hash": "53ba64f97ae8cc5c91b93471d87afaa774f8befe", "status": "OK"}, "Sheaf.Paper.IntegralScalarIsomorphismExchange": {"hash": "37c2b9541d522fbde90ad7b000d9434b15947548", "status": "OK"}, "Sheaf.Paper.MixedCupNormalizedScalars": {"hash": "6abfeee20b4b1676ba3606ecb65e764d3422c653", "status": "OK"}, "Sheaf.Paper.NormalizedFieldPurityTrace": {"hash": "3b10314592afc55a22b3f737f950026bb4f66758", "status": "OK"}, "Sheaf.Paper.OpenProjectionFactorCoefficientChange": {"hash": "4ded23de01e3727be50bec7398b3eb1c1ab0ea89", "status": "OK"}, "Sheaf.Paper.OpenProjectionFactorCompositorTransport": {"hash": "6dc983df12eb517765c277eb40b247dd1aff27ef", "status": "OK"}, "Sheaf.Paper.OpenProjectionIsoCoefficientChange": {"hash": "c9c4836531971fb7d450f3ec3ece827e8ced472c", "status": "OK"}, "Sheaf.Paper.OperationCoefficientActionData": {"hash": "6272d89e4c25ef17ae777e8fc7a2c3e7246eb23e", "status": "OK"}, "Sheaf.Paper.OrdinaryOpenScalarComposition": {"hash": "1281f7d39688ab2b2af33ba376236bf999a9c45b", "status": "OK"}, "Sheaf.Paper.ProjectionFactorCoordinates": {"hash": "459577ed27a2be8ab62aca34f79273083dd79d3c", "status": "OK"}, "Sheaf.Paper.ProjectionFiniteReduction": {"hash": "7f646f7a6793629c9eaa822c2ac53475d5ed7e31", "status": "OK"}, "Sheaf.Paper.ProjectionScalarSquare": {"hash": "1db48faca29dd2816995789c70fbe237cbaa0ae5", "status": "OK"}, "Sheaf.Paper.ProperScalarComposition": {"hash": "b210f2942df7d67cc70467223ab96a5aab3185a0", "status": "OK"}, "Sheaf.Paper.PuritySourceTransports": {"hash": "5219f37508d5276b610bdd6868c5955c5005d8f9", "status": "SLOW"}, "Sheaf.Paper.QcqsCompactSupportFiniteComparison": {"hash": "408d3c5b3fa92e576523bda90b55001876ad0991", "status": "OK"}, "Sheaf.Paper.QcqsCompactSupportFiniteMates": {"hash": "5164c1552f50386431c320a787cf56ceebca7bd7", "status": "OK"}, "Sheaf.Paper.QcqsCompactSupportImageComplete": {"hash": "107457186293832699d102df74770d0221facc5f", "status": "OK"}, "Sheaf.Paper.QcqsCompactSupportNormalizedIsoExistence": {"hash": "de30b4c39abc3b5f6d058e23a574cc3d95a9063a", "status": "OK"}, "Sheaf.Paper.QcqsCompactSupportOpenComplete": {"hash": "6a83a6b6c54f76dd32246c13682246711b401aba", "status": "OK"}, "Sheaf.Paper.QcqsCompactSupportProperComplete": {"hash": "1d11f878b6b21cc95f8494b7286ed2f9febf6961", "status": "OK"}, "Sheaf.Paper.QcqsCompactSupportRealization": {"hash": "9206ac11cc3a0ec9a13d1cb145d01e3de0969ed3", "status": "OK"}, "Sheaf.Paper.QcqsCompactSupportStrictReductionComparison": {"hash": "ddbc1d66c1f2a89e9354dd51b75427f293cecfaf", "status": "OK"}, "Sheaf.Paper.QcqsCompactSupportStrictReductionData": {"hash": "54bc752c10e67ee1d30c3404c7f130b1cc37e94e", "status": "OK"}, "Sheaf.Paper.QcqsCompactSupportStrictReductionGamma": {"hash": "e1bfe18a6157dc6fcb29fd5b2ae2551bc6d8476f", "status": "OK"}, "Sheaf.Paper.RationalPurityCoefficientModels": {"hash": "2360ef94f675ae17f9bc11607ffa0ae946ad361a", "status": "OK"}, "Sheaf.Paper.RationalPurityScalarModels": {"hash": "2fe0a2d8a75bf59a5d4759c92c4bc8249d0a6377", "status": "OK"}, "Sheaf.Paper.RationalSmoothPurityCanonical": {"hash": "2430a765f47401bf90e0fc5e77750537c4322789", "status": "SLOW"}, "Sheaf.Paper.RationalSmoothPurityFiniteTrace": {"hash": "0132a3d1f91d1f330b047db225dbada3544e07a2", "status": "OK"}, "Sheaf.Paper.RefinementOpenRestriction": {"hash": "380a131577b6b214adc0dfa01534fd7a2fabe52c", "status": "OK"}, "Sheaf.Paper.RefinementOpenRestrictionData": {"hash": "de2fb28cb23976504cf08e53bb077eca3bb88408", "status": "OK"}, "Sheaf.Paper.RelativeProductFactors": {"hash": "81251d108f829a008b298f2f1b94bfc4c7f919d1", "status": "OK"}, "Sheaf.Paper.RingEndpointScalarIdentityTransferData": {"hash": "3d76cfab81e246345851491328892e81fa766c7f", "status": "OK"}, "Sheaf.Paper.ScalarComplexAdjunctionNormalization": {"hash": "7b383889398335cb5e895ae3bd3c36bd1271bf48", "status": "OK"}, "Sheaf.Paper.ScalarGeometricPullComposition": {"hash": "3c4cee2ba8a7fd261d883cd40205ac8682f63c64", "status": "OK"}, "Sheaf.Paper.ScalarPullCoefficientComplexNormalization": {"hash": "fc355dfdba6d19d83778a51efff736f3d421396b", "status": "OK"}, "Sheaf.Paper.ScalarPullTensorCoefficientCoherence": {"hash": "f98c214d4cc40aa3e0eca510a86af7c2393461ed", "status": "SLOW"}, "Sheaf.Paper.ScalarRestrictionComplexNormalization": {"hash": "87c6c6fd750782aa2f3f6ad81305a8b24b20e84c", "status": "OK"}, "Sheaf.Paper.SfRecollementReductionBoundary": {"hash": "3e5eb049e528ed51a96a3b71024b90d9c96825a0", "status": "OK"}, "Sheaf.Paper.SixFunctorOperationDatumStages": {"hash": "c6a5374ac0ebaa23c6bdbe74ffe1761e38933915", "status": "OK"}, "Sheaf.Paper.StrictCoefficientOpenReduction": {"hash": "f1876e5850729fb357c5383e1e10d271de8ceee3", "status": "OK"}, "Sheaf.Paper.StrictCoefficientProperReduction": {"hash": "af1b9e0414718a8ef63be5b6a97a56a08b0f1d29", "status": "OK"}, "Sheaf.Paper.TowerPurityRealizedData": {"hash": "48a3c43647f30e5b85d3ad06b7ebe334a902b04d", "status": "OK"}, "Sheaf.SecSmoothPurity.AdicScalarTraceCoherence": {"hash": "bcc2dcd140be9b2e2c9e24e12af0eb748364f8dc", "status": "SLOW"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels": {"hash": "315bf5ae6984c62b3462787294e26b4b4d829a62", "status": "OK"}, "Sheaf.SixFunctors.FiniteFreeEtaleProEtaleTransport": {"hash": "1b7da415acda7246a245762e45cd44525c67c00f", "status": "OK"}, "Sheaf.SixFunctors.FiniteScalarMateData": {"hash": "6d833127857194ca1793a47e528ebd6b11472d2d", "status": "OK"}, "Sheaf.SixFunctors.FiniteScalarOrdinaryReductionIso": {"hash": "566c1b31348c5d3e440c256e3667980c6ecea3bd", "status": "OK"}, "Sheaf.SixFunctors.FiniteScalarPullComplexPresentation": {"hash": "b1fb5b21daba22ff90394c99cadd8d9c0c32dfdc", "status": "OK"}, "Sheaf.SixFunctors.FiniteScalarPullPbcNormalization": {"hash": "acfb45fe6e37d9e85f41a36ba0a1a5ca524a9f86", "status": "OK"}, "Sheaf.SixFunctors.FiniteScalarPullPresentation": {"hash": "5aaee8f578269f889b5d4827e3588502c348f976", "status": "OK"}, "Sheaf.SixFunctors.FiniteScalarPullReductionComparison": {"hash": "c4d3770db39e9be97bb4608d8b57df1f97591bf8", "status": "OK"}, "Sheaf.SixFunctors.IntegralCompactificationRealizationData": {"hash": "d7df0aa3356c36a6db8219220d2a265cef16dba5", "status": "OK"}, "Sheaf.SixFunctors.IntegralFinitePullbackCoordinates": {"hash": "fa0ce0393a53a8e0a6edb3c5c245fc8edb50d083", "status": "OK"}, "Sheaf.SixFunctors.IntegralFiniteScalarPullCochainModel": {"hash": "9b8b57ec691664e47405ee1f17e3b116a0cc4488", "status": "OK"}, "Sheaf.SixFunctors.IntegralFiniteScalarPullOrdinary": {"hash": "b388f2f27a64145e6929893b54426d4effd7e56b", "status": "OK"}, "Sheaf.SixFunctors.IntegralOpenFiniteEvaluation": {"hash": "496559d2a2ea41e6c76fed2df4bed9646ac6d833", "status": "OK"}, "Sheaf.SixFunctors.IntegralOpenScalarUnitSquare": {"hash": "f4c93ad5a117b46f92d04aa41d4232c3f23ef079", "status": "OK"}, "Sheaf.SixFunctors.IntegralProperFiniteProjection": {"hash": "0e310b77ca12a8a4de992188449bd11fbd785035", "status": "OK"}, "Sheaf.SixFunctors.IntegralReductionPullEvaluationQuotient": {"hash": "87b53355d628725de88516652134ba0b270d2d52", "status": "OK"}, "Sheaf.SixFunctors.IntegralReductionPullFiniteSquare": {"hash": "2f5be402f2b42300dddd79d61cf4ce34c49688a0", "status": "OK"}, "Sheaf.SixFunctors.IntegralReductionPullOrdinarySquare": {"hash": "3efb640435aeb3be402b1ea26b6e158b238b36bd", "status": "OK"}, "Sheaf.SixFunctors.IntegralScalarTensorIdentity": {"hash": "6b74a29b4fbb6565ec1cdcf1dca17758b6da6fc7", "status": "OK"}, "Sheaf.SixFunctors.IntegralSupportProjectionTransport": {"hash": "4652ac4321d817ef5a5a7c0aa7c2c50a5c4df44f", "status": "OK"}, "Sheaf.SixFunctors.NormalizedRingCompactScalarCocycle": {"hash": "648fbecf3c3ea3f595975abd71c05e6d2b1cf76d", "status": "OK"}, "Sheaf.SixFunctors.OpenClosedWeilMateData": {"hash": "9630df99472a0f41c00bc0768460c09c74bc07ae", "status": "OK"}, "Sheaf.SixFunctors.OpenFactorCoherence": {"hash": "40ec5b9e9aebdb322607072e367e522ba8fe214e", "status": "OK"}, "Sheaf.SixFunctors.OpenFactorCoherenceData": {"hash": "75c8a26c3fc5105d0a8b8bbaba765378b3e081e1", "status": "OK"}}, "seconds": 527, "time": "2026-10-28T12:36:00+0800", "transitive": 0, "version": 1}
```

## Second reading by D3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
