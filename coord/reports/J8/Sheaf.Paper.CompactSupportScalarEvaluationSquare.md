## What changed

Replaced the proof hole in `systemCompactScalar_evaluation_square` by an explicit
construction and proper/open pasting argument. Its complete signature and the
existing `systemCompactEvaluation` definition are unchanged. No adopted source
module is modified.

Added `Sheaf.Paper.SystemScalarFiniteEvaluation`: quotient compatibility and
uniqueness identify the generic system coefficient map with the recorded map.
The existing normalized universal cochain scalar package supplies the adjunction
of the fixed system model. Adjoint uniqueness transports the existing generic
scalar evaluation comparison to that model and to the fixed finite scalar model.
Every declaration of this new module is proved; no object is supplied by a new
existence hole.

Added `Sheaf.Paper.SystemProperScalarEvaluation` and
`Sheaf.Paper.SystemOpenScalarEvaluation`. They define the actual finite scalar
transposes and the specified geometric evaluation isomorphisms, and isolate the
two geometric-factor compatibility equations. The main module imports these
privately. Its private finite-factor lemma uses the existing scalar-transpose
pasting theorem through private imports of `FiniteCompactSupportScalarTransport`
and `FiniteCompactScalarConstructible`.

The assembly is explicit: naturality of direct-image evaluation moves the open
scalar map, functoriality applies the open equation, the direct-image equation
applies, and naturality of the finite direct scalar map moves the open evaluation.
The proved finite-factor lemma then identifies the composite with the specified
`intrinsicCompactScalar`. A private generic arrow-pasting lemma encapsulates the
composition rewrites before specialization to the large sheaf-category types.
The assembly is proved for arbitrary scalar comparisons and then specialized to
`systemScalarFiniteEvaluation`; this avoids repeated kernel reduction of the
concrete normalized construction. The identical assembled proof compiled in
22.1 seconds during profiling. All profiling options and debug modules are
removed from the delivery; the delivery command checks the final files again.

## Proved and sorry left

This is a decomposition, not a sorry-free solution: one existing hole is closed
and two strictly smaller geometric-factor holes are added (net minus one).

Closed in the item:
`WeilConjectures.FrobeniusExchange.systemCompactScalar_evaluation_square`
(`lem-sf-compact-scalar-evaluation-square`). The item now contains zero holes.

Proved without new holes in `SystemScalarFiniteEvaluation`:
`scalarQuotient_compatible`, `scalarSystemMap_eq`,
`finiteEvaluationSystemScalarModel_exists`,
`finiteEvaluationSystemScalarAdjunction`, and `systemScalarFiniteEvaluation`.
The private lemma `finiteCompactScalar_factors` and the proper/open assembly are
also fully proved.

Every new remaining hole, by full declaration name:

- `WeilConjectures.FrobeniusExchange.systemDirectScalar_finiteEvaluation`,
  in `Sheaf.Paper.SystemProperScalarEvaluation`, node
  `lem-sf-system-proper-scalar-evaluation`.
- `WeilConjectures.FrobeniusExchange.systemOpenScalar_finiteEvaluation`,
  in `Sheaf.Paper.SystemOpenScalarEvaluation`, node
  `lem-sf-system-open-scalar-evaluation`.

Both are equations for one geometric operation with the fixed, already
constructed scalar comparison. Neither states the compact-support equation,
chooses its existential witness, or assumes a repackaging of that equation.
The direct-image lemma does not assert invertibility of the scalar mate.
The open lemma assumes only the open immersion required to define its operation.
Their docstrings include their sources and proofs in words. The construction and
equations include n=0, zero objects, empty schemes and identity embeddings;
no quotient-flatness, boundedness or constructibility assumption was introduced.

## No longer needed

No existing module is withdrawn and no global pruning is claimed. Both original
public imports remain unchanged. The original proof's scalar-system and finite
restriction dependencies remain needed transitively through the three new
modules and the finite-factor lemma. The updated item's direct proof dependencies
record the actual construction, factor equations and pasting, rather than
pretending that the unspecialized generic scalar declarations alone supply the
geometric equations. No public import or maintainer tool approval was removed.

## Where the brief, the DAG or earlier work was wrong

The current server queue assigns a proof item. Its historical build-error record
names imports, but the unchanged source compiles against the published artifacts;
this delivery does not treat that fact as a repair of newer dependencies.

The existing plan describes the correct proper/open calculation but does not
supply a Lean declaration asserting either specialized equation for the fixed
system and finite models. Existing generic evaluation, adjoint-uniqueness and
mate-pasting results suffice to construct the scalar comparison and assemble the
compact equation. The two remaining specialized compatibility calculations are
now explicit separate statements. In particular, the compact equation is not
split off again under another name. No target or existing intermediate statement
has been changed, and the unit route is preserved.

## New nodes

`lem-sf-system-scalar-finite-evaluation` records the completely implemented scalar
evaluation construction in `Sheaf.Paper.SystemScalarFiniteEvaluation`, including
the quotient-map identification and fixed-model normalized adjunction.

`lem-sf-system-proper-scalar-evaluation` records the direct-image scalar
compatibility equation in `Sheaf.Paper.SystemProperScalarEvaluation`.

`lem-sf-system-open-scalar-evaluation` records the extension-by-zero scalar
compatibility equation in `Sheaf.Paper.SystemOpenScalarEvaluation`.

All three inherit the item's chapter, unit and blueprint source chain. The
original node's proof, proof dependencies and proof origin follow the Lean
assembly. No existing definitions or statements were repaired, so no change
record or consumer adaptation is required.

## Related modules compiled before delivery

128 related module(s) compiled against this delivery by deliver3.py: 121 OK, 7 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportScalarEvaluationSquare": "4873c6b3e3219cb09a4e30281962b19eb1d15711", "Sheaf.Paper.SystemOpenScalarEvaluation": "6e07a56ca277151f3881232e09031af85bbbfd2b", "Sheaf.Paper.SystemProperScalarEvaluation": "1f7d6a445710d2a9cf92b7ca384a14e62321e42e", "Sheaf.Paper.SystemScalarFiniteEvaluation": "21b8f7304805f47c81050478adb2f933eaaf18af"}, "results": {"Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction": {"hash": "5bbf58935097325495174dfd8cead09adad762f1", "status": "OK"}, "Sheaf.Paper.ClopenCanonicalFiniteEvaluation": {"hash": "115fc4aed694964474dd605fefc905519f2ded91", "status": "OK"}, "Sheaf.Paper.ClopenCanonicalRestrictionEvaluation": {"hash": "4bbad6be2a2963f186131adc37f4341c0d3f5c3b", "status": "OK"}, "Sheaf.Paper.ClopenCompletedTowerRestriction": {"hash": "0eed9f4055ccf08157dc90541286ad4c52156e6b", "status": "OK"}, "Sheaf.Paper.ClopenExceptionalScalarDescent": {"hash": "6f93085f7a982f8809424c4b14233af4b04c4278", "status": "OK"}, "Sheaf.Paper.ClopenSystemFiniteRealization": {"hash": "7cda7bba6e93799650528498da5862e667e9ef83", "status": "OK"}, "Sheaf.Paper.ClopenSystemIntegralRealization": {"hash": "998d2e4ad1aa1c9352798580ac478e7d33df9691", "status": "OK"}, "Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization": {"hash": "99558f7a44c40e2c845c30b968dd207d7d0dc81c", "status": "OK"}, "Sheaf.Paper.ClopenSystemRealizationData": {"hash": "5b68a62e6bf883c4b420078269a234e6ce5a902f", "status": "OK"}, "Sheaf.Paper.ClopenSystemRestrictionEvaluation": {"hash": "2f5b7fcf374ed240681b789149a95678c82847f1", "status": "OK"}, "Sheaf.Paper.CompactSupportSystemRealizationNormalization": {"hash": "3d61967d7537aa959d68b7f6983cffadfe893a0e", "status": "OK"}, "Sheaf.Paper.CompactSupportSystemScalarFiniteInvertible": {"hash": "bf2d428065bfe5b8537e64f154bbaeaa1f0ab8f1", "status": "OK"}, "Sheaf.Paper.CompactSupportSystemTransposeNormalization": {"hash": "25b428d31c12c81a616cb1dc001f3fb83a593541", "status": "OK"}, "Sheaf.Paper.CompletedStalkReparametrizationCoherence": {"hash": "3769ac8ecd9d11517676a2557ac9b94803bea04f", "status": "OK"}, "Sheaf.Paper.CondensedIntegralEndpoints": {"hash": "dd232434d5a5e3148db6a3d554ab119400d15d77", "status": "OK"}, "Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons": {"hash": "a09ffd92bfcb32abe2cfcdf4d36409c922bbff13", "status": "OK"}, "Sheaf.Paper.ExceptionalBaseChangeIntegralMaps": {"hash": "ddba29e6fa7e3139891c565fdbd1b35e93f330d1", "status": "SLOW"}, "Sheaf.Paper.FieldOrientationSystemComparison": {"hash": "e493085b773fc372045148189085652d1b924450", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemComparisonData": {"hash": "97d81f9bdad7450a1e62daa9216f167abc5a0124", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemCoordinates": {"hash": "14fe2d2274a0f77c19cbfcaa3f2fd61332279406", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemFiniteOrientation": {"hash": "eb0e96fdd2f148cfa9bfa178452d4305f8ea3ca7", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemHeart": {"hash": "9a070f47bd829208725e5f5eeee2aac22cacda63", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemNormalizations": {"hash": "e22be0a0e93d29067a2ae0db451474bb52136641", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemRigidity": {"hash": "18765b5e9e7e37f176463311133d1039cd0b9129", "status": "OK"}, "Sheaf.Paper.FieldPuritySystemTranspose": {"hash": "76d579b774387bd695951bbf5d80a728fd3f189f", "status": "OK"}, "Sheaf.Paper.FieldPuritySystemTransposeBase": {"hash": "0882a7a028b9479a0000159cb4ff3ff179ff9277", "status": "OK"}, "Sheaf.Paper.FieldPurityTransposeArrows": {"hash": "bd6e29a7c71ad614a10743bd1517519239715b5d", "status": "OK"}, "Sheaf.Paper.FieldPurityTransposeLevelWords": {"hash": "d261fe7d404f063aa06890a477215a246d53f6ac", "status": "OK"}, "Sheaf.Paper.FieldWeilShriekShiftData": {"hash": "5c0b9354c99c9e73728a547bd4397bc11046c209", "status": "SLOW"}, "Sheaf.Paper.FiniteGammaEvaluationIsIso": {"hash": "7399b04e1cb09b13b71b32a5c04292d5061883b4", "status": "OK"}, "Sheaf.Paper.FiniteRestrictionDiagramNaturality": {"hash": "81365072e344a50c7cddc314c30b496374b0359e", "status": "OK"}, "Sheaf.Paper.FixedPresentationUniformizerReductions": {"hash": "2195e8aeb4868a9a702ababa433fe6e635c0b07e", "status": "OK"}, "Sheaf.Paper.GeometricSmoothReconstructionSetup": {"hash": "d5f8abc24f480c3f5afd7ca4f7437295faaef56c", "status": "OK"}, "Sheaf.Paper.IntegralGeometricComparisonData": {"hash": "cc2707568a162b346675b69ebc8591da39fe2c52", "status": "OK"}, "Sheaf.Paper.IntegralGeometricComparisonRealization": {"hash": "e2edc201638183226483011a57348a50acc201a4", "status": "OK"}, "Sheaf.Paper.IntegralGeometricPurityRealization": {"hash": "0b3aa89bec9034609abf2e195b105fef87d9a785", "status": "OK"}, "Sheaf.Paper.IntegralGeometricReindexingRealization": {"hash": "dc82db56836939bdf56488314584512a9aad340d", "status": "OK"}, "Sheaf.Paper.IntegralGeometricSupportRealization": {"hash": "9ba359469968ecca14a23af8cb500f18fb9dd9c6", "status": "OK"}, "Sheaf.Paper.IntegralGeometricTransposeIdentity": {"hash": "1ae653a0bbd43cc9d3515b58d0ae07ae3f6015a9", "status": "OK"}, "Sheaf.Paper.IntegralReconstructionComparisons": {"hash": "ff879e514ff031ee4466f415e7008cada241790e", "status": "OK"}, "Sheaf.Paper.NormalizedIntegralTraceData": {"hash": "f7c116653c7faa062b478b61abb0a121463a5af7", "status": "OK"}, "Sheaf.Paper.OrderedLineLevelBounds": {"hash": "5f72ca8d9be8baf15de4529cd0c1467486cdb2d3", "status": "OK"}, "Sheaf.Paper.OrderedTowerOrientation": {"hash": "99343b2d44ec92787450dc6ec2604ea4e9142b7d", "status": "OK"}, "Sheaf.Paper.OrientationScalarTowerTransport": {"hash": "322b312084978e6ab9be061d3acdf23b186ec025", "status": "OK"}, "Sheaf.Paper.PointFiniteMultiplicationInverse": {"hash": "a4b5b2d4cacbe433e6d876caab9bbb6c8f834a72", "status": "OK"}, "Sheaf.Paper.PointFrobeniusNormalizationDefinitions": {"hash": "db21333caa57619484e89dfa96015e7de9574c20", "status": "OK"}, "Sheaf.Paper.PointFrobeniusTransportNormalization": {"hash": "ab700a1f62ac6fd61fa24fa34926ca464b09ba13", "status": "OK"}, "Sheaf.Paper.PointIdentityExchangeRecipe": {"hash": "975135da04a1e6d6828b466b7ca510e514ce83d5", "status": "OK"}, "Sheaf.Paper.PointPowerRoosComparisonSpecialization": {"hash": "2878ccb4019cc668db90359eb9e5bbd42e273486", "status": "OK"}, "Sheaf.Paper.PointPowerStrictInsertionSpecialization": {"hash": "ae5192efc9a4cc63b9e2865b60777de6b38e12ea", "status": "OK"}, "Sheaf.Paper.PointPullbackConeLocalization": {"hash": "6c3bb7f59873187d064b20726b5831b35dd6b9a3", "status": "OK"}, "Sheaf.Paper.PointQuotientComparisonCoordinates": {"hash": "c08325c333aba6cdc87ed1847abc17ddd4fe8b07", "status": "OK"}, "Sheaf.Paper.PointRestrictionWholeRoosSquare": {"hash": "eb5799b2c6579fdc42f87333fb32d36d5901a9fe", "status": "SLOW"}, "Sheaf.Paper.PointSectionsCompletionCone": {"hash": "97562935f210f54382513687d9ee98febf55a092", "status": "OK"}, "Sheaf.Paper.PointSystemNormalizedComparisonData": {"hash": "fa2a72ec24d2f533c7d6bc737477c3a7a1f63c0a", "status": "SLOW"}, "Sheaf.Paper.PointSystemPowerRoosCoherence": {"hash": "a95c004dc75bad66532502d35076a1b901be5509", "status": "OK"}, "Sheaf.Paper.PointSystemPowerRoosData": {"hash": "91259c14ac7acb42ade3398312360eba52da7357", "status": "OK"}, "Sheaf.Paper.PointSystemRoosComparisonAssembly": {"hash": "a36175a294d36429f9f80b35e80e2ad66fef67e4", "status": "OK"}, "Sheaf.Paper.PointSystemRoosRestrictionAssembly": {"hash": "3fe0291ea6e88f3b35ff3b882413d4c678247573", "status": "OK"}, "Sheaf.Paper.PointSystemRoosTransport": {"hash": "ff0b38a35b160953746792a446a4ab94660fed1e", "status": "OK"}, "Sheaf.Paper.PointSystemRoosTransportData": {"hash": "6d0f8399764aa514a9c53586faf82f7343d009f3", "status": "OK"}, "Sheaf.Paper.PointSystemRoosTransportRepresentative": {"hash": "a21cfc9def0b03581549c409beb0f68413e89394", "status": "OK"}, "Sheaf.Paper.PointSystemTransportDescent": {"hash": "fe5c14012eecaee813a2e56e0799d8acf918a2e0", "status": "OK"}, "Sheaf.Paper.PointTransportConeComparisonDescent": {"hash": "727b08db5a88dd605153a81b4bf995d7dce4d9ff", "status": "OK"}, "Sheaf.Paper.PointTransportResolutionCancellation": {"hash": "4ce4a9d815a7cca085002a1d8d65d768d21d9454", "status": "SLOW"}, "Sheaf.Paper.PurityConjugatesTowerReduction": {"hash": "1e086facd08a557ee70cd2b11daed249cb5fb1fd", "status": "OK"}, "Sheaf.Paper.PurityFiniteReductionTransport": {"hash": "bc622c3185cb59358dd7f8e7929fd9b6f2f8afe6", "status": "OK"}, "Sheaf.Paper.PurityPullbackLevelBounds": {"hash": "6ea155b44a709e8e23091cc0afc8ce2b286335a5", "status": "OK"}, "Sheaf.Paper.PurityPullbackReductionTransport": {"hash": "49fb368f9bc4b67444caa0756750e0b77b22eef5", "status": "OK"}, "Sheaf.Paper.PurityTowerReductionComparisons": {"hash": "a116ef52274ded289b1c2ab3b825696d5255418e", "status": "OK"}, "Sheaf.Paper.RamifiedScalarSystemTranspose": {"hash": "53ac490826ec5a0fa35c7c8f9a5ca4c9b3fca77d", "status": "OK"}, "Sheaf.Paper.ResidueCompatiblePullbackFrobenius": {"hash": "3809fb3bf7cf447f73328d73f4943b7fdf05fed4", "status": "SLOW"}, "Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange": {"hash": "6f30c11dc8ec3387ce795d19d5615b4637267f9b", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerGamma": {"hash": "5acba5c62f3ee60c4f89317ea0ebbe0014833afb", "status": "SLOW"}, "Sheaf.Paper.SmoothPurityTowerGammaData": {"hash": "3faa678db6f55cda2c50b35f9edb2522aed87431", "status": "OK"}, "Sheaf.Paper.SourceSectionAutomorphismModel": {"hash": "682ceaa72e8e19a9174a91290fad263da9244d24", "status": "OK"}, "Sheaf.Paper.SourceSectionIdentityModel": {"hash": "e7dfc0a142817f3482fea3dd060e69811b3587ce", "status": "OK"}, "Sheaf.Paper.SourceSectionRestrictionModel": {"hash": "baa5c4e341ee3f6e858c423fb5250abee5719c43", "status": "OK"}, "Sheaf.Paper.SourceSectionStalkConeComparison": {"hash": "6331dc588da6367d9469c378c78c78deaed0b9f9", "status": "OK"}, "Sheaf.Paper.SourceSectionStalkConeData": {"hash": "8639abd470fe2a836d0acb062d53be6573c6e1d7", "status": "OK"}, "Sheaf.Paper.SpecifiedTowerAdjunctionCharts": {"hash": "a48d6289d794e566bc76098a6213eef9ece33155", "status": "OK"}, "Sheaf.Paper.SystemScalarBasisDistributivity": {"hash": "d1e277ef767e0f140397fd95175d477b01bfab8d", "status": "OK"}, "Sheaf.Paper.SystemScalarProjectionData": {"hash": "6e6a70ab41d6f19ceee232ba81eb824f4b6f89c8", "status": "OK"}, "Sheaf.Paper.SystemScalarProjectionIdentification": {"hash": "1c756cefdef2387f213274b53f0077c897f22016", "status": "OK"}, "Sheaf.Paper.SystemScalarRefinementRestriction": {"hash": "ddecac2836e96c2ff72d7facaa63210ecf22337a", "status": "OK"}, "Sheaf.Paper.SystemScalarTensorConstituents": {"hash": "096756fb6038c07c81567f421c86a658ef0c40a6", "status": "OK"}, "Sheaf.Paper.TensorTransposeFiniteEvaluation": {"hash": "2747fdf31112a4c3a3e19ac5d06b7568f27fdf20", "status": "OK"}, "Sheaf.Paper.TensorTransposeTowerNaturality": {"hash": "0a067dc359f6b0bbf18ecaa7a0ddd6e18fc71061", "status": "OK"}, "Sheaf.Paper.TowerGeometricPurityAssembly": {"hash": "0c61068a11023e1f3414c29eda621862a82991bb", "status": "OK"}, "Sheaf.Paper.TowerGeometricPurityData": {"hash": "ed87f8b9b06e73ceae670bcf6c4d5efb190ad45b", "status": "OK"}, "Sheaf.Paper.TowerGeometricPurityMate": {"hash": "5148d3e17b63f01e577b8a194970f03cbc3065cd", "status": "OK"}, "Sheaf.Paper.TowerIsomorphismPullback": {"hash": "017c2bf54510d71e12db382735abbfc2d2ac40da", "status": "OK"}, "Sheaf.Paper.TowerNormalizationPreservation": {"hash": "1885f0cb5c93f66cc64ed000402c2d6d74ce18d8", "status": "OK"}, "Sheaf.Paper.TowerOrientationEvaluation": {"hash": "8705c45aebd6d1ea6a6fe504576b8c30baaba78c", "status": "OK"}, "Sheaf.Paper.TowerOrientationWordNormalization": {"hash": "97abe3d31b6ee4ed5f46d6370e95a616eca74995", "status": "OK"}, "Sheaf.Paper.TowerPurityPresentationRetagging": {"hash": "b2571a7d3262d6e579352822e236d226529aac30", "status": "OK"}, "Sheaf.Paper.TowerSemilinearPurityFactors": {"hash": "8719bba6ca94b52eb9e12182c593ee391f39961d", "status": "OK"}, "Sheaf.Paper.TowerTensorPresentationRetagging": {"hash": "af1e0b391289cc4aabadff640afc28538a5a9746", "status": "OK"}, "Sheaf.Paper.TowerTensorTransposeEvaluation": {"hash": "a47c26025f99b360a1796e9227faaf10a3b816db", "status": "OK"}, "Sheaf.Paper.TowerTensorTransposeWords": {"hash": "7651e3f44fb3fedc396bf3a3849fe75be73b6b36", "status": "OK"}, "Sheaf.Paper.TransportCondensedStageRealization": {"hash": "f8323086ff6e7137688f677c6b511811ad4fe164", "status": "OK"}, "Sheaf.Paper.TransportIntegralBaseChangeRealization": {"hash": "41279c82fb72a9f1781669c5bea4f75d167c5e20", "status": "OK"}, "Sheaf.Paper.TransportIntegralChartRealization": {"hash": "88cf176d90d5ec739ff0b920c34172ef3c69e24f", "status": "OK"}, "Sheaf.Paper.TransportIntegralCompositionRealization": {"hash": "38a24cd4b0bc9510d17ddebd74c653bca11b0693", "status": "OK"}, "Sheaf.Paper.TransportIntegralCounitRealization": {"hash": "362789f01525bd317330b272608a9f8d1b5f57d3", "status": "OK"}, "Sheaf.Paper.TransportIntegralStageConstruction": {"hash": "80d4d6ba6379bc0c6e16c865a1516facb64b28ed", "status": "OK"}, "Sheaf.Paper.TwistedPullbackTowerDomain": {"hash": "707eb28c771ca3083afffa07cdfbdba735f46fe5", "status": "OK"}, "Sheaf.Paper.TwistedPullbackTowerDomainDefinitions": {"hash": "6632aecdf649f0d15eab12e57540459901c0851c", "status": "OK"}, "Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient": {"hash": "dfa51ac9440dcdc04735a277ffeb597ad3cbd85d", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteDualizingCoherence": {"hash": "33e6258868e735e99734a98c2ddda6fb4b2830e1", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtension": {"hash": "a80bce78cffaf702f091a3521d667088921b08f8", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionCocycles": {"hash": "532a5085aec183e999489631bbf2213dffa2918e", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore": {"hash": "0a1aee71c28d60cfb9a9acf7830178acf5b1b529", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility": {"hash": "7da3a8e08d0e78133a5c35595921e680f5ee5142", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels": {"hash": "315bf5ae6984c62b3462787294e26b4b4d829a62", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing": {"hash": "9da7a6277038cc55900ad0956103673a862edcd4", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralScalarQuotientTransition": {"hash": "0a6961873089daa947760cc01f9a656f94d59525", "status": "OK"}, "Sheaf.SixFunctors.CoefScalarReductionExchange": {"hash": "c9ebe335e63f42afaec1d952de4f53755494da50", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralNormalizedAdjunction": {"hash": "dc3510828603f0e52ff4d7a2249b3f08c25fa75c", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralRealizationAssembly": {"hash": "029bbfb7a3f95cade80e36f8432d666abf17022a", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstruction": {"hash": "ecfed2c7ccc5b634e5234ed5d7238a3c6e1b0b1d", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstructionEquivalence": {"hash": "ba3c7868a918eff9ff9e82173364432b81326775", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces": {"hash": "dfd7491b122f1402fa3e5e5f1ca4f2b05228ee34", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralSystemExistence": {"hash": "3a2762881292a445abf50cc8f61fb3b3c0be90cb", "status": "OK"}, "Sheaf.SixFunctors.FiniteReturnFrobeniusCancellation": {"hash": "1b25b3681c9f2d1c6aa3cca1f4c67b2175908d86", "status": "OK"}, "Sheaf.SixFunctors.IntegralOperationShiftData": {"hash": "d79d356f094f2fb511f9e0bde2182c3cf96581b4", "status": "OK"}, "Sheaf.TraceFormula.LocalNormalizationStrictRealization": {"hash": "d80b1639021816dcdad1dc32e586a5d79de75bb7", "status": "OK"}, "Sheaf.TraceFormula.PointConeLiftsChainNaturality": {"hash": "824a39258ca4fa220e8773adc5c66042e1b6165d", "status": "OK"}}, "seconds": 728, "time": "2026-10-28T01:10:17+0800", "transitive": 127, "version": 1}
```

## Second reading by J8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
