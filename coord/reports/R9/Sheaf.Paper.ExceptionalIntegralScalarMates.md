## What changed

Implemented `WeilConjectures.ExceptionalIntegralScalar.ramifiedRecovery` by assembling
normalization, actual adjunction isomorphisms and the original four uniform bound
endpoints. Its signature and the `Recovery` record are unchanged.

Added three supporting modules, imported privately by the item:

- `Sheaf.CategoryTheory.SystemSelectedAdjunctionIsos`: fully proves invertibility
  of the actual selected-extension unit for every selected system, and of the actual
  counit for every normalized full system. The proof uses the supplied normalized
  transpose equations, tensor unit and joint detection of isomorphisms.
- `Sheaf.CategoryTheory.SystemSelectedNormalization`: fully proves preservation of
  all transition-adjoints by restriction and recovery. Representative normalization
  first identifies the supplied transitions/evaluation comparisons with the canonical
  ones. The existing transition composition and subsequence coherence equations,
  transposed by `adjunctionTransition_coherence`, treat arbitrary m≤n, including
  repeated next indices. No new coherence assumption is introduced.
- `Sheaf.Paper.RamifiedSystemRecoveryBounds`: isolates the remaining geometric
  finite-quotient bound calculation, preserving the independent cohomological [a,b]
  and Tor [c,d] intervals. Its source and full proposed proof are in its docstring.

The private, fully proved `restrictionBounds` transports constructibility, both
cohomological endpoints and the same Tor interval through actual selected evaluation.
It privately imports the existing `FiniteCtfTriangulated` theorem to install the
constructibility predicate's closure under isomorphisms explicitly.
The assembly retains the same existential bound witnesses and their inequalities.

Updated the parent's recovery step. The original core declaration and its node
remain unchanged; the parent's full scalar-mates plan cannot simply be copied to
that node because some proposed dependencies already depend on the core. No definitions,
public signatures, public imports, instances or attributes of existing modules change.
The new bounds module locally disables two general site-smallness instances whose
extra coefficient universe is undetermined at this fixed pro-etale universe; the
canonical site-smallness instance then elaborates its statement without new assumptions.

Edge cases checked mathematically: r=id (e=1), e=2 with omitted initial levels,
m=n, t(m)=t(n), zero systems, empty schemes, one-point intervals and distinct
cohomological/Tor intervals. The generic proofs require no flat coefficient maps.
For recovery bounds, quotient exponents stay positive; the minimal perfect-complex
argument uses the nonzero socle at the lowest degree and Nakayama at the highest
one, rather than conflating the cohomological and Tor endpoints.

## Proved and sorry left

Eliminated the original body hole of
`WeilConjectures.ExceptionalIntegralScalar.ramifiedRecovery`
(node `lem-sf-exceptional-integral-scalar-mates`). This is a decomposition into one
strictly smaller bound theorem, with the categorical adjunction and normalization
calculations fully proved. It is not claimed as a net hole reduction.

New proved public declarations, with no reachable new holes:

- `SheafOfModules.systemSelectedAdjunctionIsos`
  (`lem-pur-system-selected-adjunction-isos`).
- `SheafOfModules.systemSelectedNormalization`
  (`lem-pur-system-selected-normalization`).

The delivery has exactly these two remaining holes:

- Unchanged `WeilConjectures.ExceptionalIntegralScalar.exceptionalIntegralScalarMates_core`
  (`lem-sf-exceptional-integral-scalar-mates-core`).
- New `WeilConjectures.ExceptionalIntegralScalar.ramifiedSystemRecoveryBounds`
  (`lem-sf-ramified-system-recovery-bounds`).

Validation: the two categorical modules compile cleanly (8.7 s and 11.5 s),
the bounds module compiles cleanly (10.0 s), and the item compiles cleanly (40.6 s).
All compiles used the required server compiler; no local library build was run.
The first delivery compatibility run recorded 94 OK and 2 SLOW among 96 related
modules. SLOW is retained as a validation limitation, not called a passing compile;
the delivery tool records module-by-module evidence for the independent reviewer.

Original module: two holes before, one after. Delivery: one original hole closed,
one lower hole added; net zero. `exceptionalIntegralScalarMates` remains proved by
its existing core application and explicit arithmetic ramified-map witness.

## No longer needed

No original module or node is withdrawn. Every original public import is retained
for the existing interface. The scalar-mates obligation remains at the core hole;
no geometric scalar
mate, reconstruction, shift or unit-route dependency is pruned. The fully proved
categorical recovery argument needs only the given left-extension theory, not an
extra existence theorem for another choice of theory.

## Where the brief, the DAG or earlier work was wrong

The current server queue identifies this as a proof item with two holes, not a
zero-hole repair; its historical bad-import build log predates the current source.
The original core node has no proof dependencies. Copying the parent's ten-step
plan onto it was rejected by preflight: integral reconstruction and integral
realization shift coherence already lead back to the core through the coefficient
construction. That attempted metadata change and its expanded core docstring were
reverted. The inherited core-plan issue is reported here for its future proof work.
The new bounds node cites the coefficient-field and finite-field definitions,
rather than the aggregate exceptional-adjunction construction, and its finite-free
calculation does not assume any exceptional scalar-mate theorem.

The previous step-2 explanation said the unit Tor test preserves the original
cohomological interval. That test only supplies the Tor endpoints. The new bound
statement keeps all four endpoints and spells out the additional Artinian perfect
stalk argument required for the separate cohomological interval.

## New nodes

`lem-pur-system-selected-adjunction-isos` records the fully proved categorical
unit/counit calculation for an arbitrary given selected-extension theory.

`lem-pur-system-selected-normalization` records the fully proved normalization
calculation for all transitions and arbitrary coefficient towers, using the
existing canonical transition and adjunction coherence theorems.

`lem-sf-ramified-system-recovery-bounds` records the sole new postponed step:
finite constructibility and both original uniform intervals under ramified
selected recovery. It asserts no adjunction isomorphism, no preservation of
normalization and no scalar-mate construction, so is strictly smaller than
`ramifiedRecovery`.

## Related modules compiled before delivery

96 related module(s) compiled against this delivery by deliver3.py: 94 OK, 2 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.CategoryTheory.SystemSelectedAdjunctionIsos": "b07d5bb60b4fa4d23ad92cc8383284b4cb00016c", "Sheaf.CategoryTheory.SystemSelectedNormalization": "90d17ce2b9dcba0915f5fc5b4aabfa44fb70e9f6", "Sheaf.Paper.ExceptionalIntegralScalarMates": "76e8e71b5e4ac1c15dac912e5064ece33703e39f", "Sheaf.Paper.RamifiedSystemRecoveryBounds": "d23a64a1898e9885fe1df64d24cf026527dc0c82"}, "results": {"Sheaf.AlgebraicGeometry.ClosedDirectImageStrictReduction": {"hash": "5bbf58935097325495174dfd8cead09adad762f1", "status": "OK"}, "Sheaf.Paper.ClopenCanonicalFiniteEvaluation": {"hash": "115fc4aed694964474dd605fefc905519f2ded91", "status": "OK"}, "Sheaf.Paper.ClopenCanonicalRestrictionEvaluation": {"hash": "4bbad6be2a2963f186131adc37f4341c0d3f5c3b", "status": "OK"}, "Sheaf.Paper.ClopenCompletedTowerRestriction": {"hash": "0eed9f4055ccf08157dc90541286ad4c52156e6b", "status": "OK"}, "Sheaf.Paper.ClopenExceptionalScalarDescent": {"hash": "6f93085f7a982f8809424c4b14233af4b04c4278", "status": "OK"}, "Sheaf.Paper.ClopenSystemFiniteRealization": {"hash": "7cda7bba6e93799650528498da5862e667e9ef83", "status": "OK"}, "Sheaf.Paper.ClopenSystemIntegralRealization": {"hash": "998d2e4ad1aa1c9352798580ac478e7d33df9691", "status": "OK"}, "Sheaf.Paper.ClopenSystemOrdinaryRestrictionRealization": {"hash": "99558f7a44c40e2c845c30b968dd207d7d0dc81c", "status": "OK"}, "Sheaf.Paper.ClopenSystemRealizationData": {"hash": "5b68a62e6bf883c4b420078269a234e6ce5a902f", "status": "OK"}, "Sheaf.Paper.ClopenSystemRestrictionEvaluation": {"hash": "2f5b7fcf374ed240681b789149a95678c82847f1", "status": "OK"}, "Sheaf.Paper.CondensedIntegralEndpoints": {"hash": "dd232434d5a5e3148db6a3d554ab119400d15d77", "status": "OK"}, "Sheaf.Paper.ExceptionalBaseChangeIntegralComparisons": {"hash": "a09ffd92bfcb32abe2cfcdf4d36409c922bbff13", "status": "OK"}, "Sheaf.Paper.ExceptionalBaseChangeIntegralMaps": {"hash": "ddba29e6fa7e3139891c565fdbd1b35e93f330d1", "status": "SLOW"}, "Sheaf.Paper.ExceptionalRingTransportFamily": {"hash": "8c33ecdd1037760e02e561d41a865adcaf980ee4", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemComparison": {"hash": "e493085b773fc372045148189085652d1b924450", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemComparisonData": {"hash": "97d81f9bdad7450a1e62daa9216f167abc5a0124", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemCoordinates": {"hash": "14fe2d2274a0f77c19cbfcaa3f2fd61332279406", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemFiniteOrientation": {"hash": "eb0e96fdd2f148cfa9bfa178452d4305f8ea3ca7", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemHeart": {"hash": "9a070f47bd829208725e5f5eeee2aac22cacda63", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemNormalizations": {"hash": "e22be0a0e93d29067a2ae0db451474bb52136641", "status": "OK"}, "Sheaf.Paper.FieldOrientationSystemRigidity": {"hash": "18765b5e9e7e37f176463311133d1039cd0b9129", "status": "OK"}, "Sheaf.Paper.FieldPuritySystemTranspose": {"hash": "76d579b774387bd695951bbf5d80a728fd3f189f", "status": "OK"}, "Sheaf.Paper.FieldPuritySystemTransposeBase": {"hash": "0882a7a028b9479a0000159cb4ff3ff179ff9277", "status": "OK"}, "Sheaf.Paper.FieldPurityTransposeArrows": {"hash": "bd6e29a7c71ad614a10743bd1517519239715b5d", "status": "OK"}, "Sheaf.Paper.FieldPurityTransposeLevelWords": {"hash": "d261fe7d404f063aa06890a477215a246d53f6ac", "status": "OK"}, "Sheaf.Paper.FiniteGammaEvaluationIsIso": {"hash": "7399b04e1cb09b13b71b32a5c04292d5061883b4", "status": "OK"}, "Sheaf.Paper.FiniteRestrictionDiagramNaturality": {"hash": "81365072e344a50c7cddc314c30b496374b0359e", "status": "OK"}, "Sheaf.Paper.FixedPresentationUniformizerReductions": {"hash": "2195e8aeb4868a9a702ababa433fe6e635c0b07e", "status": "OK"}, "Sheaf.Paper.GeometricSmoothReconstructionSetup": {"hash": "d5f8abc24f480c3f5afd7ca4f7437295faaef56c", "status": "OK"}, "Sheaf.Paper.IntegralGeometricComparisonData": {"hash": "cc2707568a162b346675b69ebc8591da39fe2c52", "status": "OK"}, "Sheaf.Paper.IntegralGeometricComparisonRealization": {"hash": "e2edc201638183226483011a57348a50acc201a4", "status": "OK"}, "Sheaf.Paper.IntegralGeometricPurityRealization": {"hash": "0b3aa89bec9034609abf2e195b105fef87d9a785", "status": "OK"}, "Sheaf.Paper.IntegralGeometricReindexingRealization": {"hash": "dc82db56836939bdf56488314584512a9aad340d", "status": "OK"}, "Sheaf.Paper.IntegralGeometricSupportRealization": {"hash": "9ba359469968ecca14a23af8cb500f18fb9dd9c6", "status": "OK"}, "Sheaf.Paper.IntegralGeometricTransposeIdentity": {"hash": "1ae653a0bbd43cc9d3515b58d0ae07ae3f6015a9", "status": "OK"}, "Sheaf.Paper.IntegralReconstructionComparisons": {"hash": "ff879e514ff031ee4466f415e7008cada241790e", "status": "OK"}, "Sheaf.Paper.NormalizedIntegralTraceData": {"hash": "f7c116653c7faa062b478b61abb0a121463a5af7", "status": "OK"}, "Sheaf.Paper.OrderedLineLevelBounds": {"hash": "5f72ca8d9be8baf15de4529cd0c1467486cdb2d3", "status": "OK"}, "Sheaf.Paper.OrderedTowerOrientation": {"hash": "99343b2d44ec92787450dc6ec2604ea4e9142b7d", "status": "OK"}, "Sheaf.Paper.OrientationScalarTowerTransport": {"hash": "322b312084978e6ab9be061d3acdf23b186ec025", "status": "OK"}, "Sheaf.Paper.PurityConjugatesTowerReduction": {"hash": "1e086facd08a557ee70cd2b11daed249cb5fb1fd", "status": "OK"}, "Sheaf.Paper.PurityFiniteReductionTransport": {"hash": "bc622c3185cb59358dd7f8e7929fd9b6f2f8afe6", "status": "OK"}, "Sheaf.Paper.PurityPullbackLevelBounds": {"hash": "6ea155b44a709e8e23091cc0afc8ce2b286335a5", "status": "OK"}, "Sheaf.Paper.PurityPullbackReductionTransport": {"hash": "49fb368f9bc4b67444caa0756750e0b77b22eef5", "status": "OK"}, "Sheaf.Paper.PurityTowerReductionComparisons": {"hash": "a116ef52274ded289b1c2ab3b825696d5255418e", "status": "OK"}, "Sheaf.Paper.RamifiedScalarSystemTranspose": {"hash": "53ac490826ec5a0fa35c7c8f9a5ca4c9b3fca77d", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerExceptionalBaseChange": {"hash": "6f30c11dc8ec3387ce795d19d5615b4637267f9b", "status": "OK"}, "Sheaf.Paper.SmoothPurityTowerGamma": {"hash": "5acba5c62f3ee60c4f89317ea0ebbe0014833afb", "status": "SLOW"}, "Sheaf.Paper.SmoothPurityTowerGammaData": {"hash": "3faa678db6f55cda2c50b35f9edb2522aed87431", "status": "OK"}, "Sheaf.Paper.SpecifiedTowerAdjunctionCharts": {"hash": "a48d6289d794e566bc76098a6213eef9ece33155", "status": "OK"}, "Sheaf.Paper.SystemScalarBasisDistributivity": {"hash": "d1e277ef767e0f140397fd95175d477b01bfab8d", "status": "OK"}, "Sheaf.Paper.SystemScalarProjectionData": {"hash": "6e6a70ab41d6f19ceee232ba81eb824f4b6f89c8", "status": "OK"}, "Sheaf.Paper.SystemScalarProjectionIdentification": {"hash": "1c756cefdef2387f213274b53f0077c897f22016", "status": "OK"}, "Sheaf.Paper.SystemScalarRefinementRestriction": {"hash": "ddecac2836e96c2ff72d7facaa63210ecf22337a", "status": "OK"}, "Sheaf.Paper.SystemScalarTensorConstituents": {"hash": "096756fb6038c07c81567f421c86a658ef0c40a6", "status": "OK"}, "Sheaf.Paper.TensorTransposeFiniteEvaluation": {"hash": "2747fdf31112a4c3a3e19ac5d06b7568f27fdf20", "status": "OK"}, "Sheaf.Paper.TensorTransposeTowerNaturality": {"hash": "0a067dc359f6b0bbf18ecaa7a0ddd6e18fc71061", "status": "OK"}, "Sheaf.Paper.TowerGeometricPurityAssembly": {"hash": "0c61068a11023e1f3414c29eda621862a82991bb", "status": "OK"}, "Sheaf.Paper.TowerGeometricPurityData": {"hash": "ed87f8b9b06e73ceae670bcf6c4d5efb190ad45b", "status": "OK"}, "Sheaf.Paper.TowerGeometricPurityMate": {"hash": "5148d3e17b63f01e577b8a194970f03cbc3065cd", "status": "OK"}, "Sheaf.Paper.TowerIsomorphismPullback": {"hash": "017c2bf54510d71e12db382735abbfc2d2ac40da", "status": "OK"}, "Sheaf.Paper.TowerNormalizationPreservation": {"hash": "1885f0cb5c93f66cc64ed000402c2d6d74ce18d8", "status": "OK"}, "Sheaf.Paper.TowerOrientationEvaluation": {"hash": "8705c45aebd6d1ea6a6fe504576b8c30baaba78c", "status": "OK"}, "Sheaf.Paper.TowerOrientationWordNormalization": {"hash": "97abe3d31b6ee4ed5f46d6370e95a616eca74995", "status": "OK"}, "Sheaf.Paper.TowerPurityPresentationRetagging": {"hash": "b2571a7d3262d6e579352822e236d226529aac30", "status": "OK"}, "Sheaf.Paper.TowerSemilinearPurityFactors": {"hash": "8719bba6ca94b52eb9e12182c593ee391f39961d", "status": "OK"}, "Sheaf.Paper.TowerTensorPresentationRetagging": {"hash": "af1e0b391289cc4aabadff640afc28538a5a9746", "status": "OK"}, "Sheaf.Paper.TowerTensorTransposeEvaluation": {"hash": "a47c26025f99b360a1796e9227faaf10a3b816db", "status": "OK"}, "Sheaf.Paper.TowerTensorTransposeWords": {"hash": "7651e3f44fb3fedc396bf3a3849fe75be73b6b36", "status": "OK"}, "Sheaf.Paper.TransportCondensedStageRealization": {"hash": "f8323086ff6e7137688f677c6b511811ad4fe164", "status": "OK"}, "Sheaf.Paper.TransportIntegralBaseChangeRealization": {"hash": "41279c82fb72a9f1781669c5bea4f75d167c5e20", "status": "OK"}, "Sheaf.Paper.TransportIntegralChartRealization": {"hash": "88cf176d90d5ec739ff0b920c34172ef3c69e24f", "status": "OK"}, "Sheaf.Paper.TransportIntegralCompositionRealization": {"hash": "38a24cd4b0bc9510d17ddebd74c653bca11b0693", "status": "OK"}, "Sheaf.Paper.TransportIntegralCounitRealization": {"hash": "362789f01525bd317330b272608a9f8d1b5f57d3", "status": "OK"}, "Sheaf.Paper.TransportIntegralStageConstruction": {"hash": "80d4d6ba6379bc0c6e16c865a1516facb64b28ed", "status": "OK"}, "Sheaf.Paper.TwistedPullbackTowerDomain": {"hash": "707eb28c771ca3083afffa07cdfbdba735f46fe5", "status": "OK"}, "Sheaf.Paper.TwistedPullbackTowerDomainDefinitions": {"hash": "6632aecdf649f0d15eab12e57540459901c0851c", "status": "OK"}, "Sheaf.SecSmoothPurity.RationalPurityCommonComparisons": {"hash": "451910a2a6fb486101bdbe680fd4cb2b8a1e4b4f", "status": "OK"}, "Sheaf.SecSmoothPurity.RationalPurityLineComparisons": {"hash": "7dfea4a2aa9ca58786b61db04994341c85d15175", "status": "OK"}, "Sheaf.SecSmoothPurity.RationalPurityTraceCoherence": {"hash": "0091913289529cd60ce8938cc38e96ee7a2ce7a4", "status": "OK"}, "Sheaf.SixFunctors.CoefFiniteDualizingMixedQuotient": {"hash": "dfa51ac9440dcdc04735a277ffeb597ad3cbd85d", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteDualizingCoherence": {"hash": "33e6258868e735e99734a98c2ddda6fb4b2830e1", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtension": {"hash": "a80bce78cffaf702f091a3521d667088921b08f8", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionCocycles": {"hash": "532a5085aec183e999489631bbf2213dffa2918e", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore": {"hash": "0a1aee71c28d60cfb9a9acf7830178acf5b1b529", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionInvertibility": {"hash": "7da3a8e08d0e78133a5c35595921e680f5ee5142", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionModels": {"hash": "315bf5ae6984c62b3462787294e26b4b4d829a62", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing": {"hash": "9da7a6277038cc55900ad0956103673a862edcd4", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralScalarQuotientTransition": {"hash": "0a6961873089daa947760cc01f9a656f94d59525", "status": "OK"}, "Sheaf.SixFunctors.CoefScalarReductionExchange": {"hash": "c9ebe335e63f42afaec1d952de4f53755494da50", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralNormalizedAdjunction": {"hash": "dc3510828603f0e52ff4d7a2249b3f08c25fa75c", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralRealizationAssembly": {"hash": "029bbfb7a3f95cade80e36f8432d666abf17022a", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstruction": {"hash": "ecfed2c7ccc5b634e5234ed5d7238a3c6e1b0b1d", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstructionEquivalence": {"hash": "ba3c7868a918eff9ff9e82173364432b81326775", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces": {"hash": "dfd7491b122f1402fa3e5e5f1ca4f2b05228ee34", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralSystemExistence": {"hash": "3a2762881292a445abf50cc8f61fb3b3c0be90cb", "status": "OK"}}, "seconds": 454, "time": "2026-10-28T01:29:41+0800", "transitive": 95, "version": 1}
```

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
