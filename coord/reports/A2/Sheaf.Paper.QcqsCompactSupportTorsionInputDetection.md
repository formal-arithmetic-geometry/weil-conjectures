## What changed

Replaced the unnecessary arbitrary-field uniqueness route by the actual construction
and the exact uniqueness result used by its consumers. The general-field
`sfQcqsCompactSupportRealization` has the same type and projection predicate. It is
now `asIso` of the explicit `sfQcqsCompactSupportRealizationMap`: the reduction
adjunction unit, total limit of the chosen whole strict proper/open comparison,
and inverse recorded gamma. Finite projection identities and invertibility of
this particular composite are proved separately. No arbitrary isomorphism is
chosen solely by its finite projection equations.

Added `sfQcqsCompactSupportRealization_spec` for those projection identities. Replaced
the generic `sfQcqsCompactSupportRealization_existsUnique` assertion by the separately
named, proved `sfQcqsCompactSupportRealization_existsUnique_of_isAlgClosed`.
Its proof cancels the finite reduction isomorphisms in the normalization equations,
transports the known finite shifted-Hom theorem through the constructed realization,
and applies the Milnor finite-reduction injection componentwise. Every actual
consumer asserting uniqueness uses `FiniteFieldDatum.k`, an algebraic closure.

Four consumer proofs now use the specification lemma, with an explicit proof import:
`CompactificationCompletedRealization`, `IntegralOpenSupportNormalization`,
`IntegralSupportCounitProjection`, and `IntegralSupportTowerNormalization`.
`CompactSupportCoefficientModels` uses the algebraically closed uniqueness theorem
and derives its local `IsAlgClosed D.k` instance with `IsAlgClosure.isAlgClosed D.k₀`.
All five consumer signatures remain identical. To meet the 60-second compile limit,
proved coefficient-model helpers are moved into
`CompactSupportCoefficientModelHelpers`, imported only for proofs. The already proved
private natural-balancing uniqueness lemma is exposed as
`compactSupportCoefficientModels_balancing_existsUnique` with its own node; the other
helpers remain private. Every existing public declaration stays in place, and no
hole is introduced. They were unclaimed when checked.
No source-library file or target statement changes.

Validation: all seven delivered Lean files compile through `lcompile.py --all`.
The helper module takes 36.6 seconds, the coefficient-model consumer 43.6,
and the other adapted consumers 19.4--28.3; all stay below 60 seconds.

The direct finite-Hom argument makes the entire assigned module unnecessary.
Withdrew `QcqsCompactSupportTorsionInputDetection`, `QcqsCompactSupportReductionRigidity`,
and `QcqsCompactSupportNormalizedLift` through `deleted.txt`. Retained all six DAG
statements realized by these modules as historical mathematics with `lean: null`;
removed their unused proof dependencies. Updated the actual parent
`def-weil-integral-rational-qbar-compact-support` to the explicit construction and
direct algebraically closed Milnor proof. A full DAG parent scan and quarantine
source scan found no external remaining parent or caller of the retired assertions.
The unit has no realized statement or step requiring them. Its statement and route
are unchanged.

The coefficient-model consumer keeps the large realization locally irreducible and
respects transparency while elaborating its final proof; no global attribute changes.

Change record: `coord/changes/a2-qcqs-prune-general-field-rigidity.md`, including all
1,803 source downstream users and their claim holders when checked.

## Proved and sorry left

The item originally has one hole:
`WeilConjectures.sfQcqsCompactSupport_torsion_input_ext`
(`lem-qcqs-compact-support-torsion-input-detection`). It is **pruned**, not proved.
Thus 0 of 1 original holes are proved; 1 is removed by pruning; 0 are added and
0 are split off. The item is withdrawn under brief step 8d. There are no `sorry`
declarations in any delivered Lean module.

New fully written proofs:
`WeilConjectures.sfQcqsCompactSupportRealizationMap_spec`,
`WeilConjectures.sfQcqsCompactSupportRealizationMap_isIso`,
`WeilConjectures.sfQcqsCompactSupportRealization_spec`, and
`WeilConjectures.sfQcqsCompactSupportRealization_existsUnique_of_isAlgClosed`.
The existing private natural-balancing proof is retained as the proved public
`WeilConjectures.compactSupportCoefficientModels_balancing_existsUnique`.
The general-field mathematical uniqueness assertion remains unsettled; no
counterexample or proof is claimed. It is not needed for the target route.

## No longer needed

Withdrawn modules:

- `Sheaf.Paper.QcqsCompactSupportTorsionInputDetection` (the assigned item).
- `Sheaf.Paper.QcqsCompactSupportReductionRigidity`.
- `Sheaf.Paper.QcqsCompactSupportNormalizedLift`.

Retired nodes, all detached without changing their historical statements:

- `lem-qcqs-compact-support-torsion-input-detection`.
- `lem-qcqs-compact-support-torsion-input-finite-evaluation`.
- `lem-qcqs-compact-support-torsion-input-finite-hom`.
- `lem-qcqs-compact-support-torsion-input-alg-closed`.
- `lem-qcqs-compact-support-reduction-rigidity`.
- `lem-qcqs-compact-support-normalized-lift`.

Their public declarations disappear with those modules, including the unused
`SfQcqsCompactSupportMorphismSpec`. The generic
`sfQcqsCompactSupportRealization_existsUnique` is also retired: uniqueness
consumers use the separately named algebraically closed theorem, and consumers of
projection equations use `sfQcqsCompactSupportRealization_spec`.

The realization drops its `QcqsCompactSupportNormalizedLift`,
`SfIntegralConstructibleTriangulated`, and `ProEtaleBoundedConstructibleTriangulated`
imports; the latter two are still used by the private cone helpers reused through
`import all QcqsCompactSupportNormalizedIsoExistence`. Finite comparison remains
needed to prove invertibility of the explicit composite. The assigned module's
imports all disappear with it; none is imported solely to support its unfinished
strict-density plan. In particular `QcqsCompactSupportTorsionCoefficientAction`
has no surviving Lean importer after this withdrawal and no remaining external
DAG proof use. Its already proved source is retained, not edited or deleted.

The old planned density dependencies
`lem-weil-compact-support-reduction-tower-functor`,
`lem-weil-compact-support-representative-independence`,
`prop-weil-pbc-direct-image-limits`,
`lem-weil-pbc-ringed-strict-tower-homotopy-limit`,
`lem-coef-derived-system-evaluation-calculus`, and
`lem-sf-integral-open-reduction-comparison` are no longer obligations of the
retired detection assertion. They still serve the actual strict construction;
no claim that they are globally unnecessary is made. No source-library
signature, public import, or proved body is removed.


Removed import edges in the three withdrawn modules (all their imports):

`QcqsCompactSupportTorsionInputDetection`:

```lean
public import Sheaf.Paper.CompactSupportFiniteAction
public import Sheaf.Paper.IntegralCompactSupportCoefficientData
import Sheaf.Paper.QcqsCompactSupportNormalizedIsoExistence
import Sheaf.Paper.QcqsCompactSupportFiniteComparison
import Sheaf.Paper.QcqsCompactSupportTorsionCoefficientAction
import Sheaf.Paper.SfIntegralConstructibleTriangulated
import all Sheaf.Paper.IntegralPrincipalConeQuotientAugmentation
import Sheaf.Paper.AdicReductionTriangle
import Sheaf.Paper.IntegralReductionShiftedHomFiniteAlgClosed
import Sheaf.Paper.DerivedCompleteFiniteReductionDetection
```

`QcqsCompactSupportReductionRigidity`:

```lean
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
import Sheaf.Paper.QcqsCompactSupportTorsionInputDetection
import Sheaf.Paper.QcqsCompactSupportTorsionCoefficientAction
```

`QcqsCompactSupportNormalizedLift`:

```lean
public import Sheaf.Paper.IntegralRationalQbarCompactSupport
public import Sheaf.Paper.CompactSupportFiniteAction
public import Sheaf.Paper.IntegralCompactSupportCoefficientComparison
import Sheaf.Paper.QcqsCompactSupportNormalizedIsoExistence
import Sheaf.Paper.QcqsCompactSupportReductionRigidity
```

## Where the brief, the DAG or earlier work was wrong

The previous route promoted a general-field construction to uniqueness among
arbitrary ordinary natural transformations based on finite evaluations. The
recorded coherent-lift objection identifies a gap: the available strict-diagram
and adjunction declarations construct the specified comparison, not a lift of
every arbitrary comparison with the same finite evaluations. No unsupported
lift assertion is introduced here.

The actual blueprint definition requires a constructed realization. Its independent
review dated 2026-10-17 explicitly permits restricting general-K0 uniqueness to the
algebraically closed setting at stage 3 if necessary. All genuine uniqueness
consumers are over the already supplied algebraic closure; the single arbitrary-field
consumer of the old uniqueness theorem only used its finite projection equations.
The revised argument therefore preserves every consumer statement and proves
exactly the uniqueness conclusions they use. Generic assertions are withdrawn
with their unused dependency chain, not silently weakened under their old names.

The live server queue was read first: this is a disputed item with one hole.
The historical build-error file lists bad dependencies from a quarantine event;
the compile service currently resolves them. One proved helper node records the already proved balancing argument;
no unproved statement is introduced. Every delivered definition has an actual construction.

## New nodes

`lem-pur-compact-support-coefficient-balancing-natural-iso` records the already proved
ordinary tensor-balancing comparison, natural and uniquely fixed by its local tensor
formula. Its public declaration is
`WeilConjectures.compactSupportCoefficientModels_balancing_existsUnique` in
`Sheaf.Paper.CompactSupportCoefficientModelHelpers`. It is an actual step of the
coefficient-model proof, proved from the existing ordinary cancellation comparison,
and has zero holes. Supporting arithmetic, tensor-generator and localization proofs
remain private. Change record:
`coord/changes/a2-qcqs-prune-general-field-rigidity.md`.

## Related modules compiled before delivery

127 related module(s) compiled against this delivery by deliver3.py: 116 OK, 11 SLOW.

```json
{"capped": false, "direct": 112, "left_out": 0, "own": {"Sheaf.Paper.CompactSupportCoefficientModelHelpers": "92a5a1daec4bf1c21fca02ac4cf816557e11e603", "Sheaf.Paper.CompactSupportCoefficientModels": "b802a913c8d344956667b3d4e8e833177a8f7f8e", "Sheaf.Paper.CompactificationCompletedRealization": "9bd966138419b6f5d872603d5ddcc9a964b8db1c", "Sheaf.Paper.IntegralOpenSupportNormalization": "93803832202a74f2761b75e9cd41670c3d5c79c1", "Sheaf.Paper.QcqsCompactSupportNormalizedLift": "fdd6fd89e33daef28207b2d920705ea5b4231ed8", "Sheaf.Paper.QcqsCompactSupportRealization": "9206ac11cc3a0ec9a13d1cb145d01e3de0969ed3", "Sheaf.Paper.QcqsCompactSupportReductionRigidity": "fdd6fd89e33daef28207b2d920705ea5b4231ed8", "Sheaf.Paper.QcqsCompactSupportTorsionInputDetection": "fdd6fd89e33daef28207b2d920705ea5b4231ed8", "Sheaf.SixFunctors.IntegralSupportCounitProjection": "67492ffb670fe52a0af3216ef653a10f6055651a", "Sheaf.SixFunctors.IntegralSupportTowerNormalization": "997ad6eea799f94d9939906898cbccd1a9e509bd"}, "results": {"Sheaf.Paper.AdicOperationDomainsSourceComparison": {"hash": "2e48216f8679052116f7646d12477accfd1c91d4", "status": "OK"}, "Sheaf.Paper.AdicProjectionShiftData": {"hash": "c2aea3e7b432fca4c12e6b37a7eb82a972634455", "status": "OK"}, "Sheaf.Paper.ClopenPrescribedWeilFiltration": {"hash": "821e0f46210371b369b10bc075036b8574f60e05", "status": "OK"}, "Sheaf.Paper.CoefTowerCoaugmentation": {"hash": "4354a7f9e80c63cc95a014823955be1a4b5e07a5", "status": "OK"}, "Sheaf.Paper.CommonStageCompactSupportExactness": {"hash": "6aa9d1e63c9910fee8fef00d56c33f50c665ffd1", "status": "OK"}, "Sheaf.Paper.CommonStageOpenHeartAdjunction": {"hash": "9c5fc8eee1c11e239dcc5d8b35671125e5703e3e", "status": "OK"}, "Sheaf.Paper.CompactSupportArrowScalarTransport": {"hash": "c948fb3f2cf76d91a820583c48f339f79e90b60b", "status": "OK"}, "Sheaf.Paper.CompactSupportNormalizedRealization": {"hash": "58eb89cb700373bcccf18d953b5e270edde3d1ae", "status": "OK"}, "Sheaf.Paper.CompactSupportNormalizedScalarDescent": {"hash": "6c7c25fb0eb44a4633534e59d0bfe31c66f7496e", "status": "OK"}, "Sheaf.Paper.CompactSupportNormalizedScalarDescentTower": {"hash": "05d7f1c1e7639986cebd67503ba00ab67ab3d425", "status": "OK"}, "Sheaf.Paper.CompactSupportNormalizedScalarDescentUnit": {"hash": "1bd7a8aabdf4843146cf1a902b75f4a3de8a57bd", "status": "OK"}, "Sheaf.Paper.CompactSupportNormalizedScalarIsomorphisms": {"hash": "98ab7f48c6b9e7364232dc6c6cc0a69ad97265c6", "status": "OK"}, "Sheaf.Paper.CompactSupportProjectionRealization": {"hash": "959fbd3073942f506163e940709f48ad03204327", "status": "OK"}, "Sheaf.Paper.CompactSupportRealizationFactorNormalization": {"hash": "21a1fae00a5f5e376cdaca1227b75267f4c85edf", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarGammaIdentification": {"hash": "cc025e92de95e991214780574faf9bcb451568ce", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarLimitFoundations": {"hash": "2926279d279132ce0e90d83464e227e440a6d18a", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarLimitReduction": {"hash": "f0eba93ca050aa62762970feb3d74016b69b9b0e", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarProjectionIdentification": {"hash": "7dab61e9a6fe8b490f51538a9a2a47184f1d3643", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarShiftStructures": {"hash": "9a33778c69a8448596af18305a380741b641c626", "status": "OK"}, "Sheaf.Paper.CompactSupportStrictScalarComposition": {"hash": "483f6a051b46fc1b56726e8c58700c5ac93fc755", "status": "SLOW"}, "Sheaf.Paper.CompactSupportStrictScalarRefinement": {"hash": "ef52f86fbc3b0c076055fb346b07d1d0b7eaa9b3", "status": "OK"}, "Sheaf.Paper.CompactSupportSystemRealizationNormalization": {"hash": "3d61967d7537aa959d68b7f6983cffadfe893a0e", "status": "OK"}, "Sheaf.Paper.CompactSupportTotalLimitRealization": {"hash": "bc1fddc92abf315b1fd94da98d0e76b5a822d852", "status": "OK"}, "Sheaf.Paper.CompactificationCompletedRealizationData": {"hash": "aea98dd76874095d6ec213c558b623ee5b7b3860", "status": "OK"}, "Sheaf.Paper.CompactificationStrictRealization": {"hash": "d6bd2b8c8c3452ff18fcbe4933811f97c5166869", "status": "OK"}, "Sheaf.Paper.CompactifiedTowerComparisons": {"hash": "903a3dafff8c66a165ab5fab52ddddf0cbb78d6c", "status": "OK"}, "Sheaf.Paper.ConcreteIntegralProjectionCone": {"hash": "f3d4832ddb372eed3cdf9a1d5fbab9b893d2bf7c", "status": "SLOW"}, "Sheaf.Paper.ConcreteProjectionFieldDescent": {"hash": "37c3b4292ac1b381ec93f17713b9fea8d709f995", "status": "SLOW"}, "Sheaf.Paper.ConcreteProjectionReductionData": {"hash": "2c1f3de7cba7407c4406a3ccaa5cf5a3961327b6", "status": "OK"}, "Sheaf.Paper.ConcreteProjectionReductionSquare": {"hash": "c17a801f340cc0ad8ce08b04db449ceac876ebb4", "status": "OK"}, "Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficientsData": {"hash": "120436250c5e06a8d30545b904ea6efb84be81bf", "status": "OK"}, "Sheaf.Paper.ConstructibleExceptionalCoefficientConstructionData": {"hash": "5ca3b8be1af910cfda96857f5419c9bb3a80575b", "status": "OK"}, "Sheaf.Paper.DegreeZeroCompactSupportSections": {"hash": "5c2846a1d8755609b53e25e16fc10e6096219c46", "status": "OK"}, "Sheaf.Paper.ExceptionalIntegralScalarMates": {"hash": "76e8e71b5e4ac1c15dac912e5064ece33703e39f", "status": "OK"}, "Sheaf.Paper.ExceptionalRefinementTransportData": {"hash": "6a5841c11bc14628af0d67dfb20cd9e63507d75f", "status": "OK"}, "Sheaf.Paper.ExceptionalRingStageAssembly": {"hash": "4a87df980c4d561050c019994e2facf132662d16", "status": "OK"}, "Sheaf.Paper.ExceptionalRingStageAssemblyData": {"hash": "838678e3a414540b70aabba92f8614d45502b1d3", "status": "OK"}, "Sheaf.Paper.ExchangeFunctoriality": {"hash": "336e0b436afaf2bfd85da9d780fae6660d4a0576", "status": "OK"}, "Sheaf.Paper.ExtensionByZeroPunctual": {"hash": "501062e87622d890e754573f1ab3be2d16b61df5", "status": "OK"}, "Sheaf.Paper.FieldShriekCompositionIntegralComponent": {"hash": "1cf7d95c816de8c22ce7868d4d3133d33a1261c5", "status": "OK"}, "Sheaf.Paper.FieldShriekCompositionNormalization": {"hash": "b6be10e1a27772b9aeec5ece276325836bffbfc0", "status": "OK"}, "Sheaf.Paper.FieldShriekCompositionQcqs": {"hash": "cb1cf168bdb0908a5828dd52a2f3a112253053d3", "status": "OK"}, "Sheaf.Paper.FieldShriekLowerBound": {"hash": "bb73de0efc8835833fd83b0cab9d63390c850a05", "status": "OK"}, "Sheaf.Paper.FieldWeilShriekShiftData": {"hash": "5c0b9354c99c9e73728a547bd4397bc11046c209", "status": "SLOW"}, "Sheaf.Paper.FourierKernelConvolution": {"hash": "b6781fb89e7fea6f8945dcbec4014559699dd241", "status": "OK"}, "Sheaf.Paper.FrobeniusCompactSupportExchange": {"hash": "5238c4ffca4b34cfdee4a1b7b7d59fafc4f31b73", "status": "OK"}, "Sheaf.Paper.FrobeniusSquareExchange": {"hash": "7ebce78f7f19e0d89781a23e101d1e0957274850", "status": "OK"}, "Sheaf.Paper.IdentityCompactificationLimitComparisons": {"hash": "d3620e616e0cfe1633d1dba70e1d4a57fdc8a2af", "status": "OK"}, "Sheaf.Paper.IdentityCompactificationSystemMate": {"hash": "37a9b585ed2d6c9fdb809b06376175ed64d9c1ae", "status": "OK"}, "Sheaf.Paper.IntegralCompositionCoefficientSquare": {"hash": "b719d2ba408bfcf7da1ca77a52e46534089db02f", "status": "OK"}, "Sheaf.Paper.IntegralOpenAdjunctionTransposeNormalization": {"hash": "107a1c3be9d4e4dea3ff86ecf5087d58e074d5c8", "status": "OK"}, "Sheaf.Paper.IntegralOpenEmptyPullbackVanishing": {"hash": "e0204c7152f19f46de77bbe36a958224b3174ea2", "status": "OK"}, "Sheaf.Paper.IntegralProjectionCoordinateData": {"hash": "cea173863fef2072663dd309840aaf86b519d935", "status": "OK"}, "Sheaf.Paper.IntegralProjectionOperationPresentation": {"hash": "6e0f41f2b7151afafbd03ac47335c49b2e9dd1b1", "status": "OK"}, "Sheaf.Paper.IntegralProperOperationProjection": {"hash": "18353eaef68b2b99791caa31e96419093f9f2208", "status": "OK"}, "Sheaf.Paper.IntegralSectionsPerfectReduction": {"hash": "2be1f654cee8aed5a37528b0678cee4df608f7aa", "status": "OK"}, "Sheaf.Paper.IntegralSupportAdjunctFiniteCoordinates": {"hash": "29822a6085d1fa21a3549b52b76ca7fd3ae0f847", "status": "OK"}, "Sheaf.Paper.IntegralSupportFunctorNormalization": {"hash": "fb1f160aeee91fa0adc2ea96d83edb1460a363a9", "status": "OK"}, "Sheaf.Paper.IntegralSupportNormalizationData": {"hash": "3dace0973f3366637a488ddbda4029a59b48dba2", "status": "OK"}, "Sheaf.Paper.LocallyFiniteAdicCompactSupportData": {"hash": "228607968cbf697875a27c3beb2d872c5ea196c3", "status": "OK"}, "Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization": {"hash": "b1222b33661731a5f010777a9242825042cdc6f7", "status": "OK"}, "Sheaf.Paper.NativeCompactSupportIntegralScalarMorphism": {"hash": "34864e553b7dc493207a886cd35bbde5cbbb0f16", "status": "OK"}, "Sheaf.Paper.NativeWeilScalarFrobeniusCounit": {"hash": "744aa481959f2b15900ab73a5dbb0a8c7018ac42", "status": "OK"}, "Sheaf.Paper.NormalizedFieldPurityTrace": {"hash": "3b10314592afc55a22b3f737f950026bb4f66758", "status": "OK"}, "Sheaf.Paper.OpenCompactSupportFiniteTor": {"hash": "165bb9f853e560fc09e1e8370ecee3424edc8cf9", "status": "OK"}, "Sheaf.Paper.OpenWeilCoefficientFibres": {"hash": "c3e640d58aab7a27dd059cceb9bd7db40f6bf6b4", "status": "SLOW"}, "Sheaf.Paper.OrdinaryCompactCohomology": {"hash": "3359ac7332dec0ec808c4f2fe7279552b53a96c8", "status": "OK"}, "Sheaf.Paper.PodReconstructionCommonStageData": {"hash": "ef27d9460001bc25673af8e3c40663a5b5b3c961", "status": "OK"}, "Sheaf.Paper.PodReconstructionRawRationalNaturality": {"hash": "c7d1189397b56a4f0fecbafedee058f04478f1ef", "status": "OK"}, "Sheaf.Paper.ProjectionWeilTensorDomainBridge": {"hash": "ff2e4ac76a3581b5777f72de17fb80ec5a21c6b9", "status": "SLOW"}, "Sheaf.Paper.ProperCoefficientDescentData": {"hash": "1655015a9a095e47fa17036ed42adb4505719319", "status": "OK"}, "Sheaf.Paper.ProperCoincidenceFrobenius": {"hash": "89f04ea0eab6fc360b971ba9809eb7a9da105fc9", "status": "OK"}, "Sheaf.Paper.ProperIntegralTowerComparison": {"hash": "bf7c2dec72446cceab3c19b831e7f4a44b3de2ae", "status": "OK"}, "Sheaf.Paper.PurRepresentingPairFiniteScalar": {"hash": "5425933ee6d010d7168aca7ccface28d91f972f9", "status": "SLOW"}, "Sheaf.Paper.QuasiFiniteCompactSupportWeights": {"hash": "82eb99f9a6a4c9069dea4eb1d4cb61f27df5dde5", "status": "OK"}, "Sheaf.Paper.RationalWeilPurityNaturalityMate": {"hash": "bea9b1ea85e14d4d7c780bf521d6174ea17668f6", "status": "OK"}, "Sheaf.Paper.ReducedFrontierMixedGluing": {"hash": "5d5726d9f6bc615a22ac7b099f937058d9d9cf1f", "status": "OK"}, "Sheaf.Paper.ScalarRefinementOriginsF": {"hash": "c3cf2f49a607f86e7471bb35c7c736becdbf40e5", "status": "OK"}, "Sheaf.Paper.SfPackageFieldOperationRealization": {"hash": "978721d6f62245e573bffa5afffcc113d7302b05", "status": "OK"}, "Sheaf.Paper.SfPackageQbarAdjunctionMapDescent": {"hash": "4914402a2aa3fd2eeb36d30aab31afd362046cc4", "status": "OK"}, "Sheaf.Paper.SfProEtaleProjectionFormula": {"hash": "3a38fd19c04e2c191e9b5a3721527f4cf323432d", "status": "OK"}, "Sheaf.Paper.SfQbarLocalizationCommonStage": {"hash": "52a888325ec6a9665cc024bfcb7b995160cd7f5b", "status": "SLOW"}, "Sheaf.Paper.SfQbarLocalizationFiniteData": {"hash": "a4a089ea1db3797bf04b6d61d67b6d42ceee217e", "status": "OK"}, "Sheaf.Paper.SfRationalLocalizationOrthogonality": {"hash": "efe12e2c710e23b20efd7b06d071e181613b85ef", "status": "OK"}, "Sheaf.Paper.SmoothPurityQbar": {"hash": "8d648504e26d81c12213c01ffe2c9baf30bd300b", "status": "OK"}, "Sheaf.Paper.StrictReductionCompactSupportNormalization": {"hash": "b1e50fe7123f5b7c7b2b014983b6e39ce46649da", "status": "OK"}, "Sheaf.Paper.SystemCompactSupportRestrictionCocycle": {"hash": "c13d4be067992d57df14e6f03167b9e926ff7275", "status": "OK"}, "Sheaf.Paper.TraceFormulaCurveIntegralLattice": {"hash": "40915cc9f31c4818ef9ac8ad4b27fa2578ddd474", "status": "OK"}, "Sheaf.Paper.ZlFrameworkOpenExchange": {"hash": "817d737b9ee39d4db3caf4e5d27ae2865eee2c92", "status": "OK"}, "Sheaf.Paper.ZlFrameworkPbcOpenComparisonData": {"hash": "b7f52a5057dde39f0a1e44745a1884ddf0452f8f", "status": "OK"}, "Sheaf.Paper.ZlFrameworkPbcOpenExchangeComparison": {"hash": "c0e23fcb1067875ce173fb4fbd9371b9be4438f5", "status": "OK"}, "Sheaf.Paper.ZlFrobeniusCompactSupportComparison": {"hash": "ac4bbeee015a2595987f24b95f4d92106d531b8c", "status": "OK"}, "Sheaf.Paper.ZlImmersionFilteredReductionTransport": {"hash": "0882ca16527dda74844fd839ce718279ed9fc292", "status": "OK"}, "Sheaf.Paper.ZlOpenCompactSupportRestriction": {"hash": "ce71c5e9b8161d84c7c62a4fb3a1e5e4fc7ec35a", "status": "OK"}, "Sheaf.Paper.ZlOpenExtensionTExact": {"hash": "4da00ee15371c466828dc33a38b9e073d71ab4e9", "status": "OK"}, "Sheaf.Paper.ZlOpenWeilUnitEmptyFibre": {"hash": "2c645bee0c85cdd5623a41dd36a150e0bb194e2c", "status": "OK"}, "Sheaf.Paper.ZlWeilHeartLocalizationExact": {"hash": "29c54b823032f6001deace41c29951a5b8e8b6f7", "status": "OK"}, "Sheaf.Paper.ZlWeilShriekCoefficientLongExact": {"hash": "540a26ecffa5f3eb4f05a4ac668de5753cf5a970", "status": "OK"}, "Sheaf.SecSmoothPurity.AdicScalarTraceCoherence": {"hash": "bcc2dcd140be9b2e2c9e24e12af0eb748364f8dc", "status": "SLOW"}, "Sheaf.SecSmoothPurity.ClosedUnitAllStages": {"hash": "ebf887d228730dc4c84bf207e315f1015c572a02", "status": "OK"}, "Sheaf.SixFunctors.CoefDualFormulaScalarTranspose": {"hash": "7d3d589889a049d7fd8736b8652bcf76e2fb7865", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierData": {"hash": "d25f0b76e5fc624b6b4cfe79dfbc577aef15f376", "status": "SLOW"}, "Sheaf.SixFunctors.CompactSupportStrictRoosShiftModel": {"hash": "b70d2eb996233ffa48c3fa8d8d0428ea8a4b852f", "status": "OK"}, "Sheaf.SixFunctors.CompactifiedProperTowerExchange": {"hash": "ad24fb59d5edf2eb5516cd4d49606259858444cc", "status": "OK"}, "Sheaf.SixFunctors.CompletedShriekCompositionLaws": {"hash": "a47b2735a4bdbf6d4e335cab6c7a4294f5d436a8", "status": "SLOW"}, "Sheaf.SixFunctors.DualizingSupportEvaluation": {"hash": "c495b06bb7f8ca6bfe591f0e39e3073225f3b720", "status": "OK"}, "Sheaf.SixFunctors.ExceptionalIntegralReconstructionInterfaces": {"hash": "dfd7491b122f1402fa3e5e5f1ca4f2b05228ee34", "status": "OK"}, "Sheaf.SixFunctors.FiniteCounitRestrictionSquare": {"hash": "d41b89b1a34bdb7d6c2ff25b5130f9b52b44e252", "status": "OK"}, "Sheaf.SixFunctors.FiniteMappingAdjunctionData": {"hash": "4d66fc0643988fe5de760a8fd6f4c53b92f4b89e", "status": "OK"}, "Sheaf.SixFunctors.FiniteScalarMateData": {"hash": "6d833127857194ca1793a47e528ebd6b11472d2d", "status": "OK"}, "Sheaf.SixFunctors.IntegralBasicRealization": {"hash": "e442298ef3f59c14ad0159080c4ae240bd784b76", "status": "OK"}, "Sheaf.SixFunctors.IntegralBasicRealizationData": {"hash": "fd4af4054e381afc50e6ff94d98f2308833fef5e", "status": "OK"}, "Sheaf.SixFunctors.IntegralCompactificationBridgeCoordinates": {"hash": "ca02ec050a010594eb1632b5f790db2ea40531dd", "status": "OK"}, "Sheaf.SixFunctors.IntegralCompactificationBridgeOrdinaryCoordinates": {"hash": "5b934cee03a6a26949588c19d193f812ffa3ad34", "status": "OK"}, "Sheaf.SixFunctors.IntegralCompactificationBridgeWords": {"hash": "cc4aff69aa90484a90d57f136d50dc9329320f53", "status": "OK"}, "Sheaf.SixFunctors.IntegralCompactificationComparisonBridge": {"hash": "70c1e070a3319b6c466a555f9ce32dc75a487a42", "status": "OK"}, "Sheaf.SixFunctors.IntegralCompactificationComparisonData": {"hash": "a229908825b8f95939f7b9d36c3a211946e92f4b", "status": "OK"}, "Sheaf.SixFunctors.IntegralCompactificationOrdinaryComposition": {"hash": "c2eb0a9041bbd2126aa194133d696f5f002a3a01", "status": "OK"}, "Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction": {"hash": "4cb63c4e27d0be274a5c4afb21fbc9031b6afbbb", "status": "OK"}, "Sheaf.SixFunctors.IntegralExceptionalMappingSystem": {"hash": "c06bf153e52e4cfced26aa8c141827ea7671d493", "status": "OK"}, "Sheaf.SixFunctors.IntegralExpressionRecursionData": {"hash": "4fb1639c8e04a7dc1d416d75cfc0c4ef21089804", "status": "OK"}, "Sheaf.SixFunctors.IntegralNormalizedRefinementPasting": {"hash": "b32deb85da648bb9c49ab07dff91712c562e556b", "status": "OK"}, "Sheaf.SixFunctors.OpenClosedWeilMateData": {"hash": "9630df99472a0f41c00bc0768460c09c74bc07ae", "status": "OK"}, "Sheaf.SixFunctors.ProjectionRefinementData": {"hash": "f6392cdd93746a11b3cd3ab75471f43bb75a99d5", "status": "OK"}, "Sheaf.SixFunctors.RationalOperationsData": {"hash": "6e1c802189be17ac7cce9014d9935851da7c4c8b", "status": "OK"}, "Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality": {"hash": "4cb460929f9ff045c0629d458c2bcf359c6e98da", "status": "OK"}, "Sheaf.WeilSheaf.CompactSupportFiniteCoefficientComparison": {"hash": "6e330b538358b91d2839ef99278da69eb16c114e", "status": "OK"}}, "seconds": 762, "time": "2026-10-28T02:58:00+0800", "transitive": 15, "version": 1}
```

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
