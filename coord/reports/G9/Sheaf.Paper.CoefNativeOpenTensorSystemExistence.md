## What changed

Replaced the proof hole in `Sheaf.Paper.CoefNativeOpenTensorSystemExistence` by an
explicit construction of the unchanged `SystemOpenCochainsData` statement.
The construction works on the vertical coefficient sequence site itself.
It uses the existing normalized algebraic inverse image and scalar-extension
adjunction, transports the ordinary tensorator through uniqueness of left
adjoints, and proves that its pure-section formula uses the specified native
`moduleAdj` unit. The proved generic restriction construction is in the new module
`Sheaf.Paper.CoefNativeOpenTensorRestriction`; it transports flatness and
K-flatness through the same isomorphism. The item specializes it to the native
sequence sites, with native push as the right adjoint.

A proved private categorical argument transposes the tensor of the open unit
and identity, inverts it using ordinary support and the invertible open unit,
and proves both the specified inverse-transpose equation and simultaneous
naturality. The new proved module `Sheaf.Paper.CoefNativeOpenTensorTotalization`
then supplies the actual cochain comparison, its summand equation, and
simultaneous naturality by the existing direct-sum totalization construction.

The remaining geometric clause is isolated in
`Sheaf.Paper.CoefNativeOpenTensorOrdinarySupported`: ordinary tensoring with
an extended module remains in the native extension's essential image.
It has a source, a complete proof in words, and its own DAG node. It is strictly
one part of the former obligation; it asserts no comparison morphism,
normalization, cochain compatibility or flatness. Existing module signatures,
definitions, public imports and target statements are unchanged.

All added imports of the item are proof imports. The new totalization module
publicly imports only `SemilinearSystemModels`; the support module publicly
imports `CompactSupportNativeSystemEvaluation` and `SemilinearSystemModels`,
which provide its actual statement definitions. The new restriction module
publicly imports `SemilinearSystemModels`, `AlgebraicInverseImage`, and the
continuous module pushforward definition needed by its public signature. No existing module other than
the item is changed. The three new modules have their own nodes, and the original
node's proof and dependencies describe this construction.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.CoefSupportOpenTensor.nativeOpenTensor_system_exists`
(node `lem-coef-native-open-tensor-system-existence`). Its proof is complete
from the imported named declarations, including the smaller support statement.
The item's module has zero `sorry`.

Added one hole:
`WeilConjectures.CoefSupportOpenTensor.nativeOpenTensor_ordinary_supported`
(node `lem-coef-native-open-tensor-ordinary-supported`). This is the only
`sorry` in the four delivered modules. Thus one upper hole is closed and one
strictly smaller ordinary-module hole is added: this is a decomposition,
not a claim of a net hole closure.

Proved without adding a hole:
`WeilConjectures.CoefSupportOpenTensor.nativeOpenTensor_restriction_exists`
(node `lem-coef-native-open-tensor-restriction`), including the specified
module-adjunction unit formula and preservation of flat-term K-flatness.

Also proved without adding a hole:
`WeilConjectures.CoefSupportOpenTensor.nativeOpenTensor_totalization_exists`
(node `lem-coef-native-open-tensor-totalization`). Its ordinary comparison
is a hypothesis; its unbounded cochain comparison and all insertion and
naturality equations are proved.

All four modules passed server compilation in import order; the item took
58.7 seconds in the successful run. The unused-variable warning on the
original existential binder is disabled only for that declaration, preserving
its exact signature. No profiler/debug options remain. `deliver3.py` performs
the final recompilation and packet, dependency and axiom checks.

## No longer needed

No original import is removed; the item's only original public import of
`CoefNativeOpenTensorPrimitives` is preserved. No existing module is withdrawn.

The original direct dependency on `lem-sf-open-tensor-normalization`
(`Sheaf.SixFunctors.OpenTensorNormalization`) is unnecessary for this ordinary
construction: the native open-unit theorem and the proved adjunction argument
supply normalization directly. We do not import the derived normalization
module. The planned direct use of
`lem-pur-site-restriction-module-adjunction-exact`
(`Sheaf.CategoryTheory.LocalizedModuleExactForSystems`) is replaced in the
restriction construction by the normalized geometric module adjunction and
uniqueness of adjoints; existing public declarations and their dependencies
are preserved.

`lem-weil-proetale-weakly-etale-localization` and
`lem-weil-pbc-ringed-slice-extension-tensor` are no longer direct dependencies
of the main construction. They remain dependencies of the smaller ordinary
support obligation, so this delivery does not claim that these nodes or their
modules can be removed. Likewise the totalization helper still uses
`lem-sf-ringed-open-total-tensor-kflat` through its proved generic component
comparison. These are dependency refinements; no global module pruning is claimed.

## Where the brief, the DAG or earlier work was wrong

No false statement or target mismatch was found. The existing ringed-topos,
normalized tensorator, and component-totalization proofs do supply most of the
construction, even though their public conclusions use different presentations.
Importing their proved private transport APIs lets this item construct its
specified native unit formulas instead of restating the whole data package.

The remaining gap is the transport of ordinary localized tensor support to the
native sequence-site module operations, including horizontal quotient arrows.
The existing derived varying-ring support statement does not directly supply
this ordinary-module assertion. The new node isolates exactly that geometric
step. Empty opens, zero modules and zero coefficient rings satisfy its stated
formula and need no extra hypotheses. The unit route is preserved; no unit
statement or realized proof step is removed.

## New nodes

`lem-coef-native-open-tensor-ordinary-supported`, in
`dag/nodes/sec-six-functors/lem-coef-native-open-tensor-ordinary-supported.json`,
is the single remaining ordinary essential-image clause of Stacks 0E8I. Its
statement is weaker than a normalized ordinary projection isomorphism, and it
contains none of the restriction/cochain/flatness data proved in the item.

`lem-coef-native-open-tensor-totalization`, in
`dag/nodes/sec-six-functors/lem-coef-native-open-tensor-totalization.json`,
is a proved reusable ordinary-to-cochain comparison with the required summand
and naturality equations. Separating it keeps the canonical totalization
elaboration in its own compilation unit. There are no change records: no
existing definition, signature, public import or other module is changed.

`lem-coef-native-open-tensor-restriction`, in
`dag/nodes/sec-six-functors/lem-coef-native-open-tensor-restriction.json`,
is a proved generic ringed restriction statement. Its public signature writes
out the actual module pushforward and underlying ring sheaves; no private
helper occurs in that signature. Separating it removes the generic tensor and
K-flat transport elaboration from the native specialization. The proof imports
of `CochainTensoratorExistence` and `KFlatRingedToposPullback` moved from the item
to this module and remain needed there.

## Related modules compiled before delivery

75 related module(s) compiled against this delivery by deliver3.py: 65 OK, 10 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.CoefNativeOpenTensorOrdinarySupported": "aed2f953fc7ff7381746402632cc6e18badd2ed6", "Sheaf.Paper.CoefNativeOpenTensorRestriction": "ad0e2f94b831a9779b1eb5e7e23af8396a942ae1", "Sheaf.Paper.CoefNativeOpenTensorSystemExistence": "865ed89b62dc7c45ef0de9af083813b4df5754ca", "Sheaf.Paper.CoefNativeOpenTensorTotalization": "8c26d45dc8677a748240ca0094681dcb8b722eda"}, "results": {"Sheaf.Paper.CoefNativeOpenTensorCochains": {"hash": "24883058d4c98279a981a16746182cd98d71edaa", "status": "OK"}, "Sheaf.Paper.CoefNativeOpenTensorModelsDataExistence": {"hash": "1edb30173f46503bb1ca97ba51b72d14a54ece98", "status": "OK"}, "Sheaf.Paper.CoefNativeOpenTensorModelsExistence": {"hash": "c2c8dd788ee9ddb5e7020ad7d4b30b0b3d12c5a4", "status": "OK"}, "Sheaf.Paper.CoefSupportOpenTensorModel": {"hash": "4699b1986c60f7b9d9d86b6b3da4640ea30e731e", "status": "OK"}, "Sheaf.Paper.CommonStageOpenHeartAdjunction": {"hash": "9c5fc8eee1c11e239dcc5d8b35671125e5703e3e", "status": "SLOW"}, "Sheaf.Paper.CompactSupportScalarLimitFoundations": {"hash": "2926279d279132ce0e90d83464e227e440a6d18a", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarLimitReduction": {"hash": "f0eba93ca050aa62762970feb3d74016b69b9b0e", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarProjectionIdentification": {"hash": "7dab61e9a6fe8b490f51538a9a2a47184f1d3643", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarRoosNormalization": {"hash": "198287cfb5e8418dffa020a0d751b0a380a6946a", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarRoosTensorNormalization": {"hash": "438e809356a5815a39ce3a7d5699fb9cd2f1072a", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarShiftNormalization": {"hash": "c5afcaac1025c37c6b3930ca5de1c17d2dd797c6", "status": "SLOW"}, "Sheaf.Paper.CompactSupportScalarShiftStructures": {"hash": "9a33778c69a8448596af18305a380741b641c626", "status": "OK"}, "Sheaf.Paper.CompactSupportScalarShiftWitness": {"hash": "38cca8fefa4288a91b3e863051ca0c24bef47b7e", "status": "OK"}, "Sheaf.Paper.CompactSupportStrictScalarComposition": {"hash": "483f6a051b46fc1b56726e8c58700c5ac93fc755", "status": "SLOW"}, "Sheaf.Paper.CompactSupportStrictScalarRefinement": {"hash": "ef52f86fbc3b0c076055fb346b07d1d0b7eaa9b3", "status": "SLOW"}, "Sheaf.Paper.CompactSupportSystemRealizationNormalization": {"hash": "3d61967d7537aa959d68b7f6983cffadfe893a0e", "status": "SLOW"}, "Sheaf.Paper.CompactSupportSystemTransposeNormalization": {"hash": "25b428d31c12c81a616cb1dc001f3fb83a593541", "status": "OK"}, "Sheaf.Paper.CompletedScalarAssociatorLocalization": {"hash": "f8769dbb26a78a73a7b2145c463949a21eb753f5", "status": "OK"}, "Sheaf.Paper.CompletedScalarExactLocalization": {"hash": "9392e473ffbd2fd004a607a31fb1e0c1ac7bac70", "status": "OK"}, "Sheaf.Paper.ConcreteIntegralProjectionCone": {"hash": "f3d4832ddb372eed3cdf9a1d5fbab9b893d2bf7c", "status": "SLOW"}, "Sheaf.Paper.ConstantCompletedOrdinaryAssociativity": {"hash": "d2d5e70664fbb5923ea1dff5ca2c4c110a8898f7", "status": "OK"}, "Sheaf.Paper.ConstantCompletedScalarAssociativity": {"hash": "2807b14af30e2bdb141949744d8bfff248a7e96e", "status": "OK"}, "Sheaf.Paper.FieldExtensionSystemCoordinates": {"hash": "d34427d04e10d80237f67676047b8cd2482c4534", "status": "OK"}, "Sheaf.Paper.FieldWeilShriekShiftData": {"hash": "5c0b9354c99c9e73728a547bd4397bc11046c209", "status": "SLOW"}, "Sheaf.Paper.FiniteOrientationReduction": {"hash": "21d8aa28f4c00c0d85f62eb3c6de40d7f2ae8a07", "status": "OK"}, "Sheaf.Paper.FiniteRestrictionDiagramNaturality": {"hash": "81365072e344a50c7cddc314c30b496374b0359e", "status": "OK"}, "Sheaf.Paper.FrobeniusSystemExchangeInverse": {"hash": "e6fbdfa18f544325b6382df9ce2cec5cb1099414", "status": "OK"}, "Sheaf.Paper.IntegralClosedAlphaNormalization": {"hash": "2c4786251b452a9d8fc15a8dafa41dd615c4cbe2", "status": "OK"}, "Sheaf.Paper.IntegralClosedReductionComparison": {"hash": "6aa063eb838301593a8aaaba6651dc9547b991e5", "status": "OK"}, "Sheaf.Paper.IntegralClosedSupportNormalization": {"hash": "6edd8cbf1e1b1d61f0eac149bb6ec224435e90cd", "status": "OK"}, "Sheaf.Paper.IntegralOpenAdjunctionTransposeNormalization": {"hash": "107a1c3be9d4e4dea3ff86ecf5087d58e074d5c8", "status": "OK"}, "Sheaf.Paper.IntegralOpenSupportNormalization": {"hash": "11be195fd04eb6eb1c10cf93311a61f0c1640984", "status": "OK"}, "Sheaf.Paper.IntegralOrientationReductionInjectivity": {"hash": "aea3ebc1e08acf42a6a261ef82db64d1861880b6", "status": "OK"}, "Sheaf.Paper.IntegralOrientationShiftedSheafModels": {"hash": "d5bd1293be3e2ea302c85bce3b9ec78a54b76c45", "status": "OK"}, "Sheaf.Paper.IntegralProjectionDirectFactorEvaluation": {"hash": "24d71629815af5545049b2ac9e815729455983ec", "status": "OK"}, "Sheaf.Paper.IntegralProjectionOpenFactorEvaluation": {"hash": "504be66d84b5efa720f8d9c7527cff1f25ecd27c", "status": "OK"}, "Sheaf.Paper.IntegralProjectionOperationPresentation": {"hash": "6e0f41f2b7151afafbd03ac47335c49b2e9dd1b1", "status": "OK"}, "Sheaf.Paper.IntegralProjectionSupportFactorCoordinates": {"hash": "c155141d262d956b48c94dedf4453c261d9a4bbf", "status": "OK"}, "Sheaf.Paper.IntegralReconstructionComparisonData": {"hash": "88ad3c07a82b68901542849f4167187c1722104d", "status": "OK"}, "Sheaf.Paper.IntegralReconstructionComparisons": {"hash": "ff879e514ff031ee4466f415e7008cada241790e", "status": "OK"}, "Sheaf.Paper.IntegralScalarIsomorphismExchange": {"hash": "4ae22ceb44b609a346cff17a1cdc8070244d97db", "status": "OK"}, "Sheaf.Paper.IntegralSupportAdjunctFiniteCoordinates": {"hash": "29822a6085d1fa21a3549b52b76ca7fd3ae0f847", "status": "OK"}, "Sheaf.Paper.IntegralSupportFunctorNormalization": {"hash": "fb1f160aeee91fa0adc2ea96d83edb1460a363a9", "status": "OK"}, "Sheaf.Paper.IntegralSupportNormalizationData": {"hash": "3dace0973f3366637a488ddbda4029a59b48dba2", "status": "OK"}, "Sheaf.Paper.IntegralSupportReductionNormalization": {"hash": "13c2c8849d429ec6a339d763cfb51f2bff6d4219", "status": "OK"}, "Sheaf.Paper.OrientationScalarTowerTransport": {"hash": "322b312084978e6ab9be061d3acdf23b186ec025", "status": "OK"}, "Sheaf.Paper.OriginalScalarMateShift": {"hash": "5db8b7beb8f7e26b60b8f32f12859e5e3e61e825", "status": "OK"}, "Sheaf.Paper.ProjectionReductionPresentation": {"hash": "ee8b6dd4180d903688860c4010b96b55a386c7e3", "status": "OK"}, "Sheaf.Paper.ProperCoefficientDescent": {"hash": "906240e63c6682f49280bcebdd034e2a01436fbb", "status": "OK"}, "Sheaf.Paper.ProperCoefficientDescentData": {"hash": "1655015a9a095e47fa17036ed42adb4505719319", "status": "OK"}, "Sheaf.Paper.PulledOrderedLineSingle": {"hash": "cb960d5ebe300e4ab392cf74c8bd9ebd8c1da9c7", "status": "OK"}, "Sheaf.Paper.RamifiedScalarSystemTranspose": {"hash": "53ac490826ec5a0fa35c7c8f9a5ca4c9b3fca77d", "status": "OK"}, "Sheaf.Paper.ScalarLimitConstraintShift": {"hash": "f761cab615b005057366311b82f73043dc93da05", "status": "OK"}, "Sheaf.Paper.ScalarLimitTensorComposition": {"hash": "2810cf04a66b8c644001cc052251062a3e141273", "status": "OK"}, "Sheaf.Paper.ScalarLimitTensorRestriction": {"hash": "b03186aa7af10fe946e58c971cbdbb0423b6e3d9", "status": "OK"}, "Sheaf.Paper.ScalarRoosComparisonUnique": {"hash": "e1d886c82ea9ed231075fee4747dab188156bafe", "status": "OK"}, "Sheaf.Paper.SectionsRationalModelComparison": {"hash": "46163f9f6f8a18e6b2778f54884309a233c3e571", "status": "OK"}, "Sheaf.Paper.SfIntegralLocalizationConstruction": {"hash": "54c926d486966e3d6c09f5e3a29ee469568e568f", "status": "OK"}, "Sheaf.Paper.SfProEtaleProjectionFormula": {"hash": "3a38fd19c04e2c191e9b5a3721527f4cf323432d", "status": "OK"}, "Sheaf.Paper.SfRationalLocalizationOrthogonality": {"hash": "efe12e2c710e23b20efd7b06d071e181613b85ef", "status": "OK"}, "Sheaf.Paper.StrictCoefficientOpenReduction": {"hash": "f1876e5850729fb357c5383e1e10d271de8ceee3", "status": "SLOW"}, "Sheaf.Paper.StrictCoefficientProperReduction": {"hash": "af1b9e0414718a8ef63be5b6a97a56a08b0f1d29", "status": "OK"}, "Sheaf.Paper.StrictScalarMateShift": {"hash": "de8a1a32235e9ccf301fb13f2e84711d746fd5a0", "status": "OK"}, "Sheaf.Paper.SystemProjectionTriangleCompatibility": {"hash": "a5c99a0942a8a6f7c864595a051a7805d58b7342", "status": "OK"}, "Sheaf.Paper.TwistedPullbackReductionData": {"hash": "472524daae4b2328c2fb0820b62c2d952b49a31e", "status": "OK"}, "Sheaf.Paper.WeilIndOpenRealization": {"hash": "20bee50fd34f46d7c0ab05d775c148474b5a3b28", "status": "OK"}, "Sheaf.Paper.ZlOpenExtensionTExact": {"hash": "4da00ee15371c466828dc33a38b9e073d71ab4e9", "status": "OK"}, "Sheaf.Paper.ZlOpenWeilUnitEmptyFibre": {"hash": "2c645bee0c85cdd5623a41dd36a150e0bb194e2c", "status": "SLOW"}, "Sheaf.SixFunctors.CoefFinitePairingEvaluationData": {"hash": "fa1044633197aec4e26ddfab3d7501c7e266918b", "status": "SLOW"}, "Sheaf.SixFunctors.CoefFiniteProjectionEvaluationData": {"hash": "e7f119beff899f9e612a24462641ba05345202c0", "status": "OK"}, "Sheaf.SixFunctors.CoefPairingFiniteNormalization": {"hash": "39e863e7542697acda44134a513f9ddf10bd9d5a", "status": "OK"}, "Sheaf.SixFunctors.CoefPairingSystemDinaturality": {"hash": "cdcfc9f9ffdb7b410ffe11d84ec900901e60f9ea", "status": "OK"}, "Sheaf.SixFunctors.CoefSystemProjectionEvaluation": {"hash": "abb9a53e452739c10aca6d5356a48b00fa6ac8ba", "status": "OK"}, "Sheaf.SixFunctors.CoefficientProjectionPointData": {"hash": "5fee030fb70027e1defdcbb3194b98e3dee6185a", "status": "OK"}, "Sheaf.SixFunctors.OpenClosedWeilMateIntegral": {"hash": "d42f07b1e8972be9600efb177069f4a042a6ce6d", "status": "OK"}}, "seconds": 484, "time": "2026-10-28T03:59:32+0800", "transitive": 74, "version": 1}
```

## Second reading by G9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
