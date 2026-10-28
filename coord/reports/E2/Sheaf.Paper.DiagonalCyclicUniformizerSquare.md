## What changed

`diagonalCyclic_uniformizerSquare` retains its original statement and public
import. Its body combines two independent endpoint calculations using naturality
of an explicitly constructed derived mate. The mate comes from the actual scalar
adjunctions and finite-realization equivalences, not from an assumed class square.

The realization identities are proved: the cyclic one expands the specified
reduction, and the successive one composes both supplied
`ScalarCompatibility.delta` equations. A general category calculation cancels the
source isomorphism; a proved Ext/Hom calculation translates the result to the
original Yoneda square. The helper definitions construct all their data explicitly. `FiniteRouteData`
bundles the realized functor, both endpoints and a proved realization method for
every compatible arrow. The two concrete endpoint bundles are constructed before
any arrow is supplied; their data is independent of the subsequent application
of that method. This shares the endpoint types without unfolding large derived
functors at every use. Its class-map family and compatibility predicate are named
functions, so projection types retain these expressions by name. Each route's
three field aliases have their own module; the ordinary scalar maps and initial
objects are in `DiagonalCoefficientRouteEndpoints`.

`DiagonalFiniteRouteDataCore` contains the shared record, input predicate and
explicit class-map family. `DiagonalFiniteRouteData` constructs that record using
the proved realization method. Their names and bodies are preserved; separating
the declarations keeps their individual kernel checks below the per-file limit.

The successive scalar functor and its adjunction also retain the coefficient
objects carried by `ScalarCompatibility`, rather than reconstructing them from
`integralMap`. This keeps the common source as `continuousMapRingObj` throughout;
reconstructing it independently picked the definitionally equal specialized
`padicIntegersRingObj` and made Lean repeatedly expand its category data.

The proved realization identities use the shared route data. The specializations
`cyclic_realization`, `successive_square` and `quotient_realization` inherit their
types from the proved generic composition or the bundle method, avoiding a second
elaboration of the coefficient categories. Their bodies are complete proof terms.
The cyclic identity supplies the explicit cyclic input arrow and uses Mathlib's
`Iso.hom_inv_id_assoc` directly. Its application to the criterion checks the
existing definition of `CyclicCartierFrame.reduce`.

Local term elaborators emit Lean's primitive structure projections. They reuse
the category arguments stored in the bundle's type and produce ordinary terms
checked by the kernel.

The ordinary restriction functor retains `diagonalResidue`, matching the cyclic
finite realization. The explicit `residueMap`, `sourceMap`, and `lineMap` are the
supplied algebra, pushed source, and root-line maps with those types retained.
This avoids repeated conversion from `cartierResidueRing` and recomputation of
restriction/direct-image compatibility. The scalar composition uses the project's
existing pro-étale monoidal structures, matching `Modules`.

The endpoint equations recover the domain and codomain of the supplied initial
arrow via `Arrow.mk`; this discards its value and preserves the exact endpoint
types. No equation about that arrow is added to either endpoint lemma.

The supported and shifted-line endpoints share their generic constructions.
Their domain objects are the supplied source and shifted line. Their types use
the functor and endpoint fields of the shared bundles. This avoids repeating functor-composition
and coefficient-object conversions. These thin endpoint wrappers are abbreviations
of their shared constructions. The generic criterion eliminates the source
existence proposition inside its proved body; the concrete criterion specializes
that proof to the actual routes. The final theorem uses the proved application chain for the four
independent endpoint and realization results. The local
ring, abelian and monoidal instance preferences select existing library structures; no source-library definition,
instance, attribute or public import is changed. The new modules prefer the named
`diagonalModuleSheafAbelian` instance where inference has not already determined
the structure. Stored predicate expressions retain the category instances of
the constructed routes.

The two endpoint statements reuse the first two hypothesis types stored in the
proved `endpointSquare` criterion. Their local signature elaborators emit the
ordinary quantified endpoint formulas, with the criterion's category-instance
expressions retained. The source predicate is the unique normalized restriction
comparison with its supported-constant equation; the target predicate quantifies
over every normalized comparison and asserts its positive-root equation. The
elaborator checks that the target predicate has no dependency on the source
proof. Their mathematical hypotheses and conclusions are unchanged. Lean checks every emitted formula and proof term with its kernel.

## Proved and sorry left

The original hole in
`AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCyclic_uniformizerSquare`
is replaced by a complete combining proof. This is a decomposition, not a full
proof of the mathematical obligation: one upper hole is closed and two strictly
smaller endpoint holes are added, for a net of -1.

The proved helper identities are `finiteArrowClass_hom`,
`finiteRealizedClass_eq_arrowClass`, `finiteRealizedClass_hom`,
`finiteRealization_compositionCore`, `finiteRealization_composition`,
`ScalarCompatibility.composite_delta`, and
`FiniteRouteData.realize` in the explicit constructor and
`UniformizerSquareData.cyclic_realization`, `.successive_square`, and
`.quotient_realization`. The private category and Ext lemmas in
`DiagonalExtMateSquare`, its public `finiteCoefficient_extSquare_of_endpoints`,
and the concrete `UniformizerSquareData.endpointSquare` criterion are completely
proved. The proved helper modules split the large concrete kernel check without
adding assumptions or holes. The final application uses ordinary function application and `exact`;
Lean checks it against the original equation. The proof-valued definitions `sourceSquare`, `targetSquare`,
`cyclicSquare` and `realizedSquare` supply its four proof arguments one at a time;
their bodies are also complete. Their proof dependencies are public imports
because Lean must infer these definitions before knowing their result is a
proposition.

The only new holes are:

- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCyclic_uniformizerSource`:
  the unique normalized ordinary restriction comparison and its supported-constant
  endpoint (node `lem-diagonal-cyclic-uniformizer-source`). Its conclusion contains no root endpoint or initial-arrow equation.
- `AlgebraicGeometry.ProEtale.DiagonalCoefficients.diagonalCyclic_uniformizerTarget`:
  the positive-root endpoint of the constructed mate for any normalized ordinary
  restriction comparison (node `lem-diagonal-cyclic-uniformizer-target`). It
  assumes no source endpoint or class equation.

Each has its source, complete natural-language proof and blueprint identifier in
its docstring, with a corresponding new DAG node. Every other new theorem is
proved. No definition selects mathematical data from the source existence theorem. The source
existence theorem is eliminated only within the final proposition's proof.

The endpoint proof plans cover exponent n=0, the empty scheme and the zero
coefficient ring. They add no flatness or invertibility hypothesis.

## No longer needed

The new explicit composition core imports `DiagonalCyclicCartierFrame` directly,
rather than importing it through `DiagonalFiniteRealizationEndpoints`; it does not
use the named endpoint wrappers. Those wrappers remain needed by both routes.

The two concrete realization modules use the bundle's proved `realize` method;
they do not import the generic composition theorem directly. That theorem remains
needed by `finiteRouteData`, so its module and node stay in the proof closure.

The private `iso_square` helper was removed; the cyclic calculation uses
Mathlib's existing `Iso.hom_inv_id_assoc`.

None of the original mathematical dependencies is pruned. The coefficient maps,
scalar compatibility, finite realization and root interfaces remain necessary
for the two endpoint calculations. No original import, node, module, unit
statement or realized unit step is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The snapshot's old build-error file reported a missing root-frame import, but the
original item compiled against the published artifacts. The assigned work is its
existing proof hole.

The DAG described the supported-constant and positive-root calculations in prose
without corresponding endpoint theorems. Those steps are now separate statements;
the remaining realization and naturality argument is implemented in Lean. No
mathematical statement is disputed or weakened.

## New nodes

All modules below are under `Sheaf.Paper`.

`def-diagonal-finite-realization-endpoints` — `DiagonalFiniteRealizationEndpoints`: Explicit realized source and shifted-target constructions.

`def-diagonal-finite-realized-class-core` — `DiagonalFiniteRealizedClassCore`: Explicit Ext constructor and its proved comparison with the existing finite class.

`lem-diagonal-finite-realized-class-hom` — `DiagonalFiniteRealizedClassHom`: Proved formula for the derived representative.

`lem-diagonal-finite-realization-composition-core` — `DiagonalFiniteRealizationCompositionCore`: Proved explicit single/shift calculation.

`lem-diagonal-finite-realization-composition` — `DiagonalFiniteRealizationComposition`: Proved realization of an arbitrary supplied endpoint square, using shared endpoints.

`lem-diagonal-scalar-arrow-composition` — `DiagonalScalarArrowComposition`: Generic composite endpoints and proved composition of both scalar delta equations.

`def-diagonal-coefficient-route-endpoints` — `DiagonalCoefficientRouteEndpoints`: Actual two route functors, restriction and realized endpoints.

`def-diagonal-coefficient-route-comparison` — `DiagonalCoefficientRouteComparison`: Actual composite adjunctions, normalized restriction comparison and its derived mate.

`def-diagonal-coefficient-route-equations` — `DiagonalCoefficientRouteEquations`: Separate source and target endpoint propositions.

`lem-diagonal-cyclic-uniformizer-source` — `DiagonalCyclicUniformizerSource`: Remaining supported-constant calculation.

`lem-diagonal-cyclic-uniformizer-target` — `DiagonalCyclicUniformizerTarget`: Remaining positive-root calculation.

`lem-diagonal-coefficient-route-realization` — `DiagonalCoefficientRouteRealization`: Proved cyclic realization identity.

`lem-diagonal-uniformizer-route-compatibility` — `DiagonalUniformizerRouteCompatibility`: Concrete specialization of the proved scalar composition.

`lem-diagonal-uniformizer-route-realization` — `DiagonalUniformizerRouteRealization`: Proved successive realization identity.

`def-diagonal-finite-route-data` — `DiagonalFiniteRouteData`: Explicit realized endpoints and their proved universal arrow calculation.

`def-diagonal-coefficient-route-data` — `DiagonalCoefficientRouteData`: Concrete endpoint bundles for the two coefficient routes, independent of the supplied arrow.

`def-diagonal-cyclic-route-endpoints` — `DiagonalCyclicRouteEndpoints`: Fields of the explicitly constructed cyclic endpoint bundle.

`def-diagonal-uniformizer-route-endpoints` — `DiagonalUniformizerRouteEndpoints`: Fields of the explicitly constructed successive endpoint bundle.

`lem-diagonal-ext-mate-square` — `DiagonalExtMateSquare`: Proved generic cancellation, naturality and Ext/Hom criterion.

`lem-diagonal-coefficient-route-square` — `DiagonalCoefficientRouteSquare`: Fully proved specialization to the actual coefficient routes, retaining four independent proof arguments.

`lem-diagonal-coefficient-source-square` — `DiagonalCoefficientSourceSquare`: Supplies the source endpoint theorem to the proved criterion.

`lem-diagonal-coefficient-target-square` — `DiagonalCoefficientTargetSquare`: Supplies the independent target endpoint theorem.

`lem-diagonal-cyclic-class-square` — `DiagonalCyclicClassSquare`: Supplies the proved cyclic realization.

`lem-diagonal-uniformizer-class-square` — `DiagonalUniformizerClassSquare`: Supplies the proved successive realization, completing the actual Yoneda square.

`def-diagonal-finite-route-data-core` — `DiagonalFiniteRouteDataCore`: Shared input predicate, record and explicit class-map family, separated from the proved constructor.

## Related modules compiled before delivery

106 related module(s) compiled against this delivery by deliver3.py: 2 INFRA, 98 OK, 6 SLOW.

```json
{"capped": false, "direct": 1, "left_out": 0, "own": {"Sheaf.Paper.DiagonalCoefficientRouteComparison": "895eff54fc82eaf8daee150c931f9e0f28e626b2", "Sheaf.Paper.DiagonalCoefficientRouteData": "96ae4b9b4c7276db75fe507f0fc32b9e598ae409", "Sheaf.Paper.DiagonalCoefficientRouteEndpoints": "6bec41c201d36ff546dd02cb847a5256dc0b8d09", "Sheaf.Paper.DiagonalCoefficientRouteEquations": "838c6d652f119da68a60fcddfefc85bb239c140d", "Sheaf.Paper.DiagonalCoefficientRouteRealization": "5ada20bc11486fb0b9517cb7e35de3d4e5b66155", "Sheaf.Paper.DiagonalCoefficientRouteSquare": "c753b47281b7788360898dac0da01be2e2ebe7b5", "Sheaf.Paper.DiagonalCoefficientSourceSquare": "385d02e5154ce999fa7205b4fb8f0c191e20bfab", "Sheaf.Paper.DiagonalCoefficientTargetSquare": "44d1933c19e273e6181d40a48fbd76e50fa488d6", "Sheaf.Paper.DiagonalCyclicClassSquare": "f0ebb632c7f079a74a5675680183bc75ca07269f", "Sheaf.Paper.DiagonalCyclicRouteEndpoints": "c7ab036bd0a369289bfc681bc0cdee3720b726e7", "Sheaf.Paper.DiagonalCyclicUniformizerSource": "8b1a183c055dc0479ac14f57d9fdb0bdac58f15b", "Sheaf.Paper.DiagonalCyclicUniformizerSquare": "81e867dea88b79d8afdd856d1f08cc2c5c8a424e", "Sheaf.Paper.DiagonalCyclicUniformizerTarget": "75269f9c6e2a8d2ee78ad8cc314bcba1e226c181", "Sheaf.Paper.DiagonalExtMateSquare": "7816e1329b47dfd7ece55af92cc93902e6a9fbff", "Sheaf.Paper.DiagonalFiniteRealizationComposition": "572b415061794019ecf0a2f64b86278e4de7ed53", "Sheaf.Paper.DiagonalFiniteRealizationCompositionCore": "35a6681bccd7c4b01b66ffa81c9a387d51b6594d", "Sheaf.Paper.DiagonalFiniteRealizationEndpoints": "c005daf21043784e654f647ad67a477c31b01b70", "Sheaf.Paper.DiagonalFiniteRealizedClassCore": "96dd98ffc707e6379cc396a1f4ae932152315fe0", "Sheaf.Paper.DiagonalFiniteRealizedClassHom": "1aef55acad07f86103e6dcfbc4d65b44769a88db", "Sheaf.Paper.DiagonalFiniteRouteData": "430c600dec1f91388aa84fe505be68d8a0a7bee8", "Sheaf.Paper.DiagonalFiniteRouteDataCore": "4064dd4a47295352dbf5efeb149fe7809de061b4", "Sheaf.Paper.DiagonalScalarArrowComposition": "d9ed81d6ab4771df9de27549f36513398506abcc", "Sheaf.Paper.DiagonalUniformizerClassSquare": "a5d21201c1ca3018f82a70d4c7681a25a95cf2d8", "Sheaf.Paper.DiagonalUniformizerRouteCompatibility": "183e710601491a24f280ff8f5eaf9fb0f348a0ae", "Sheaf.Paper.DiagonalUniformizerRouteEndpoints": "b28992744a47aa5ca18f3f59c5634b645127d763", "Sheaf.Paper.DiagonalUniformizerRouteRealization": "719e5f48f0496d298bb87f59ff50aa8310449f9e"}, "results": {"Sheaf.DeligneLaumon.QbarCurveDuality": {"hash": "698919cd1c65cfbd98e0a94220b347ea95489629", "status": "OK"}, "Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity": {"hash": "aad6b959ad4c884b495b276a87eaff7d8ccc1135", "status": "OK"}, "Sheaf.Paper.AdicPurityScalarNaturalityData": {"hash": "28cc25b50afc3cb7b673c86c4f6d7336fa5e2b86", "status": "OK"}, "Sheaf.Paper.AdicTraceTransposeData": {"hash": "a9189dc1d7e5d889986caf1e60baa388d51a053e", "status": "OK"}, "Sheaf.Paper.AdicUnitTraceReductionData": {"hash": "6fde2b47349c9ae9165093fb269a39ccfaf9ce1b", "status": "OK"}, "Sheaf.Paper.AdicUnitTraceScalarData": {"hash": "b9e2298d743b1e198d897f0ed6561d94c9c10346", "status": "OK"}, "Sheaf.Paper.AffineSpaceProductDomain": {"hash": "63629d017a7de1e8479da6346199ca85e3da75a0", "status": "OK"}, "Sheaf.Paper.CartesianSectionAdjointMates": {"hash": "46876cbeb310d6a668c0ce01483ad439a761dfed", "status": "OK"}, "Sheaf.Paper.CompactSupportProjectionFormula": {"hash": "9d8a08bf4a6d4025a7ffc9ce8b51e70bcc8ad44a", "status": "OK"}, "Sheaf.Paper.CompactSupportProjectionIntegralStages": {"hash": "9e7579cfe54e6968fbb0134e039a5f62d67399ca", "status": "OK"}, "Sheaf.Paper.ConcreteIntegralProjectionCone": {"hash": "f3d4832ddb372eed3cdf9a1d5fbab9b893d2bf7c", "status": "SLOW"}, "Sheaf.Paper.CondensedCompositorRealizationData": {"hash": "a0c7b3b8f4c75aba5a0683ba8ad1d550af600aee", "status": "OK"}, "Sheaf.Paper.CondensedCompositorRealizationSquare": {"hash": "e3186c1b28171ea2655f06c3eb4fb103ac186cb7", "status": "OK"}, "Sheaf.Paper.CondensedExceptionalReconstruction": {"hash": "c4b5052a58716274d7cee2620a16b289055c0e59", "status": "OK"}, "Sheaf.Paper.CondensedExceptionalReconstructionData": {"hash": "fdebf090817919002878b9f558bbbb7739915132", "status": "OK"}, "Sheaf.Paper.CondensedOpenCounitComparisons": {"hash": "d15a0f84ad12ce316c6c1d36de6f3af07d8f56d8", "status": "OK"}, "Sheaf.Paper.CondensedOpenCounitUnits": {"hash": "f6992093322faef0c8d2cc2c308093e13e78eae6", "status": "OK"}, "Sheaf.Paper.ConstantPurityFrobeniusSquare": {"hash": "57e1afb9cc6da75a28f05ec3856b5b1c77ee5d7b", "status": "SLOW"}, "Sheaf.Paper.DiagonalUniformizerCartierReduction": {"hash": "31bc10594a19e20c3edaef3a809ace95a53855bf", "status": "OK"}, "Sheaf.Paper.ExceptionalReconstructionComparison": {"hash": "d2808d06efb721bf1bf12ac544724e77a081cd54", "status": "OK"}, "Sheaf.Paper.ExceptionalReconstructionContext": {"hash": "65c9f8438b968b80d5fe5810cfd41538f8456aac", "status": "OK"}, "Sheaf.Paper.FieldProjectionRefinementSquare": {"hash": "872ee5a8124cdab9bf8c30cf3144ed29664e55de", "status": "OK"}, "Sheaf.Paper.FiniteOrientationScalarPresentation": {"hash": "78618ec802a17cc9731355406f51974f80b7a7fd", "status": "OK"}, "Sheaf.Paper.FiniteProductScalarPresentation": {"hash": "bbf8b546b63da982812871a899053f96cd2e48de", "status": "OK"}, "Sheaf.Paper.FiniteProjectionOpenAssembly": {"hash": "913d6d6fb54946b63d9a97c09cc89146e429a235", "status": "OK"}, "Sheaf.Paper.FinitePurityCounitSystem": {"hash": "0b0bc7ef25aed819debf022434a329c99d0f7df4", "status": "OK"}, "Sheaf.Paper.FixProjectionCompactificationComparison": {"hash": "80c036e73cecd5c5ddaddab18bc4a5fb3acd6de1", "status": "OK"}, "Sheaf.Paper.GeneralHomComparisonCocycles": {"hash": "d868c7f7d9bcfda76be62f0fec6e271641b39e6e", "status": "OK"}, "Sheaf.Paper.IntegralGeometricComparisonData": {"hash": "cc2707568a162b346675b69ebc8591da39fe2c52", "status": "OK"}, "Sheaf.Paper.IntegralOrientedExchangeSquares": {"hash": "07b26e0002ab4b2de16e89bac7a69e976dce1fbf", "status": "OK"}, "Sheaf.Paper.IntegralProjectionFiniteEvaluation": {"hash": "e2d9151a80a1b1f7db95a6e2203057ac2e64654e", "status": "OK"}, "Sheaf.Paper.IntegralPurityComparisonCocycles": {"hash": "f88677315b5409399d6a6c40be1c5c5844bfc678", "status": "OK"}, "Sheaf.Paper.IntegralPurityCounitReduction": {"hash": "fd3df8be2f2fe5b901eefcdcc20aa0d5b1dcf113", "status": "OK"}, "Sheaf.Paper.LevelwiseNormalizedAdjointDescent": {"hash": "a4687df1819afbc07bab1fc04f44745ad084ca18", "status": "OK"}, "Sheaf.Paper.NormalizedIntegralPurityTrace": {"hash": "f4fb93ec1e6587a42edde62a87ff1896a1bb9bbe", "status": "OK"}, "Sheaf.Paper.NormalizedOrientationPerfectDuality": {"hash": "145740e6c5f67bc36ee7e1685fb1db5db7f77808", "status": "SLOW"}, "Sheaf.Paper.NormalizedSupportEtalePresentation": {"hash": "fa601f0943ff51e883af75e7cc7fc472b4062056", "status": "OK"}, "Sheaf.Paper.ProjectionFiniteReduction": {"hash": "7f646f7a6793629c9eaa822c2ac53475d5ed7e31", "status": "OK"}, "Sheaf.Paper.ProjectionFormulaCoherence": {"hash": "13929edce12d5ca05c2586b744f63881a5c1f9f4", "status": "OK"}, "Sheaf.Paper.PurityCompactSupportTransport": {"hash": "bd575c8bed97e5acdde9930afcba36f3c3b054aa", "status": "OK"}, "Sheaf.Paper.RamifiedScalarSystemTranspose": {"hash": "53ac490826ec5a0fa35c7c8f9a5ca4c9b3fca77d", "status": "OK"}, "Sheaf.Paper.RationalScalarTransposeCompatibility": {"hash": "d81b0d131c7293f30241b16ef1f8f825959c5914", "status": "OK"}, "Sheaf.Paper.RelativeProductBaseChangeFactorSquares": {"hash": "24904ca5226686499904fe259df5b17441d1da0b", "status": "SLOW"}, "Sheaf.Paper.SfBidualityClass": {"hash": "3d09b2271a532ea090a93820751ad92e2f041e90", "status": "OK"}, "Sheaf.Paper.SfCoefficientComparisonConclusions": {"hash": "a6ffb793d5941b2a35b6a2e6ad8f462561e43db2", "status": "OK"}, "Sheaf.Paper.SmoothOrientationStageExchange": {"hash": "ee76f98b9e44088ec57690adf03346358795026a", "status": "OK"}, "Sheaf.Paper.SmoothPurityFieldExtension": {"hash": "36d0f00aa8e308dc40784530671db8587573904f", "status": "SLOW"}, "Sheaf.Paper.SystemScalarProjectionData": {"hash": "6e6a70ab41d6f19ceee232ba81eb824f4b6f89c8", "status": "OK"}, "Sheaf.Paper.SystemScalarProjectionIdentification": {"hash": "1c756cefdef2387f213274b53f0077c897f22016", "status": "OK"}, "Sheaf.Paper.SystemScalarTensorConstituents": {"hash": "096756fb6038c07c81567f421c86a658ef0c40a6", "status": "OK"}, "Sheaf.Paper.TensorHomCoefficientTransposes": {"hash": "ffd4867a03cd4cee9a6d2500bba78f5f452bc5eb", "status": "OK"}, "Sheaf.Paper.TensorHomExchange": {"hash": "220d046d5b668a7f1aaab68abea931d9b7b3f9b2", "status": "OK"}, "Sheaf.Paper.TowerPurityRealizedData": {"hash": "48a3c43647f30e5b85d3ad06b7ebe334a902b04d", "status": "OK"}, "Sheaf.Paper.WeilChosenDualityExchange": {"hash": "83a2d19a6418f03a623027e4b1036b475bcc5429", "status": "OK"}, "Sheaf.Paper.WeilChosenDualityExchangeData": {"hash": "5cde62e4f890ccabacce5ef9c5939f73d2d2b6ee", "status": "OK"}, "Sheaf.SixFunctors.CoefDualFormulaScalarTranspose": {"hash": "0f7df824dd97c32746df97be275b1933e9025c38", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionBetaReductionSquare": {"hash": "e9bc055b7b2428d1c1a68c75837fd719cb27786a", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionCore": {"hash": "0a1aee71c28d60cfb9a9acf7830178acf5b1b529", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionHomReductionSquare": {"hash": "34ed5b216357820b46e33d90f12c2323423b27a7", "status": "OK"}, "Sheaf.SixFunctors.CoefIntegralFiniteExtensionReductionPairing": {"hash": "2b784b1215f0423449be5c100624ed7b610ba08b", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarFiniteExceptionalCore": {"hash": "5080a3c353fcd0e376a8da8f074cbc7dae318184", "status": "INFRA"}, "Sheaf.SixFunctors.CoefQbarFiniteExceptionalCoreNaturality": {"hash": "d50f6ed7519f191ae33bb4304c8d981cf4bba11c", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarFiniteExceptionalFormula": {"hash": "a1e3b69d6893c46fff72dc3d50dcd5d46d7ef81e", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarFiniteExceptionalScalar": {"hash": "d28e1cf58a5052e7ca04dacc2dfd17fb705b4b8d", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierCore": {"hash": "9e958454f1e189dec671106840380e92f3724fdc", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierCoreEquations": {"hash": "54a843d825394530e98b48aacd7705138a496eeb", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierData": {"hash": "d25f0b76e5fc624b6b4cfe79dfbc577aef15f376", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierDualInclusion": {"hash": "1eaf5d2109b6aff5ef28a25e028981d3dd7dfa18", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierEvaluationRepresentatives": {"hash": "97ea3b309a94da006b8a4c8fbc0287416bd154a0", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierExceptional": {"hash": "807b526093da108aa223c17704358fc4c6826b8c", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierFiniteCoherence": {"hash": "cb055b11812e35ec2fe912400b12adf965f50478", "status": "SLOW"}, "Sheaf.SixFunctors.CoefQbarVerdierFiniteEvaluationStage": {"hash": "ca0fb762ff05bb48a3dc5ef6f56a46c5118bed5d", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierHomComparisonComponents": {"hash": "50c2303f28830e57a23f5511fe5036681f686ea6", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierInternalHom": {"hash": "1d723423e9adea8fd21909e1a5684d1b675e0850", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierInternalHomUniversal": {"hash": "73c2eb7db91047a00ed29e0e2be7fb1a89044b0b", "status": "OK"}, "Sheaf.SixFunctors.CoefQbarVerdierTensorInclusion": {"hash": "e1b021e95f7241ae19e4a9ab57f7650af3d71bca", "status": "OK"}, "Sheaf.SixFunctors.CoefVerdierWeilData": {"hash": "acc671d6ece089f581c6cc4f502ab4cf7b0fcdaa", "status": "OK"}, "Sheaf.SixFunctors.CoefWeilExceptionalCompatibility": {"hash": "add67b0187599655d011c82c04faaaef8fca3b1e", "status": "OK"}, "Sheaf.SixFunctors.FiniteAdjunctionSystemData": {"hash": "5384396ad97a828cbff89189041d95c436c8e3ad", "status": "OK"}, "Sheaf.SixFunctors.FiniteExceptionalData": {"hash": "85df0f9a9ac89db058592787a7773abfe5d6b2be", "status": "OK"}, "Sheaf.SixFunctors.FiniteScalarMateData": {"hash": "6d833127857194ca1793a47e528ebd6b11472d2d", "status": "OK"}, "Sheaf.SixFunctors.IntegralDualizingExceptionalUnitBridge": {"hash": "5bab0b8a6b84e3360f4968fcf971bee4d5291a9b", "status": "OK"}, "Sheaf.SixFunctors.IntegralVerdier": {"hash": "26cc57e04421a4b0121abccdc539c11c22af323a", "status": "OK"}, "Sheaf.SixFunctors.IntegralVerdierModels": {"hash": "691a143ac760a340fa99e3fb5d20e598f62860b6", "status": "OK"}, "Sheaf.SixFunctors.IntegralVerdierReductionPairing": {"hash": "58c56be144a113d9466062fc6e01ba30e3ef2e28", "status": "OK"}, "Sheaf.SixFunctors.IntegralVerdierReductionPairingDelta": {"hash": "e3b727db22e8a97ccf4811eb97e53087f353632a", "status": "OK"}, "Sheaf.SixFunctors.IntegralVerdierReductionPairingDeltaUncurried": {"hash": "7f8952df455e47ea9cd107f9511f01981c74d410", "status": "OK"}, "Sheaf.SixFunctors.IntegralVerdierReductionPairingTransition": {"hash": "d0a105450665f3b9d9bc2d7eb9f9df7b5e8a2157", "status": "OK"}, "Sheaf.SixFunctors.IntegralVerdierSignedCalculus": {"hash": "ed1dbd048bd09c9547ed901e651607feaf98119e", "status": "OK"}, "Sheaf.SixFunctors.RamifiedScalarExceptionalLimit": {"hash": "723650115b6c043294a725a7f6282c8137a23ea8", "status": "OK"}, "Sheaf.SixFunctors.RationalDualFormulaScalarCounit": {"hash": "d01de62cfa12860103b2a29f0307f6d1b9e1f463", "status": "OK"}, "Sheaf.SixFunctors.RationalExceptionalIdentifications": {"hash": "0ca8a052072442611d18f9edf7baef6a53d58f84", "status": "OK"}, "Sheaf.SixFunctors.RationalOperationsData": {"hash": "6e1c802189be17ac7cce9014d9935851da7c4c8b", "status": "OK"}, "Sheaf.SixFunctors.RationalVerdierComparisonBiduality": {"hash": "c2e39586fbcce4f5f39e537c4d35dd316f27549a", "status": "OK"}, "Sheaf.SixFunctors.RationalVerdierComparisonEvaluation": {"hash": "196e72a39aa1a5e37100add2794fbcdceb0566b2", "status": "OK"}, "Sheaf.SixFunctors.RationalVerdierComparisonEvaluationIntegral": {"hash": "8a567e9e18e95e57719dd681bc9062ed585c4222", "status": "OK"}, "Sheaf.SixFunctors.RationalVerdierComposition": {"hash": "c5470d96143d3b2f3cab14db26d0fe4c1286029f", "status": "OK"}, "Sheaf.SixFunctors.RationalVerdierCompositionEquation": {"hash": "c6a378cee2397dc18299c71361d6a0f6abb6366f", "status": "INFRA"}, "Sheaf.SixFunctors.RationalVerdierLocalizedComposition": {"hash": "06c77bc2545270933e40bc226026cba8bb939685", "status": "OK"}, "Sheaf.SixFunctors.RationalVerdierModels": {"hash": "3c72030abeb75a13846476b5ca4679ec14e9a9cd", "status": "OK"}, "Sheaf.SixFunctors.RationalVerdierUnit": {"hash": "e081a603b11fabad18bf5890986d045a22e24cd9", "status": "OK"}, "Sheaf.SixFunctors.WeilChosenDualityHom": {"hash": "27dd3c66aec9161437056b59c8ca303302abd8aa", "status": "OK"}, "Sheaf.WeilSheaf.DualRealizationComparison": {"hash": "a4c7aed1bf1cface6c840589f93a3d310530ca70", "status": "OK"}, "Sheaf.WeilSheaf.NativeBidualEvaluationRealization": {"hash": "237c3de53410c930efdb5d8359bcec22e4f96f2b", "status": "OK"}, "Sheaf.WeilSheaf.NativeDualRealizationComparisonData": {"hash": "a583cf0fc17098bae4da272cf5517b4d7e9f799f", "status": "OK"}, "Sheaf.WeilSheaf.StructuralBidualInvertible": {"hash": "86e30fe2b8d9b87dbbdb3f36423e71736b903e75", "status": "OK"}}, "seconds": 622, "time": "2026-10-28T12:30:57+0800", "transitive": 105, "version": 1}
```

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
