# WeilConjectures.ordinaryIntegralDerivedPull and ordinaryIntegralCompletionComparison

## Reason

Group V2, 2026-10-25. Item Sheaf.Paper.OrdinaryCompletedIntegralPullback.

The original module places all ordinary coefficient maps, module adjunctions, total
derived pullback, quotient augmentation and completion comparison before a final
constructibility/isomorphism theorem. The final theorem's local-model argument needs
a coefficient-presentation comparison, whose data module imported those earlier
constructions from this same module. Separate the earlier declarations into
Sheaf.Paper.OrdinaryIntegralPullbackConstruction and publicly import that module
from the original. Existing public names, signatures, attributes and constructions
are preserved.
No target statement or mathematical definition changes.

Adapt ProperIntegralOrdinaryData (unclaimed in coord/claims at inspection) by replacing
its public constructor import with the new construction module. It uses no occurrence
of ordinaryCompletedIntegralPullback. ProperIntegralStrictModelComparison imports the
data module and therefore obtains the same public constructor declarations without
importing the later theorem. It also adds a direct proof import of the construction module, so its compiled
dependency records resolve the moved declarations at their new defining module. Its
public imports, statement and theorem proof remain unchanged. Its DAG and the data node cite
the construction, derived-pullback and comparison-descent nodes in place of the final
constructibility theorem node. These are reference corrections, with the Lean signatures
and mathematical assertions unchanged.

## Old

```lean
-- ProperIntegralOrdinaryData.lean
public import Sheaf.Paper.OrdinaryCompletedIntegralPullback
```

All construction declarations preceding ordinaryCompletedIntegralPullback lived in
OrdinaryCompletedIntegralPullback. Their signatures and bodies are preserved verbatim.

## New

```lean
-- ProperIntegralOrdinaryData.lean
public import Sheaf.Paper.OrdinaryIntegralPullbackConstruction
-- OrdinaryCompletedIntegralPullback.lean
public import Sheaf.Paper.OrdinaryIntegralPullbackConstruction
```

Local irreducibility is set after the computation-counit API for
ordinaryIntegralDerivedPull, ordinaryIntegralPullCounit, ordinaryTensorPull and
ordinaryTensorRingMap, and after the good-representative comparison for ordinaryIntegralPullComplex.
This prevents repeated expansion during subsequent elaboration; the definitions and
public attributes are unchanged.

The constructed adjunction comparison, augmentation and cochain counit are also locally
irreducible after their component APIs. The large private comparison-on-good-complexes
construction now refers to a named private counit natural transformation and its proved
component formula. This replaces repeated definitional normalization of the total-derived
counit in a subtype proof by one named equality. Labeled profiling identified repeated
kernel checking of ordinaryIntegralComparisonOnGood._proof_2 as a cost. These changes
alter no public signature, definition body, or exported transparency attribute.

The chain comparison is now first packaged as a private natural transformation on all
complexes and then restricted by whiskering to good complexes. Its proved component
equation is the original completion chain map. This avoids rechecking the expanded
quotient tower inside the good-complex subtype's anonymous natural transformation.
The tower functor is also locally irreducible after the chain-map API is proved.

All construction declarations now live in OrdinaryIntegralPullbackConstruction;
the original module reexports every one under exactly the original public name.
The extraction changes neither data nor a target meaning. The new module has the original
constructor declarations verbatim, apart from its module documentation, the documented
local elaboration controls and private counit helper, and omission of the final theorem.

## Users

The current downstream census has 119 modules, all listed below together with
the item. No public declaration signature or definition body changes. Only
ProperIntegralOrdinaryData, ProperIntegralStrictModelComparison and
FiniteProjectiveModelPullback require import adaptations;
all other consumers retain the existing public reexport. ProperIntegralOrdinaryInputs
continues to import the final theorem explicitly. The sole import-all consumer of the
original module is FiniteProjectiveModelPullback, whose proof uses the moved private
constant-section helpers and therefore imports the construction module with import-all.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.DeligneLaumon.FiniteStageFibreVanishing | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.DeligneLaumon.QbarCurveDuality | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.DeligneLaumon.RawHeartAdicLisseStratification | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.AdicCommonStageHomTranspose | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.AdicCompactificationSectionRealization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.AdicHomTensorLisseCriterion | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.AdicMiddleExtensionConstructible | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.AdicNormalizedPurityLift | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.AdicOperationDomainsSourceComparison | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.AdicProperAdjunctionRealization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.AdicSectionCanonicalModels | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.AffineCommonProjectiveCharts | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.AnchoredPureCurveCriterion | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.BoundaryHomVanishing | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.CartesianSectionAdjointMates | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.CartesianSectionData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalFiniteWeilDiagramRealization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilFrontierRestriction | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalLisseWeilRestrictionMaps | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreComparison | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalNormalizedTwoFibreData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCoherence | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonFibres | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRealization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestriction | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonRestrictionData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseCommonSystem | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseOperations | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLissePointFibres | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseRealizationData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalRawLisseScalarCoherence | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalSystemRawLisseRealization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreCommonData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalTwoFibreScalarData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClassicalWeilFiltrationHeartTransport | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ClopenProjectiveChartCommonRefinement | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.CommonAdicCompactificationSectionData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.CommonAdicOpenSectionData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.CompletedLocalFibreComparisonData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ConstructibleProjectiveChartRefinement | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ConstructibleResidueTree | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.CurveIntermediateExtension | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.CurveRestrictionFiltrationSpectrum | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.DlConstantFieldCharts | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicCompactificationSectionData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicImageNormalization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicOpenSectionData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicOrdinarySectionData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicProperSectionData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.FiniteAdicSectionRealizationCore | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.FiniteAdjointMateCompatibility | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.FiniteDiagonalOrientationReduction | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.FiniteDncNormalizationReduction | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.FiniteGeometricSectionsPointOrbits | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.FiniteProjectiveModelPullback | unclaimed | Private proof import redirected for the two moved constant-section helpers. |
| Sheaf.Paper.FiniteRestrictionCoefficientDescent | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.FiniteRestrictionGeometricArrows | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.GeometricQuotientWeilCompositionSeries | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.LevelwiseNormalizedAdjointDescent | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.LisseCohomologyDerivedDual | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.LisseFieldNormalization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.LisseLatticeHeartLift | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.LissePointNormalization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.LissePointSectionsRealization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.LissePullbackNormalization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.LisseRationalRealization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.LisseRationalRealizationData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.LisseShortComplexCommonStageExactness | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.LisseTensorNormalization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.LisseTensorPullbackRealization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.LocalFrobeniusLargeCoefficients | U9 | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.MiddleExtensionHcZero | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.MiddleExtensionSectionRestriction | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.NativeProperCoefficientOperations | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.NativeProperTensorComparison | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.NormalizedClassicalWeilRealization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.NormalizedFiniteFibreModels | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.NormalizedFiniteRealizationFibre | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.OrdinaryCompletedIntegralPullback | V2 | Public reexport preserves every constructor; final proof completed. |
| Sheaf.Paper.OrdinaryPullbackStratifiedModels | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ProperIntegralOrdinaryData | unclaimed | Constructor import redirected to avoid the theorem cycle. |
| Sheaf.Paper.ProperIntegralOrdinaryInputs | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.ProperIntegralStrictModelComparison | unclaimed | Add a direct constructor proof import; same public statement and proof. |
| Sheaf.Paper.QcqsCompletionUnitLocality | E3 | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.RamifiedScalarSystemTranspose | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.RationalDirectImageRealization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.RationalHomScalarTranspose | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.RationalVerdierEvaluationAdjoints | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.SfBidualityClass | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.SfPackageExceptionalCoherenceRealization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.SfPackageFieldOperationRealization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.SitePerfectRationalBidual | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.SystemProjectionFormulaCoherence | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.SystemScalarProjectionIdentification | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.VerdierCoefficientRealization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.WeilChosenDualityExchange | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.Paper.WeilOpenImageDelta | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.SixFunctors.CoefDualFormulaScalarTranspose | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.SixFunctors.CoefQbarVerdier | V1 | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.SixFunctors.CoefVerdierWeilEquivariance | V3 | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionDiagramRealization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteAdjunctionSystemData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteExceptional | X3 | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateData | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.SixFunctors.FiniteScalarMateRealization | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralDualExceptionalSystem | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalDescendedCounit | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingAdjunction | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.SixFunctors.IntegralExceptionalMappingSystem | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.SixFunctors.RationalOperations | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.SixFunctors.RationalRetractEvaluation | unclaimed | Same public names, types and constructions through reexport; no adaptation. |
| Sheaf.SixFunctors.WeilChosenDualityHom | unclaimed | Same public names, types and constructions through reexport; no adaptation. |

## Status

landed 20261025T101620-L-3714355 2026-10-25 (merge of deliver/V2/Sheaf.Paper.OrdinaryCompletedIntegralPullback)

Check edge cases: the direct local-model pullback argument admits zero complexes,
empty schemes and empty strata. It retains the whole finite index set; an empty stratum
has the pulled-back covering sieve. No nonemptiness or flat structural ring map is assumed.
Scalar perfection is retained from the original model, not inferred for a different object.

Validation and timing will be recorded in report.md after the final compilation.
