# WeilConjectures.SfAlgebraicallyClosedCoefficients.stageCategory

## Reason

The old cache elaborates to a Category record whose CategoryStruct is the
projection of the existing ScalarLocalization.category and whose law fields are
its laws. Repeated conversions through this expanded record slowed the kernel
when comparing the scalar pentagon and the stage-system specifications. Return
the same constructed category instance directly. Its Hom, identities, composition,
and law proofs are the same data; this changes no mathematical definition.

The scope parameters D, l, hl, Ω, Y and their instances are unchanged. No signature,
public import, public attribute, coefficient model, shift, constructibility
predicate, or distinguished-triangle predicate changes. Only proof-local opacity
settings move. respectTransparency stays enabled.

The target statements retain their meaning because their category data are equal
to the original data. This record supplies the definition-use review required by
AGENTS.md §4; it requests no target statement revision. The accompanying report
lists the actual completed holes and the proved rational-descent extraction.

## Old

```lean
noncomputable instance stageCategory (E : Index l Ω) :
    Category (Stage D l hl Ω Y E) :=
  inferInstanceAs (Category (D.sfRationalCategory l hl (Coefficient.{u} l Ω E) Y))
```

## New

```lean
noncomputable instance stageCategory (E : Index l Ω) :
    Category (Stage D l hl Ω Y E) :=
  ScalarLocalization.category (Padic.coefficientExtensionIntegers l (Coefficient.{u} l Ω E))
    (sfIntegralConstructibleCategory l (Coefficient.{u} l Ω E) Y)
    (Padic.coefficientExtensionUniformizer l (Coefficient.{u} l Ω E))
```

## Users

`tools/downstream.py Sheaf.Paper.SfAlgebraicallyClosedCoefficients --uses stageCategory`
returns these 44 textual hits, including the item. The tool matches the final name
segment, so many hits use the similarly named general-stage cache or a local
variable. All remain semantically unchanged because the cached instance is the
same category. The only direct importers are the two GeneralAlgebraicallyClosed
modules below; their unchanged sources are compiled against the final candidate
and their temporary sandbox copies are removed. No other existing module is
adapted or withdrawn. Holders are the local claim records at preparation time.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.A1QbarOpenClosedCohomology | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.AdicAmbientHomEvaluationComparison | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.AutomorphismConstructibleStageEquivalence | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.CommonAdicSectionData | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.CommonProjectionOpenFactor | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.CommonProjectionOpenPullbackTensor | J7 | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.CommonStageFiniteHomLifting | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.CommonStageFiniteObjectLifting | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.CommonStageInclusionTensorModel | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.CommonStageInclusionTensorNaturality | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.CommonStageOpenHeartAdjunction | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.CommonStagePullbackRepresentativeLinearity | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.CommonStageRestrictionTensorDescent | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.CommonStageTensorLineCoherenceNaturality | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.CommonStageTensorRightUnitorNaturality | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.CompactSupportStageActionAdjunction | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.DerivedPullbackTensorHom | E3 | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.DerivedPullbackTensorIso | J2 | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.FdScalarRoosComparisonIntertwining | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.FrobeniusCoefficientTwistsCanonical | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.FrobeniusFixedPairComparison | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.FrobeniusSquareExchange | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficientStages | unclaimed | Direct importer; unchanged source checked against the candidate. |
| Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients | unclaimed | Direct importer; unchanged source checked against the candidate. |
| Sheaf.Paper.GeneralPairHomCoordinates | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.IsomorphismPullbackRawStage | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.IsomorphismPullbackTExactCoefficients | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.OpenWeilCoefficientFibres | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.OrientationCoefficientTwists | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.PodReconstructionCommonStageCoherence | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.PurFrameworkPbcCoefficientCategoryComparison | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.RationalPullbackStageCoherence | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.RationalSmoothPurityCanonical | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.RationalTensorStageCoherence | N1 | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.RestrictionTensorRepresentativeTransport | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.SemilinearFieldOperationLifts | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.SfAlgebraicallyClosedCoefficients | S2 (this assignment) | Direct cache body and proofs changed as described here. |
| Sheaf.Paper.SfNormalizedCommonStageWeilSquares | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.SixFunctorOrientationDatum | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.SixFunctorOrientationFamily | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.SixFunctorOrientationHigherPair | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.SixFunctorOrientationStageCompatibility | unclaimed | Transitive short-name hit; category data equal, no source change. |
| Sheaf.Paper.SmoothPurityCoordinateCategories | unclaimed | Transitive short-name hit; category data equal, no source change. |

## Status

landed 20261027T131505-L-2946408 2026-10-27 (merge of deliver/S2/Sheaf.Paper.SfAlgebraicallyClosedCoefficients)
