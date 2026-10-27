# finiteReduction_tensorPurity proof transparency

## Reason

The inverse-orientation square unifies several large derived scalar functors. Local
irreducibility prevents unification from expanding their adjunction and localization
constructions. These attributes apply only inside the item module. No definition body,
existing signature, public import or downstream elaboration attribute changes.

## Old

No local irreducibility attributes in `Sheaf.Paper.FiniteReductionTensorPurity`.

## New

```lean
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension Etale.derivedTensor Etale.upperStar Etale.lowerStar
  Scheme.sfIntrinsicDerivedEquivalence ProEtale.upperStar

namespace WeilConjectures.PurityFiniteSetting
attribute [local irreducible] finiteTensorCore
  finiteTensorPullbackComparison finiteReductionTensorInputComparison diagonalDualizingObject
  smoothPurityPullback diagonalDualizing
attribute [local implicit_reducible] finiteTensorReduction
```

The new modules `Sheaf.Paper.FiniteReductionTensorFactors`,
`Sheaf.Paper.FiniteReductionThetaFactor`, and
`Sheaf.Paper.FiniteReductionPositiveLineComparison` add explicit factor definitions and
two named comparison obligations. They are private proof imports of the item; the
item's published interface is unchanged. Each has a new DAG node.

## Users

`tools/downstream.py Sheaf.Paper.FiniteReductionTensorPurity --uses
finiteReduction_tensorPurity` finds only `Sheaf.Paper.FiniteReductionOfPurity` outside
the item. Its application is unchanged. The full downstream module list is included
below. No consumer edits are necessary: all added attributes are local, the theorem
signature is identical, and the added definitions are behind private imports. Current
consumer holders need no adaptation; none of their files is changed.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FiniteReductionTensorPurity | A2 | Private proof implementation only. |
| Sheaf.Paper.AdicExceptionalNormalizationMate | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.AdicNormalizedPurityLift | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.AdicPurityCanonicalSourceCoherence | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.AdicPurityNormalizedComparisonConstruction | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.AdicPurityScalarNaturality | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.AdicPurityScalarNaturalityData | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.AdicUnitTraceConstruction | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.AdicUnitTraceCounitReductions | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.AdicUnitTraceProjectionAssembly | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.AdicUnitTraceReductionData | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.AdicUnitTraceScalarData | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.AdicUnitTraceTargetNormalization | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.FiniteReductionOfPurity | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.NormalizedIntegralPurityTrace | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.PurAdicReconstruction | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.RationalExceptionalFinalEquations | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.RationalPurityCoherenceDescent | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.RationalPurityComparisonDescent | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.RationalPurityScalarLocalization | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.RationalPuritySourceLocalization | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.RationalScalarComparisonData | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.RationalScalarComparisonIdentification | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.TwistedPullbackAdicAgreement | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.TwistedPullbackCanonicalShifts | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.TwistedPullbackPbcCoordinates | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.TwistedPullbackPbcPullback | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.TwistedPullbackPbcTwist | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.TwistedPullbackScalarFamilies | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.TwistedPullbackScalarShifts | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.TwistedPullbackShiftCoherence | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.TwistedPullbackSquareCoordinates | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.TwistedPullbackSquareMaps | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.TwistedPullbackSquareScalars | unchanged; no adaptation | Same theorem signature and public interface. |
| Sheaf.Paper.TwistedPullbackSquareShiftEquations | unchanged; no adaptation | Same theorem signature and public interface. |

## Status

landed 20261025T201222-L-2337616 2026-10-25 (merge of deliver/A2/Sheaf.Paper.FiniteReductionTensorPurity)
