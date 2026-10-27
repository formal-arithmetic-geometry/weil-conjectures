# PointAutomorphismTransportScalarExtension proof context

## Reason

J2 fills the four existing theorem holes with proved private helpers. The added
lexical scope and local irreducibility attributes support the ordinary tensor
calculation and prevent elaboration from expanding large coefficient constructions.
Every original public declaration signature, definition body, visibility, public
import and exported attribute is preserved. No target meaning changes.

## Old

The existing command block remains verbatim:

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures
```

There was no `ChangeOfRings` scope opening or local irreducibility block in this module.

## New

In addition to the original commands, the proof uses:

```lean
set_option Elab.async false
open scoped ChangeOfRings
attribute [local instance 2000] pointScalarModuleDerived
  pointIntegralModuleTensorAdditive pointIntegralModuleTensorLimits
  pointIntegralModuleTensorColimits
attribute [local irreducible] completedScalarChangeData completedOrdinaryScalarExtension
  completedDerivedScalarExtension completedScalarCounit completedScalarTensorSection
  completedIntegralCoefficientSheafUnrestricted integralOperationsGoodComplex

attribute [local irreducible] pointAutomorphismRestrictionDerived transportRestrictionIso
attribute [local irreducible] isomorphismScalarTensorDerived
  Functor.mapDerivedCategoryNatIso
```

Sequential elaboration avoids repeating expensive type checking and linting
work concurrently for these large dependent constructions. This setting affects
only this module's elaboration and does not change kernel checks.

The scope opening follows `universe u`. The instance priorities and initial
irreducibility block occur just inside `namespace WeilConjectures`. The restriction
irreducibility attribute follows `transportRestrictionDerived_isIso`, after the
explicit comparison equality is proved. The derived tensor and natural-isomorphism
attributes follow `transportScalarTensorDerived_eq`. All these attributes remain local to
this file. They do not alter global
reducibility or any construction. Proof dependencies are private imports; two
`import all` directives expose existing proved private tensor and naturality APIs
only during this proof. New helpers are private and completely proved.

## Users

`tools/downstream.py Sheaf.Paper.PointAutomorphismTransportScalarExtension --names`
reports the following consumers. Their public interfaces and mathematical statements
are unchanged, and no consumer source adaptation is necessary. No held module is edited.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.DeligneLaumon.FiniteStageFibreVanishing` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.DeligneLaumon.RawHeartAdicLisseStratification` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.DeligneLaumon.TwoPointCurveConstituentPurity` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.AdicHomTensorLisseCriterion` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.AnchoredPureCurveCriterion` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalFiniteWeilDiagramRealization` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilFrontierRestriction` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilRestrictionData` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalLisseWeilRestrictionMaps` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalLocalFrobeniusData` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalLocalFrobeniusIterateComparison` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalNormalizedTwoFibreComparison` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalNormalizedTwoFibreData` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCoherence` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCommonFibres` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCommonRealization` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCommonRestriction` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCommonRestrictionComparison` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCommonRestrictionData` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseCommonSystem` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseOperations` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalRawLissePointFibres` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseRealizationData` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalRawLisseScalarCoherence` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalSystemRawLisseRealization` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalTwoFibreCommonData` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalTwoFibreScalarData` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ClassicalWeilFiltrationHeartTransport` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.CompletedLocalFibreComparisonData` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.ConstantExtensionReturnLocalOperators` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.CurveRestrictionFiltrationSpectrum` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.GeometricQuotientWeilCompositionSeries` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.IteratedReturnTransportScalarCalculus` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.LisseCohomologyDerivedDual` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.LisseFieldNormalization` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.LisseLatticeHeartLift` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.LissePointNormalization` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.LissePointSectionsRealization` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.LissePullbackNormalization` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.LisseRationalRealization` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.LisseRationalRealizationData` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.LisseShortComplexCommonStageExactness` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.LisseTensorNormalization` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.LisseTensorPullbackRealization` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.LocalFrobeniusLargeCoefficients` | U9 | Same public API and data; no adaptation. |
| `Sheaf.Paper.NormalizedClassicalWeilRealization` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.NormalizedFiniteFibreModels` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.NormalizedFiniteRealizationFibre` | unclaimed | Same public API and data; no adaptation. |
| `Sheaf.Paper.RationalReturnBlockPower` | unclaimed | Same public API and data; no adaptation. |

## Status

landed 20261025T123131-L-1835869 2026-10-25 (merge of deliver/J2/Sheaf.Paper.PointAutomorphismTransportScalarExtension)
