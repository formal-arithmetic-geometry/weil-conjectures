# WeilConjectures.PurCompactSupport.scalarTensorTotal

## Reason

Restore the module from its current quarantine archive, retaining all declarations and
statements. The archived scalar tensor total fails to elaborate against the current
library: instance search chooses an unrelated coefficient-universe parameter in an
`EssentiallySmall` proof, producing `u + 1 =?= max (u + 1) ?u` and kernel application
type mismatches in `SheafOfModules.cochainTensorLocalizationIsMonoidal`.

Exclude the three ambiguous imported smallness instances in this module and pin the
ordinary monoidal structures to the actual site/ring universes. This uses the same
signed total map and the same ordinary tensor-balancing comparison. No coefficient
object, functor, target statement, or mathematical meaning changes. The two monoidal
structure expressions in `scalarTensorTotal_isIso` are pinned identically.

## Old

```lean
def scalarTensorTotal {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P Q : CochainComplex (pbcModules W R) ℤ) :=
  letI := SheafOfModules.monoidalCategory R
  letI := SheafOfModules.monoidalCategory S
  tensorPullbackTotal (pbcExtend a) (scalarOrdinaryTensor a)
    (fun {_ _ _ _} v z ↦ scalarOrdinaryTensor_naturality a v z) P Q

```

## New

```lean
def scalarTensorTotal {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (a : R ⟶ S)
    (P Q : CochainComplex (pbcModules W R) ℤ) :=
  letI := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} R
  letI := SheafOfModules.monoidalCategory.{u, u + 1, u + 1} S
  tensorPullbackTotal (pbcExtend a) (scalarOrdinaryTensor a)
    (fun {_ _ _ _} v z ↦ scalarOrdinaryTensor_naturality a v z) P Q

```

The module-local elaboration environment also excludes
`WeilConjectures.integralOperationsSiteSmall`,
`WeilConjectures.scalarReductionSiteSmall`, and
`WeilConjectures.integralReductionSiteEssentiallySmall` as instances. Their declarations
remain unchanged. There are no new public declarations.

## Users

`tools/downstream.py Sheaf.Paper.IntegralCompactSupportCoefficientComparison --uses
scalarTensorTotal` reports `unknown module(s)` because the item is currently quarantined.
A direct search of both `lean/` and `quarantine/` finds no external use of
`PurCompactSupport.scalarTensorTotal`. Its in-file consumers are
`scalarTensorTotal_isIso`, `scalarTensor_existsUnique`, and the `scalarTensor`
construction through that normalization. They retain their signatures and use the same
map. The quarantined importers are retained and listed for the restoration review:

| module | group holding it | effect |
| --- | --- | --- |
| `quarantine/Sheaf/SecSmoothPurity/AdicScalarTraceCoherence.lean` | quarantined; not adapted | Imports restored interface; no direct scalarTensorTotal use. |
| `quarantine/Sheaf/SecSmoothPurity/RationalPurityTraceCoherence.lean` | quarantined; not adapted | Imports restored interface; no direct scalarTensorTotal use. |
| `quarantine/Sheaf/Paper/SixFunctorOperationDatumStages.lean` | quarantined; not adapted | Imports restored interface; no direct scalarTensorTotal use. |
| `quarantine/Sheaf/Paper/PuritySourceTransports.lean` | quarantined; not adapted | Imports restored interface; no direct scalarTensorTotal use. |
| `quarantine/Sheaf/Paper/RationalSmoothPurityCanonical.lean` | quarantined; not adapted | Imports restored interface; no direct scalarTensorTotal use. |
| `quarantine/Sheaf/Paper/RationalPurityPresentation.lean` | quarantined; not adapted | Imports restored interface; no direct scalarTensorTotal use. |
| `quarantine/Sheaf/Paper/ProjectionFiniteReduction.lean` | quarantined; not adapted | Imports restored interface; no direct scalarTensorTotal use. |
| `quarantine/Sheaf/Paper/QcqsCompactSupportRealization.lean` | quarantined; not adapted | Imports restored interface; no direct scalarTensorTotal use. |
| `quarantine/Sheaf/Paper/CompactSupportCondensedRealization.lean` | quarantined; not adapted | Imports restored interface; no direct scalarTensorTotal use. |
| `quarantine/Sheaf/Paper/BasicOperationsCoefficientReduction.lean` | quarantined; not adapted | Imports restored interface; no direct scalarTensorTotal use. |
| `quarantine/Sheaf/Paper/DegreeZeroCompactSupportSections.lean` | quarantined; not adapted | Imports restored interface; no direct scalarTensorTotal use. |
| `quarantine/Sheaf/SixFunctors/IntegralCompactificationSystemRealization.lean` | quarantined; not adapted | Imports restored interface; no direct scalarTensorTotal use. |
| `quarantine/Sheaf/SixFunctors/CoefIntegralFiniteExtension.lean` | quarantined; not adapted | Imports restored interface; no direct scalarTensorTotal use. |
| `quarantine/Sheaf/SixFunctors/OpenFactorCoherence.lean` | quarantined; not adapted | Imports restored interface; no direct scalarTensorTotal use. |

No consumer adaptation is required; no target text or intended meaning changes.
The independent reader should confirm that the explicit universe instantiation is the
original intended monoidal structure before closing this record.

## Status

landed 20261021T171734-L-3120649 2026-10-21 (merge of deliver/A9/Sheaf.Paper.IntegralCompactSupportCoefficientComparison)
