# integral_lfp_local_torsion_charts: proof environment

## Reason

Preflight conservatively classifies changed scope and local-instance commands as
an interface change. The new proofs use zero objects and preservation instances
for composites and binary biproducts. These commands only affect elaboration in
this file; they change no existing declaration's signature, visibility or data.
The original theorem statement and the private helpers imported by consumers are
unchanged. This record documents the flagged commands, not a mathematical repair.

## Old

```lean
open scoped CategoryTheory.Obj

attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] comp_preservesFiniteLimits comp_preservesLimits
```

## New

```lean
open scoped CategoryTheory.Obj ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts
attribute [local instance] comp_preservesFiniteLimits comp_preservesLimits
```

Before the new scalar-chart transport helpers:

```lean
attribute [local instance] comp_preservesFiniteColimits
attribute [local instance] preservesBinaryBiproducts_of_preservesBinaryCoproducts
```

Both additional attributes are local, and opening a scope is local to this file.
The new private helpers have fully proved bodies. No existing definition or
statement changes meaning, and no target statement review is reopened.

## Users

The complete downstream list from `tools/downstream.py` is recorded below.
These commands have no exported effect; no consumer needs adaptation. In
particular, `resolutionRationalLF`, privately imported by the local resolution
module, retains its exact signature and body.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.ContinuousConstructibleIntegralDenominators | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralGluing | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralImage | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralModel | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralSingle | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousConstructibleIntegralStratum | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousExchangeIntegralModel | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralComplexTelescope | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralExchangeSquare | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalization | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationColimitTransport | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationContinuity | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationHomology | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationLegs | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationMate | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralLocalizationModel | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralModuleTelescope | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralPushComparison | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.ContinuousIntegralRegularTelescope | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSequentialHom | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.IntegralConstructibleSheafHom | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.IntegralLfpEventualFreeImage | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.IntegralLfpFiniteQuotientCharts | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.IntegralLfpHomContinuity | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.Paper.IntegralLfpLocallyFreeResolution | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| TargetsCheck | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Unaffected: existing signatures and visibility unchanged; no adaptation. |

## Status

landed 20261016T090411-L-1837755 2026-10-16 (merge of deliver/A4/Sheaf.Paper.IntegralLfpLocalTorsionCharts)
