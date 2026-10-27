# SfPackageLocalizationProjectionRealization public imports

## Reason

The integral image assembly now uses the two private proof-input modules. It does not use
`SfRecollementReductionBoundary`; its source-boundary statement is sufficient for the
exact image and full-inclusion lift. The previously removed supplemental Weil declarations
had also left `ProjectionWeilTensorDomainBridge` imported without a remaining use.
Remove these three unused imports, including the total-limit realization import, and make
the source-recollement import private because only the proof uses it. Every existing
declaration, signature and definition
stays identical. The unit route, target statements and their meanings do not change.

## Old

```lean
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.SfOpenClosedTriangleAllStages
public import Sheaf.Paper.SfRecollementReductionBoundary
public import Sheaf.Paper.CompactSupportTotalLimitRealization
public import Sheaf.Paper.CompactSupportProjectionFormula
public import Sheaf.Paper.ProjectionWeilTensorDomainBridge
import Sheaf.Paper.FiniteTorStability
```

## New

```lean
public import Sheaf.Paper.SixFunctorOperationDatum
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.CompactSupportProjectionFormula
import Sheaf.Paper.FiniteTorStability
import Sheaf.Paper.SfOpenClosedTriangleAllStages
import Sheaf.Paper.SfPackageIntegralRecollementSource
import Sheaf.Paper.SfPackageIntegralSupportTowerNormalization
```

## Users

`python3 tools/downstream.py Sheaf.Paper.SfPackageLocalizationProjectionRealization`
reports zero downstream modules. A direct source-import search agrees. The parent DAG
references and the unit route are preserved; zero importers is not used to withdraw the item.
There are no consumer adaptations.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.SfPackageLocalizationProjectionRealization | F2 | Unused imports removed and proof import privatized; signatures and definitions unchanged. |

## Status

landed 20261026T023114-L-521184 2026-10-26 (merge of deliver/F2/Sheaf.Paper.SfPackageLocalizationProjectionRealization)
