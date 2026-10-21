# OpenImmersionTensorPiece proof namespace

## Reason

The new private tensor-complex proof helpers use tensor notation and the standard
`MonoidalCategory` lemmas. The preflight conservatively classifies a new top-level `open`
command as changing what importers see and requests this record. The command changes local
name resolution for the proofs. All existing declaration signatures, definition bodies and
public imports stay verbatim.

## Old

```lean
open CategoryTheory CategoryTheory.Limits
```

## New

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
```

## Users

The downstream source import graph has the following consumers (current claim holders).
There are no definition or statement changes and no forced adaptations.

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.Paper.CompletedBaseChangeMap` | unclaimed | No signature or definition change; no adaptation. |
| `Sheaf.Paper.CompletedDirectImageLimits` | P5 | No signature or definition change; no adaptation. |
| `Sheaf.Paper.CompletedProjectionCoherence` | D2 | No signature or definition change; no adaptation. |
| `Sheaf.Paper.CompletedPullbackUnitTower` | V1 | No signature or definition change; no adaptation. |
| `Sheaf.Paper.CompletedTowerCompatibility` | unclaimed | No signature or definition change; no adaptation. |
| `Sheaf.Paper.CompletedTowerCorners` | unclaimed | No signature or definition change; no adaptation. |
| `Sheaf.Paper.OpenImmersionTensorPiece` | C6 | Proof and local name resolution only. |
| `Sheaf.Paper.PerfectProjectionFormula` | T7 | No signature or definition change; no adaptation. |
| `Sheaf.Paper.ProEtaleConstantReductionTower` | T4 | No signature or definition change; no adaptation. |
| `Sheaf.Paper.ProjectionFormulaCompactified` | unclaimed | No signature or definition change; no adaptation. |
| `Sheaf.Paper.ProjectionFormulaIdentityCompactification` | unclaimed | No signature or definition change; no adaptation. |
| `Sheaf.Paper.QuotientCornerFrobeniusStructures` | unclaimed | No signature or definition change; no adaptation. |
| `Sheaf.Paper.SfIntegralDirectImageConstructible` | unclaimed | No signature or definition change; no adaptation. |
| `Sheaf.Paper.StrictTowerExchangeMateNormalization` | N2 | No signature or definition change; no adaptation. |
| `Sheaf.SecSmoothPurity.OpenBaseChangeDerivedUnit` | unclaimed | No signature or definition change; no adaptation. |
| `Sheaf.SecSmoothPurity.OpenScalarExchange` | unclaimed | No signature or definition change; no adaptation. |

## Status

landed 20261021T004821-L-1790755 2026-10-21 (merge of deliver/C6/Sheaf.Paper.OpenImmersionTensorPiece)
