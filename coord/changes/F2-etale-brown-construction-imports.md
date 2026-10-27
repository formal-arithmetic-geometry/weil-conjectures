# Strict étale construction proof interfaces

## Reason

The two existing intermediate statements use only `StrictEtaleSystemInterfaces`.
Importing the unfinished adjoint theorem adds unrelated proof dependencies when these
statements are used to construct the Brown adjunction. Narrow their public imports to
the definition owner. No declaration, binder, visibility, attribute or body is changed.
These modules were unclaimed when checked. This is an interface import cleanup, not a
repair of the mathematics or a deletion of an upstream declaration.

## Old

In each of the following modules:

- `Sheaf.Paper.EtaleCompactSupportConstruction`
- `Sheaf.Paper.EtaleCompactSupportScalarAction`

```lean
public import Sheaf.Paper.EtaleCoefficientSystemAdjoint
```

## New

```lean
public import Sheaf.Paper.StrictEtaleSystemInterfaces
```

## Users

`tools/downstream.py --uses` identifies the two declarations themselves and
`EtaleTowerBrownAdjunction` as their declaration users. The latter explicitly imports
`EtaleCoefficientSystemAdjoint` and both modules, so it retains its complete public
interface. The remaining transitive importers therefore retain theirs as well. The new
Brown proof imports the two statements privately.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.EtaleCompactSupportConstruction | unclaimed | Import narrowed; signature and proof unchanged. |
| Sheaf.Paper.EtaleCompactSupportScalarAction | unclaimed | Import narrowed; signature and proof unchanged. |
| Sheaf.Paper.BrownTowerBoundedTransport | not adapted | No declaration change; adjoint import remains through EtaleTowerBrownAdjunction. |
| Sheaf.Paper.BrownTowerFiniteEvaluation | not adapted | No declaration change; adjoint import remains through EtaleTowerBrownAdjunction. |
| Sheaf.Paper.BrownTowerFiniteSiteComparison | not adapted | No declaration change; adjoint import remains through EtaleTowerBrownAdjunction. |
| Sheaf.Paper.BrownTowerRealization | not adapted | No declaration change; adjoint import remains through EtaleTowerBrownAdjunction. |
| Sheaf.Paper.BrownTowerSite | not adapted | No declaration change; adjoint import remains through EtaleTowerBrownAdjunction. |
| Sheaf.Paper.CondensedExceptionalReconstruction | not adapted | No declaration change; adjoint import remains through EtaleTowerBrownAdjunction. |
| Sheaf.Paper.EtaleTowerBrownAdjunction | not adapted | No declaration change; adjoint import remains through EtaleTowerBrownAdjunction. |
| Sheaf.Paper.ExceptionalRealizationNormalization | not adapted | No declaration change; adjoint import remains through EtaleTowerBrownAdjunction. |
| Sheaf.Paper.ExceptionalReconstructionComparison | not adapted | No declaration change; adjoint import remains through EtaleTowerBrownAdjunction. |
| Sheaf.Paper.ExceptionalReconstructionContext | not adapted | No declaration change; adjoint import remains through EtaleTowerBrownAdjunction. |
| Sheaf.Paper.ExceptionalReconstructionPresentations | not adapted | No declaration change; adjoint import remains through EtaleTowerBrownAdjunction. |
| Sheaf.Paper.PurIntegralRepresentingPair | not adapted | No declaration change; adjoint import remains through EtaleTowerBrownAdjunction. |
| Sheaf.Paper.PurIntegralSupportComparison | not adapted | No declaration change; adjoint import remains through EtaleTowerBrownAdjunction. |
| Sheaf.Paper.ReconstructedPairRefinementCoherence | not adapted | No declaration change; adjoint import remains through EtaleTowerBrownAdjunction. |
| Sheaf.Paper.EtaleSystemBrownConstruction | F2 | New proof-only user of the two statements. |

## Status

landed 20261025T030510-L-2852930 2026-10-25 (merge of deliver/F2/Sheaf.Paper.EtaleSystemBrownConstruction)
